//! The primary implementation of the systems used for managing the runtime operations of the
//! database

use crate::internal::{Computable, Priority, Runtime};
use crate::{Error, JobId};
use futures::channel::oneshot::{self, Sender};
use futures::executor::ThreadPool;
use futures::lock::Mutex;
use futures::prelude::*;
use std::collections::{hash_map::Entry, HashMap};
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::sync::Arc;

pub struct DBLayer<K, V, DB, Token> {
    values: Mutex<HashMap<K, ComputeStatus<V>>>,

    /// A reference of the values for which keys we have `JobId`s currently active
    // NOTE: Always lock *before* `values`
    refs: Mutex<HashMap<JobId, K>>,

    compute: PhantomData<(DB, Token)>,
}

enum ComputeStatus<T> {
    InProgress(OngoingJob<T>),
    Done(Arc<crate::Result<T>>),
}

struct OngoingJob<T> {
    // The `JobId` that is currently tasked with computing this value
    job: JobId,

    // The set of jobs that are currently waiting for this job to finish
    // This list includes everything but the original query's job id
    waiting: Vec<(JobId, Sender<Arc<crate::Result<T>>>)>,

    // The recursive set of jobs that the compute task is currently blocked on
    // TODO: This should probably be a structure that makes it easier to answer "is this other job
    // a descendant of something in the set"
    blocked_on: Vec<JobId>,
}

pub struct Executor(ThreadPool);

impl<K, V, DB, Token> DBLayer<K, V, DB, Token>
where
    K: 'static + Hash + Eq + Clone + Send + Sync,
    V: 'static + Debug + Send + Sync,
    DB: Runtime + AsRef<Self>,
    Token: Computable<DB, Value = V, Key = K> + Send + Sync,
{
    /// Constructs a new, blank `DBLayer`
    pub fn new() -> Self {
        Self {
            values: Mutex::new(HashMap::new()),
            refs: Mutex::new(HashMap::new()),
            compute: PhantomData,
        }
    }

    /// Gets the value corresponding to a key, doing no work if it has already been computed
    pub async fn query(&self, global: &DB, job: JobId, key: K) -> Arc<crate::Result<V>> {
        // We need to open `self.refs` first, because we might need to add to it later.
        let mut key_guard = self.refs.lock().await;

        // The first *actual* thing we do is checking inside `self.values` to see if the value for
        // this key has alredy been computed:
        let mut values_guard = self.values.lock().await;
        match values_guard.entry(key.clone()) {
            // If there's nothing here, then we need to compute the value!
            Entry::Vacant(entry) => {
                let (tx, rx) = oneshot::channel();
                Self::add_task(global, job.clone(), key.clone(), tx);

                // After we've started the task -- but BEFORE WE LET GO OF THE LOCK -- we mark this
                // key as bein currently computed.
                key_guard.insert(job.clone(), key);
                entry.insert(ComputeStatus::InProgress(OngoingJob {
                    job,
                    waiting: Vec::new(),
                    blocked_on: Vec::new(),
                }));

                rx.await.unwrap()
            }

            // Otherwise, if it's already computed (or already has been), we'll return that
            Entry::Occupied(mut entry) => match entry.get_mut() {
                ComputeStatus::Done(arc_value) => arc_value.clone(),
                ComputeStatus::InProgress(status) => {
                    // If the current job id is a descendant of the one that's supposed to be
                    // computing this, we'll return a cycle error. We ALSO have an error if the
                    // computation of this value is blocked by an ancestor of this job id!
                    let is_direct_cycle = job.descendant_of(&status.job);
                    let maybe_indirect = Self::contains_ancestor(&job, &status.blocked_on);

                    if maybe_indirect.is_some() || is_direct_cycle {
                        let mut cycles = Vec::new();
                        if let Some(job) = maybe_indirect {
                            cycles.push(job);
                        }

                        if is_direct_cycle {
                            // Ideally we wouldn't need to clone here, but the workaround would
                            // likely be far more expensive than an `Arc` clone.
                            cycles.push(status.job.clone());
                        }

                        let res = Arc::new(Err(Error::Cycles(cycles)));
                        *entry.into_mut() = ComputeStatus::Done(res.clone());
                        // entry.replace_entry(ComputeStatus::Done(res.clone()));
                        return res;
                    }

                    // If we didn't immediately spot a cycle, then we're free to wait for this to
                    // finish. There's a few things that we need to do in order to register our
                    // future.
                    let (tx, rx) = oneshot::channel();
                    Self::delay_mark_ancestors_blocked(global.clone(), &job, status.job.clone());
                    status.waiting.push((job, tx));

                    rx.await.unwrap()
                }
            },
        }
    }

    /// Constructs a task for computing the value of the function
    fn add_task(db: &DB, job: JobId, key: K, tx: Sender<Arc<crate::Result<V>>>) {
        let global = db.clone();
        let task = async move {
            let result = Token::construct(global.clone(), &job, key.clone()).await;
            let result = Arc::new(result);

            // After we're done constructing the value, we need to set the values inside the db
            // layer:
            let this = global.as_ref();

            // we always lock `refs` before values
            let mut refs_guard = this.refs.lock().await;
            let mut vals_guard = this.values.lock().await;

            // remove the job from the list of currently-running jobs
            refs_guard
                .remove(&job)
                .expect("tried to remove unrecognized job from db layer reference");

            // and then its status with "done"
            let entry = vals_guard
                .get_mut(&key)
                .expect("failed to get db layer value status");
            let waiting = match entry {
                ComputeStatus::Done(_) => panic!("unexpected finished value in task completion"),
                ComputeStatus::InProgress(info) => std::mem::replace(&mut info.waiting, Vec::new()),
            };

            *entry = ComputeStatus::Done(result.clone());
            drop((vals_guard, refs_guard));

            // we can unwrap `try_send` here because the channels each have capacity 1, so (under
            // valid conditions) this should never block. And if we do get a panic, it'll be
            // helpful to know about a bug earlier on in the process
            waiting
                .into_iter()
                .for_each(|(_, s)| s.send(result.clone()).unwrap());

            tx.send(result).unwrap();
        };

        db.executor().add_task(task, Priority::Asap)
    }

    /// Queues a low-priority task into the global executor that marks all of the job's ancestors
    /// as blocked by a job
    ///
    /// If this job has no ancestors, this function does nothing.
    fn delay_mark_ancestors_blocked(global: DB, job: &JobId, blocked_by: JobId) {
        let parent = match job.parent() {
            None => return,
            Some(p) => p.clone(),
        };

        global.executor().add_task(
            global.clone().mark_blocked_recursive(parent, blocked_by),
            Priority::Defer,
        );
    }

    /// Determines whether any of the `JobId`s in the list are an ancestor of the first, returning
    /// the first one found if that is the case
    fn contains_ancestor(this: &JobId, jobs: &[JobId]) -> Option<JobId> {
        jobs.iter()
            .find(|job| this.descendant_of(job))
            .map(JobId::clone)
    }

    /// Marks the given job as blocked by another
    ///
    /// This function returns `None` if the original job is no longer in progress
    pub async fn mark_blocked(&self, job: &JobId, blocked_by: &JobId) -> Option<()> {
        let key_guard = self.refs.lock().await;
        let key = key_guard.get(job)?;

        let mut values_guard = self.values.lock().await;
        let status = values_guard
            .get_mut(key)
            .expect("could not find key in DBLayer value map");

        let info = match status {
            // Because the map of currently running jobs to keys had an entry, the job shouldn't
            // already be done!
            ComputeStatus::Done(_) => panic!("job led to key that had already finished!"),
            ComputeStatus::InProgress(info) => info,
        };

        // If there's any currently waiting jobs that are a *descendant* of the one that's blocked,
        // we have a cycle.
        //
        // This is a bit weird, so let's go through this. Suppose we have the following graph of
        // computation attempts:
        //
        // +-------+  A   +---+
        // | ENTRY | ---> | A | <------+ B'
        // +-------+      +---+        |
        //                  |        +---+      +-------+
        //               A' +------> | B | <--- | ENTRY |
        //                           +---+   B  +-------+
        //
        // Each *arrow* here is a single job. The labels for arrows (for the jobs that we care
        // about) give them a name. Labeled nodes give the name of the job that is tasked with
        // computing them -- i.e the value of `info.job`, in this current scope.
        //
        // Here's what happened in this graph, ordered by the actual time it took place.
        //  1. Entry for job A; marks node A as in progress and continues.
        //  2. Entry for job B;
        //  3. Computing A requires B; job A' is started
        //    a. A' recognizes that B is already working, so it adds itself (the job A') to B's list
        //       of jobs waiting for it. It then starts a low-priority task to mark A as being
        //       blocked by B. Note: in most cases, the task will start after B has already
        //       finished, and so will do nothing.
        //  4. Computing B requires A; job B' is started
        //    a. Same deal as with A' -- A gets marked with job B' waiting, and a low-priority task
        //       to mark B as blocked by A is queued.
        //
        // -- All high-priority tasks finish or are blocked --
        //
        //  5. Task from 3.a starts, marking A as blocked by B. We have enough information at this
        //     point to know that there's a cycle -- because B' is in the list of jobs waiting on
        //     A, and B' has B as an ancestor. Therefore, B' will never finish because we have:
        //         "A" required by "B'" required by "B" required by "A"
        //
        // This final check is what we need to do here - this method is always called as a
        // low-priority task (though calling it as high-priority would not affect correctness).
        //
        // In the example above, we would have been given `job = A` and `blocked_by = B`, hence the
        // need to check descendants of B to find B'.

        // In the event that we *do* find blocked jobs, we send them signals to report the cycle
        // error. When we do this, we take them off the blocked jobs list.
        //
        // We're able to *only* send the signals to the jobs that are in a cycle because those are
        // the only ones that won't get unblocked by themselves -- essentially, we're inserting
        // errors at the minimum set of queries that will ensure everything *does* get calculated.
        let mut did_err = false;
        let waiting = std::mem::replace(&mut info.waiting, Vec::new());

        info.waiting = (waiting.into_iter())
            .filter_map(|(job, tx)| {
                if job.descendant_of(blocked_by) {
                    did_err = true;
                    // sending won't block because the channel has capacity of 1
                    tx.send(Arc::new(Err(Error::Cycles(vec![blocked_by.clone()]))))
                        .unwrap();
                    None
                } else {
                    Some((job, tx))
                }
            })
            .collect();

        Some(())
    }
}

impl Executor {
    pub fn new() -> Executor {
        Executor(ThreadPool::new().expect("failed to build executor thread pool"))
    }

    fn add_task(&self, f: impl 'static + Send + Future<Output = ()>, _priority: Priority) {
        self.0.spawn_ok(f);
    }
}
