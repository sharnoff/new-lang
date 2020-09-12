//! The primary implementation of the systems used for managing the runtime operations of the
//! database

use crate::internal::{Computable, Runtime};
use crate::JobId;
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;

pub struct DBLayer<K, V, DB, Token> {
    values: HashMap<K, ValueInfo<V>>,

    /// A separate store so that we can check which `JobId`s
    /// A reference of the values for which keys we have `JobId`s
    refs: HashMap<JobId, K>,

    compute: PhantomData<(DB, Token)>,
}

struct JobContext<DB> {
    id: JobId,
    global_db: DB,
}

struct ValueInfo<T> {
    compute_status: ComputeStatus<T>,
}

enum ComputeStatus<T> {
    InProgress {
        // The `JobId` that is currently tasked with computing this value
        job: JobId,
        // The set of jobs that the compute task is currently blocked on;
        blocked_on: Vec<JobId>,
    },
    Done(T),
}

impl<K, V, DB, Token> DBLayer<K, V, DB, Token>
where
    K: Hash,
    Token: Computable<DB, Value = V>,
    DB: Runtime,
{
    pub fn get(&self, global: &DB, job: JobId, key: K) -> crate::Result<V> {
        todo!()
    }

    pub fn mark_blocked(&self, job: JobId, by: JobId) -> Option<()> {
        todo!()
    }
}
