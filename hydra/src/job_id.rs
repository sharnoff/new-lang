//! A wrapper module for providing the

use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A unique identifier given to individual query jobs, containing a call-stack of queries that
/// spawned this job
///
/// This type can *never* be created by client code; it is given to jobs as an argument,
#[derive(Debug)]
pub struct JobId(Arc<InternalJobId>);

/// The internal representation of a [`JobId`]
///
/// The depth of an internal [`JobId`] is always exactly equal to the number of successive accesses
/// of `parent` that can be done before encountering `None`.
///
/// [`JobId`]: struct.JobId.html
#[derive(Debug)]
struct InternalJobId {
    parent: Option<JobId>,
    depth: usize,
}

impl JobId {
    /// Produces a new `JobId` as a child query of the current one
    pub fn new_child(&self) -> JobId {
        JobId(Arc::new(InternalJobId {
            parent: Some(self.clone()),
            depth: self.0.depth + 1,
        }))
    }

    /// An internal function to produce a `JobId` as a standalone query
    pub(crate) fn initial_seed() -> JobId {
        JobId(Arc::new(InternalJobId {
            parent: None,
            depth: 0,
        }))
    }

    /// A method to provide the functionality of `std::clone::Clone` for internal use, while still
    /// preventing users from creating new `JobId`s, outside of [`JobId::new_child`].
    ///
    /// [`JobId::new_child`]: #method.new_child.html
    fn clone(&self) -> JobId {
        JobId(Arc::clone(&self.0))
    }

    /// An internally method to determine whether the given job id is a descendant of another
    ///
    /// This is primarily used to find dependency loops.
    fn descendant_of(&self, ancestor: &JobId) -> bool {
        if self.0.depth < ancestor.0.depth {
            return false;
        }

        // We know that `self` is a descendant of `ancestor` if the job id from the equivalent
        // depth on `self` is exactly equal to `ancestor`.
        //
        // We can compare the two with `Arc::ptr_eq` to determine whether they point to the same
        // allocation.
        //
        // EFFICIENCY:
        //   This function could be made significantly more by removing the cloning on each
        //   successive parent. That would either require unsafe code (which isn't great) or
        //   recursion (which could overflow). So in the meantime we have this, until a profiler
        //   reveals we'd benefit with a different solution.

        let mut p = self.clone();

        while p.0.depth > ancestor.0.depth {
            p = p.0.parent.as_ref().unwrap().clone();
        }

        debug_assert!(p.0.depth == ancestor.0.depth);

        &p == ancestor
    }
}

impl Hash for JobId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr_value = Arc::as_ptr(&self.0) as usize;
        ptr_value.hash(state);
    }
}

impl PartialEq<JobId> for JobId {
    fn eq(&self, other: &JobId) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for JobId {}

// Some simple tests to check that the basic tools provided here work
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn job_id_all() {
        // The best way to explain what we're doing here is with a tree of the constructed jobs.
        // Then it becomes clear why each of the assertions make sense.
        //                                       +------+
        //                                       | base |
        //                                       +-+--+-+
        //                  +-----+                |  |                +-----+
        //                  | lhs |----------------+  +----------------| rhs |
        //                  +-+-+-+                                    +-----+
        //     +------+       | |       +------+                          |
        //     | lhs1 |-------+ +-------| lhs2 |                       +------+
        //     +------+                 +------+                       | rhs2 |
        //                                                             +------+

        let base = JobId::initial_seed();
        let lhs = base.new_child();
        let rhs = base.new_child();

        let lhs1 = lhs.new_child();
        let lhs2 = lhs.new_child();

        let rhs2 = rhs.new_child();

        assert!(lhs.descendant_of(&base));
        assert!(!base.descendant_of(&rhs));

        assert!(lhs1.descendant_of(&lhs));
        assert!(lhs2.descendant_of(&base));
        assert!(!base.descendant_of(&lhs2));
        assert!(!base.descendant_of(&lhs1));

        assert!(rhs2.descendant_of(&rhs));

        assert!(!rhs2.descendant_of(&lhs));

        // dbg!(&lhs1, &rhs2);
        assert!(!lhs1.descendant_of(&rhs2));
    }
}
