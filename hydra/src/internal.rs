//! Publicly exposed pieces of the API that are *not* for public use
//!
//! The items in this module are all publicly exposed because we need to be able to access them
//! from the macro expansions, though we don't *actually* want users to touch this. So this module
//! is marked with `#[doc(hidden)]` in order to reflect that.
//!
//! Just because it's *hidden* doesn't mean we don't actually document it - have fun reading here!
//! :)

#![doc(hidden)]

use crate::JobId;
use futures::future::Future;
use futures::lock::Mutex;
use std::collections::HashMap;
use std::pin::Pin;

pub use crate::runtime::Executor;

/// A singleton, unique type that only exists to act as an object for cross-macro storage
///
/// Through traits and associated items, we can create the effect of communication and storage
/// across macros. The typical problem we'll solve is something like: "How does a proc-macro in
/// module 'foo' know about the input to the macro in module 'bar'?"
///
/// We're able to solve this by requring that the macro in 'foo' be able to reproduce some trait
/// defined in 'bar'. Let's walk through an example.
///
/// ## Example
///
/// Say we're in the middle of some proc-macro (like `hydra_macros::__make_database`, for example),
/// and we want to be able to use a set of types and constants defined by a separate, attribute
/// macro.
///
/// - this is useful because it allows us to avoid using `Box<dyn Any>` inside of the
/// database.
///
/// ```ignore
/// #[proc_macro]
/// fn __make_database(input: TokenStream) -> TokenStream {
///     // -- snip --
///     
///     // We're going to suppose that all we're given about the other invocation is the name of
///     // some trait we generated.
///     let trait_name = /* generated; maybe __DummyFoo from trait Foo */
///
///     // Typically, there's many uses of `Dummy`, so we abbreviate:
///     let dummy = quote!(hydra::internal::Dummy as #trait_name);
///     
///     // With `Dummy` here, we're able to extract types, constants, and functions defined by the
///     // other proc-macro. Here's a type:
///     let bar_type = quote!(<#dummy>::Bar);
///
///     // And here's a constant:
///     let baz_const = quote!(<#dummy>::Baz);
///     // Oh wait! They look exactly the same! We just have to be careful not to confuse our types
///     // with our constants.
///
///     // Now we can do fun things with this, like emit code *here* based on the input somewhere
///     // else:
///     quote!(
///         struct MyStruct {
///             bar: #bar_type,
///         }
///
///         impl MyStruct {
///             fn baz() -> u32 {
///                 #baz_const
///             }
///         }
///     )
/// }
/// ```
pub struct Dummy;

/// A wrapper around a `u16` to provide storage and dispatch to different database layers
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct QueryKind(pub u16);

pub trait Computable<DB> {
    type Key;
    type Value: Sized;
    const QUERY_KIND: QueryKind;

    fn construct<'a>(
        db: DB,
        job: &'a JobId,
        key: Self::Key,
    ) -> Pin<Box<dyn 'a + Send + Sync + Future<Output = crate::Result<Self::Value>>>>;
}

#[doc(hidden)]
pub trait Runtime: 'static + Clone + Send + Sync {
    /// Mark the given job as blocked by a query
    ///
    /// This function should return `None` if the id given by `job` has already finished.
    fn mark_single_blocked<'a>(
        &'a self,
        job: &'a JobId,
        by: &'a JobId,
    ) -> Pin<Box<dyn 'a + Send + Sync + Future<Output = Option<()>>>>;

    /// Returns the executor for handling tasks
    fn executor(&self) -> &Executor;

    /// A helper method to mark all ancestor jobs of the given one as being blocked by the the
    /// given job.
    ///
    /// Contrary to the name "recursive", this method is only really structurally recursive - much
    /// in the same way that linked lists are typically a "recursive" datatype though they an be
    /// traversed without recursive function calls.
    ///
    /// If the job has already finished, this function will simply return without doing anything.
    ///
    /// This method should not be implemented manually (by users or the procedural macros).
    fn mark_blocked_recursive(
        self,
        job: JobId,
        by: JobId,
    ) -> Pin<Box<dyn Send + Sync + Future<Output = ()>>> {
        async fn inner(this: impl Runtime, job: JobId, by: JobId) {
            let mut job = &job;

            // From the documentation of `mark_single_blocked`:
            // > This function should return `None` if the id given by `job` has already finished
            if this.mark_single_blocked(job, &by).await.is_none() {
                return ();
            }

            while let Some(p) = job.parent() {
                job = &p;
                if this.mark_single_blocked(job, &by).await.is_none() {
                    return ();
                }
            }
        }

        Box::pin(inner(self, job, by))
    }
}

pub enum Priority {
    Defer,
    Asap,
}

pub struct JobOwners {
    map: Mutex<HashMap<JobId, QueryKind>>,
}

impl JobOwners {
    pub fn new() -> JobOwners {
        Self {
            map: Mutex::new(HashMap::new()),
        }
    }

    pub async fn query_kind(&self, job: &JobId) -> Option<QueryKind> {
        self.map.lock().await.get(job).cloned()
    }
}
