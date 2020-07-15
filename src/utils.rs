//! A collection of utilities used throughout the compiler

use std::ops::Deref;

/// A generic guard type that allows for chained dereferencing, through a mapping function
///
/// This type should be constructed with the values themselves. The implementation of `Deref` will
/// dereference `provider` and apply `map` to the resulting pointer. This can be used to give
/// guarded access to values that might not be directly inside a lock.
///
/// ## Example
///
/// Here's the skeleton of how this type is used in the `db` module - with an rwlock and
/// dereferencing read guards:
///
/// ```
/// use std::ops::Deref;
/// use std::sync::{RwLock, RwLockReadGuard as ReadGuard};
/// # use super::Guard
///
/// // The type containing the locks - in the case of `db`, this represents `Filestate`.
/// struct Foo {
///     bar: RwLock<Option<Bar>>,
/// }
///
/// // The internal, locked type. This is typically a `Result` of some kind that is expensive to
/// // compute.
/// struct Bar {
///     // The inner value we want to provide a guarded reference to
///     //
///     // In practice, this will be one of (possibly) multiple fields, where we might just want to
///     // provide access to one.
///     inner: i32,
/// }
///
/// // This function showcases example usage. It's typically better to return an `impl Deref`,
/// // instead of writing out the `Guard` type explicitly
/// fn get_bar(foo: &Foo) -> impl Deref<Target=i32> {
///     // Do an initial check so that we don't unnecessarily acquire write locks - that would
///     // defeat the point of using an rwlock!
///     if foo.bar.read().unwrap().is_none() {
///         // If `bar` hasn't already been computed, we'll do that now!
///         let mut write_guard = foo.bar.write().unwrap();
///         if write_guard.is_none() {
///             *write_guard = compute_bar();
///         }
///     }
///
///     // From this point forward, we know tht `bar` has been computed, so we're safe to unwrap it
///     // in our mapping function
///
///     // We define the helping mapper function. This is typically defined locally (as it's
///     // usually simple) but may be defined elsewhere if it is more complex.
///     fn map(b: &Option<Bar>) -> &i32 {
///         &b.as_ref().unwrap().inner
///     }
///
///     Guard {
///         provider: foo.bar.read().unwrap(),
///         map,
///     }
/// }
///
/// // This is mostly a placeholder function - in practice this is more expensive, and produces a
/// // result worth caching.
/// fn compute_bar() -> i32 {
///     Bar { inner: 0 }
/// }
/// ```
pub struct Guard<T, P: Deref, F: Fn(&P::Target) -> &T> {
    /// The initial guard, typically for accessing some outer value
    pub provider: P,

    /// The mapping function, which essentially inserts the method for the implementation of
    /// `Deref` for `P::Target`, with a target as `T`. For more information, refer to the
    /// implementation of `Deref` or to the example given above.
    pub map: F,
}

impl<T, P: Deref, F: Fn(&P::Target) -> &T> Deref for Guard<T, P, F> {
    type Target = T;

    fn deref(&self) -> &T {
        (self.map)(&self.provider)
    }
}

pub trait Guarded {
    type Output;

    fn get(&self) -> Self::Output;
}

pub struct Mapped<T, P, F: Fn(&P) -> T> {
    pub provider: P,
    pub map: F,
}

impl<T, P, F: Fn(&P) -> T> Guarded for Mapped<T, P, F> {
    type Output = T;

    fn get(&self) -> T {
        (self.map)(&self.provider)
    }
}
