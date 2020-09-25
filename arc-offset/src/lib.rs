//! Production of `Arc`-like smart pointers for offsets within a struct
//!
//! This crate exists give reference-counted views into components of a type - typically `enum`s,
//! though there's nothing stopping you from using a struct.
//!
//! There are two main components here: the [`ArcOffset`] type and the derive macros under the same
//! name that can be used to generate 
//!
//! ## Examples
//! 
//! The primary use case looks like this:
//!
//! ```
//! use arc_offset::{ArcOffset, Offset};
//! use std::sync::Arc;
//!
//! #[derive(Debug, Clone, ArcOffset)]
//! enum Test {
//!     Foo(u8),
//!     Bar(i32),
//! }
//!
//! let t = Arc::new(Test::Bar(3));
//! let inner: TestArcOffset = t.arc_offset();
//! let cloned: ArcOffset<_,i32> = match &inner {
//!     TestArcOffset::Bar(x) => {
//!         assert_eq!(&x as &i32, &3);
//!         ArcOffset::clone(&x)
//!     }
//!     _ => unreachable!(),
//! };
//! 
//! drop(inner);
//! assert_eq!(*cloned, 3);
//! ```
//!
//! ## Known issues
//!
//! There are a couple known issues (like how the origin type is encoded in the produced
//! [`ArcOffset`]), but those don't have easy solutions. To elaborate, we'd like to turn any
//! `Arc<Option<T>>` into an `ArcOffset<T>` - without the additional `Src` generic type. This
//! would - in turn - allow treating `ArcOffset`s derived from different source types as the same
//! type. This would unfortunately require something akin to a custom `Arc` type to implement.
//!
//! A second area of possible improvement is the bound on `Sized` for `ArcOffset::new`. This could
//! be fixed by some trait to give the size of a type at runtime. This isn't an immediate concern,
//! but may be introduced at some point.
//!
//! [`ArcOffset`]: struct.ArcOffset.html

// re-export the macro(s) under a unified name
pub use arc_offset_macros::*;

use std::sync::Arc;
use std::ops::{Deref, Range};
use std::mem::size_of;
use std::marker::PhantomData;

/// The raison d'etre of this crate
///
/// For more information and sample usage, please refer to the [crate-level documentation].
///
/// [crate-level documentation]: index.html
#[derive(Debug)]
pub struct ArcOffset<Src, T> {
    src: Arc<Src>,
    offset: usize,
    marker: PhantomData<T>,
}

impl<Src, T> Clone for ArcOffset<Src, T> {
    fn clone(&self) -> Self {
        ArcOffset {
            src: self.src.clone(),
            offset: self.offset,
            marker: PhantomData,
        }
    }
}

#[doc(hidden)]
pub trait __OffsetHelper {
    type Inner;

    fn arc_offset(this: Arc<Self>) -> Self::Inner;
}

pub trait Offset {
    type Inner;

    fn arc_offset(self) -> Self::Inner;
}

impl<T: __OffsetHelper> Offset for Arc<T> {
    type Inner = T::Inner;

    fn arc_offset(self) -> T::Inner {
        T::arc_offset(self)
    }
}

/// A helper function for extracting the value of a reference
///
/// This is made public (albeit hidden) because it's useful within derive macros, in conjunction
/// with [`ArcOffset::new_unchecked`].
#[doc(hidden)]
#[inline(always)]
pub fn addr<T>(ptr: &T) -> usize {
    ptr as *const T as *const u8 as usize
}

impl<Src: Sized, T: Sized> ArcOffset<Src, T> {
    /// Constructs a new `ArcOffset` referencing the enum variant or field given by the target
    /// function.
    ///
    /// If the target function returns a reference that is outside the range of the source `Arc`,
    /// this function will panic. This should not happen with typical inputs.
    pub fn new(src: Arc<Src>, target: fn(&Src) -> &T) -> Self {
        let s: &Src = &src;
        let t = target(s);

        let src_range = Range {
            start: addr(s),
            end: addr(s) + size_of::<Src>(),
        };

        if !src_range.contains(&addr(t)) || !src_range.contains(&(addr(t) + size_of::<T>())) {
            panic!("failed to construct `ArcOffset`; `target` returned reference outside source");
        }

        let offset = addr(t) - addr(s);
        // Unsafety: the invariant that we're expected to uphold is that the value of type `T` is
        // contained within `Src` -- we know that to be true here, so we're good to go.
        unsafe { ArcOffset::new_unchecked(src, offset) }
    }
}

impl<Src, T> ArcOffset<Src, T> {
    /// An internal-only method provided for constucting an `ArcOffset` directly
    ///
    /// While this function contains no unsafe code directly, further *safe* methods on
    /// `ArcOffset`s require the invariants that are expected to be upheld here.
    ///
    /// ## Safety
    ///
    /// This function requires that there is a value of type `T` obtained at the byte offset
    /// `offset` from a reference to `Src`. The offset is in units of bytes because the value of
    /// `T` might not be aligned relative to `Src`.
    ///
    /// This function *really* shouldn't be called in normal code - it primarily exists to allow
    /// reasonable conversion implementations when deriving `ArcOffset` on an `enum`.
    #[doc(hidden)]
    #[inline(always)]
    pub unsafe fn new_unchecked(src: Arc<Src>, offset: usize) -> Self {
        ArcOffset { src, offset, marker: PhantomData }
    }
}

impl<Src, T: Sized> Deref for ArcOffset<Src, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // The implementation here is required to use unsafe. Due to the construction of the
        // `ArcOffset`, we know that there's a value of type `T` accessible at `offset` from the
        // original pointer.
        let target_addr = addr(&self.src as &Src) + self.offset;
        let target_ptr = unsafe {
            &*(target_addr as *const u8 as *const T)
        };

        target_ptr
    }
}

#[cfg(test)]
mod tests {
    use crate as arc_offset;

    #[test]
    fn test() {
        use arc_offset::{ArcOffset, Offset, addr};
        use std::sync::Arc;

        #[derive(ArcOffset)]
        enum Test {
            Foo(u8),
            Bar(i32),
        }

        let t = Arc::new(Test::Bar(3));
        let inner: TestArcOffset = t.arc_offset();
        let cloned: ArcOffset<_,i32> = match &inner {
            TestArcOffset::Bar(x) => {
                assert_eq!(&x as &i32, &3);
                ArcOffset::clone(&x)
            }
            _ => unreachable!(),
        };

        drop(inner);
        assert_eq!(*cloned, 3);
    }
}
