//! A wrapper module for the `Consumed` trait
//!
//! For more information, refer to [the documentation](trait.Consumed.html) for the trait.

/// A trait for providing the number of tokens consumed in the construction of each syntax element
///
/// This is provided as a trait (instead of individual methods) so that certain types that aren't
/// owned in this module (e.g. `Option<Vis>`) may implement this as well. To allow this, there is a
/// blanket implementation of `Consumed` for `Option<T>`, where `T: Consumed`.
pub(super) trait Consumed {
    /// Gives the number of tokens consumed to construct the syntax element
    fn consumed(&self) -> usize;
}

impl<T: Consumed> Consumed for Box<T> {
    fn consumed(&self) -> usize {
        (&self as &T).consumed()
    }
}

impl<T: Consumed> Consumed for Option<T> {
    fn consumed(&self) -> usize {
        self.as_ref().map(T::consumed).unwrap_or(0)
    }
}

impl<T: Consumed> Consumed for Vec<T> {
    fn consumed(&self) -> usize {
        self.iter().map(T::consumed).sum()
    }
}
