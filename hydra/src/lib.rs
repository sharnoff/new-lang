//! The query-handling database for the compiler and associated systems
//!
//! A significant portion of the implementation is within the macros given in the `hydra-macros`
//! crate as well. This is located in the neighboring 'macros' directory.

#[doc(hidden)]
pub use hydra_macros::__make_database as make_database_internal;

// pub use hydra_macros::input;
pub use hydra_macros::query;

mod core;
mod job_id;
mod runtime;

pub mod internal;

pub use self::core::{Error, Result};
pub use job_id::JobId;
pub use runtime::DBLayer;

#[macro_export]
macro_rules! make_database {
    (
        $(#[$attr:meta])*
        $vis:vis struct $db_name:ident impl {
            $( $field_vis:vis $fn_name:ident: $trait:ident, )+
        }
    ) => {
        $crate::make_database_internal! {
            ($(#[$attr])*) $vis $db_name ($($field_vis $trait $fn_name, )+)
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
