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
pub use runtime::{DBLayer, Indexed};

// Re-export `futures` so that we guarantee that it's available for us in the macro
#[doc(hidden)]
pub use futures;

/// The macro that constructs the root database type itself
///
/// Documentation is a WIP
#[macro_export]
macro_rules! make_database {
    (
        $(#[$attr:meta])*
        $vis:vis struct $db_name:ident {
            $(@single $single_vis:vis $single_name:ident: $single_ty:ty, )*

            $(@indexed {
                $( $idx_vis:vis $add_idx:ident -> $all_idx:ident: $idx_ty:ty, )+
            })?

            impl {
                $( $field_vis:vis $fn_name:ident: $trait:ident, )+
            }
        }
    ) => {
        $crate::make_database_internal! {
            ($(#[$attr])*) $vis $db_name
                ($($single_vis $single_name $single_ty, )*)
                ($($($idx_vis $add_idx $all_idx $idx_ty, )+)?)
                ($($field_vis $trait $fn_name, )+)
        }
    }
}
