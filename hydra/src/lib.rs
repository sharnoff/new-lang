//! The query-handling database for the compiler and associated systems
//!
//! A significant portion of the implementation is within the macros given in the `hydra-macros`
//! crate as well. This is located in the neighboring 'macros' directory.

#[doc(hidden)]
pub use hydra_macros::__make_database as make_database_internal;

// pub use hydra_macros::input;
pub use hydra_macros::{query, Index};

mod core;
mod job_id;
mod runtime;

pub mod internal;

pub use self::core::{Error, Result};
pub use internal::Runtime;
pub use job_id::JobId;
pub use runtime::{DBLayer, Index, Indexed};

// Re-export `tokio` so that we guarantee that it's available for us inside the macro
#[doc(hidden)]
pub use tokio;

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
                $( $idx_vis:vis $add_idx:ident -> $get_idx:ident as $index:ty => $all_idx:ident: $idx_ty:ty, )+
            })?

            impl {
                $( $field_vis:vis $fn_name:ident: $trait:ident, )+
            }
        }
    ) => {
        $crate::make_database_internal! {
            ($(#[$attr])*) $vis $db_name
                ($($single_vis $single_name $single_ty, )*)
                ($($($idx_vis $add_idx $get_idx $index $all_idx $idx_ty, )+)?)
                ($($field_vis $trait $fn_name, )+)
        }
    }
}
