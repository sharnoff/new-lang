//! A place for some of the "core" publicly-exposed type definitions
//!
//! These are all individually re-exported at the crate root

use crate::JobId;
use std::sync::Arc;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub enum Error {
    // Cycle errors always give the JobId that originally made the query;
    //
    // They aren't intended to be bubbled up. Instead, functions that receive a cycle error should
    // use a custom result type to separately track whatever additional information might be
    // required to generate an error message.
    Cycles(Arc<Vec<JobId>>),
}
