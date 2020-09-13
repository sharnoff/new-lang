//! A place for some of the "core" publicly-exposed type definitions
//!
//! These are all individually re-exported at the crate root

use crate::JobId;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    // Cycle errors always give the JobId that was originally
    Cycles(Vec<JobId>),
}
