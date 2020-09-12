//! A place for some of the "core" publicly-exposed type definitions

use crate::JobId;

pub type Result<T> = std::result::Result<T, Error>;

pub enum Error {
    // Cycle errors always give the JobId that was originally
    Cycle(JobId),
    Stale,
}
