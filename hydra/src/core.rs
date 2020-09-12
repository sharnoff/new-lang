//! A place for some of the "core" publicly-exposed type definitions
//!
//! These are all individually re-exported at the crate root

use crate::JobId;
use std::sync::mpsc::Receiver;

pub type Result<T> = std::result::Result<T, Error>;

pub enum Error {
    // Cycle errors always give the JobId that was originally
    Cycles(Vec<JobId>),
}

pub enum Future<T> {
    Done(T),
    Queued(Receiver<T>),
}

impl<T> Future<T> {
    pub fn wait(self) -> T {
        match self {
            Future::Done(t) => t,
            Future::Queued(chan) => chan.recv().unwrap(),
        }
    }
}
