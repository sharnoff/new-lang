//! Management for file-system interaction with the database

use crate::Database;
use hydra::JobId;
use std::borrow::Cow;
use std::fs;
use std::io;
use std::ops::Range;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// A unique identifier to track files that have been successfully read
///
/// A `FileId` may be used to access the file's content via the [`get_file`] method on
/// [`Database`].
///
/// [`Database`]: ../db/struct.Database.html
/// [`get_file`]: ../db/struct.Database.html#get_file
#[derive(Debug, Copy, Clone, Eq, PartialEq, hydra::Index)]
pub struct FileId(usize);

/// The information about a single file
#[derive(Debug, Clone)]
pub struct FileInfo {
    pub id: FileId,
    pub name: String,
    pub content: String,
}

impl FileInfo {
    pub fn get_line(&self, line_idx: usize) -> Cow<str> {
        todo!()
    }

    pub fn line_idx(&self, byte_idx: usize) -> usize {
        todo!()
    }

    pub fn col_idx(&self, byte_idx: usize) -> usize {
        todo!()
    }
}

pub type IoResult<T> = Result<Arc<T>, Arc<IoError>>;

/// A wrapper around `io::Error` to track whether an error has been reported to the user
#[derive(Debug)]
pub struct IoError {
    pub reported: AtomicBool,
    pub err: io::Error,
}

/// Attempts to get the file content of a file
///
/// This function also registers the file in the database's list of [`FileId`]s on success.
///
/// [`FileId`]: struct.FileId.html
#[hydra::query(GetFile)]
pub async fn file_content(
    db: Database,
    job: &JobId,
    file_name: String, // TODO: this should be a path instead
) -> hydra::Result<IoResult<FileInfo>> {
    // This function is one of the few async database functions that *doesn't* cooperate.
    // Ironically, because using async here would require *more* dependencies (and an additional
    // runtime), we actually do blocking io here -- without allowing the runtime to delay.
    //
    // Thankfully, file IO should take an incredibly small amount of time, relative to the rest of
    // the data processing we need to do, so we're okay with having a little bit of inefficiency
    // here.

    // wrap with `Ok` because there's never any other DB requirements here
    Ok(match fs::read_to_string(&file_name) {
        Err(err) => Err(Arc::new(IoError {
            reported: AtomicBool::new(false),
            err,
        })),
        Ok(content) => {
            let mut file = None;
            db.register_file(job, |id| {
                let f = Arc::new(FileInfo {
                    id,
                    name: file_name,
                    content,
                });

                file = Some(f.clone());
                f
            })
            .await;

            Ok(file.unwrap())
        }
    })
}

/// A byte range of a source file
#[derive(Debug, Copy, Clone)]
pub struct Span {
    pub file: FileId,
    // We use `start` and `end` here because we otherwise wouldn't be able to derive `Copy`... :(
    start: usize,
    end: usize,
}

impl Span {
    /// Attempts to join with another span, returning `None` if they do not belong to the same file
    ///
    /// For more information, refer to the infallible version of this method,
    /// [`join`](#method.join).
    pub fn try_join(self, other: Span) -> Option<Span> {
        if self.file != other.file {
            return None;
        }

        let range = Span::join_ranges(self.range(), other.range());
        Some(Span {
            file: self.file,
            start: range.start,
            end: range.end,
        })
    }

    /// Joins the two spans, panicking if they are not part of the same file
    ///
    /// For a fallible version of this method, see [`try_join`](#method.try_join).
    pub fn join(self, other: Span) -> Span {
        self.try_join(other)
            .expect("tried to join spans from different files")
    }

    /// Returns the range of the bytes in the file that this span corresponds to
    pub fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    /// An internal helper method to join two ranges
    ///
    /// ## Semantics
    ///
    /// This method produces a new range from the first start point to the last end point.
    /// Essentially, this means that - if the ranges are disjoint - the returned range will include
    /// the region between them.
    fn join_ranges(this: Range<usize>, other: Range<usize>) -> Range<usize> {
        Range {
            start: this.start.min(other.start),
            end: this.end.min(other.end),
        }
    }
}
