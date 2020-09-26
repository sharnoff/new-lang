//! Management for file-system interaction with the database

use crate::Database;
use hydra::JobId;
use std::borrow::Cow;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use tokio::{fs, io};
use unicode_width::UnicodeWidthStr;

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
    pub path: PathBuf,
    pub name: String,
    pub content: String,
    line_ranges: Vec<Range<usize>>,
}

impl FileInfo {
    /// Returns the [`Span`](struct.Span.html) corresponding to the end of the file
    pub fn eof_span(&self) -> Span {
        Span {
            file: self.id,
            // Note that we go one byte past the end of the file here.
            // The support for len + 1 is baked into the other functions on `FileInfo` taking
            // spans, and we need to do this because we otherwise wouldn't be guarantee a non-zero
            // length'd span inside the file. (it may be empty)
            start: self.content.len(),
            end: self.content.len() + 1,
        }
    }

    /// Returns the line corresponding to the given index in the lines of the file's content
    ///
    /// If the provided index is greater than or equal to the number of lines in the file, this
    /// function will panic.
    ///
    /// Please note that the index is interpreted as starting at zero.
    pub fn get_line(&self, line_idx: usize) -> Cow<str> {
        let line = &self.content[self.line_ranges[line_idx].clone()];

        if line.contains('\t') {
            Cow::Owned(line.replace('\t', "    "))
        } else {
            Cow::Borrowed(line)
        }
    }

    /// Returns the line index corresponding to the given byte in the file
    ///
    /// If the given byte index is outside the range of bytes in the file, this function will
    /// panic. A small exception is made for the *ending* byte of the file -- the byte index is
    /// permitted to be exactly equal to the length of the file, but no greater.
    ///
    /// Please note that the returned index starts from zero; it is compatible with [`get_line`].
    ///
    /// [`get_line`]: #method.get_line
    pub fn line_idx(&self, byte_idx: usize) -> usize {
        if byte_idx > self.content.len() {
            panic!(
                "received byte index {} for file {:?} of size {}",
                byte_idx,
                self.name,
                self.content.len()
            );
        }

        self.line_ranges
            .binary_search_by_key(&byte_idx, |range| range.start)
            // Because `binary_search` returns the index where a value could be inserted to
            // maintain the ordering, a byte index between two lines will return the index of the
            // second, not the first - hence why we need to subtract one here.
            .unwrap_or_else(|i| i - 1)
    }

    /// Returns the column index corresponding to the given byte in the file
    ///
    /// The same restrictions on and behavior surrounding `byte_idx` apply here as from
    /// [`line_idx`](#method.line_idx).
    ///
    /// Please note that the returned index starts from zero.
    pub fn col_idx(&self, byte_idx: usize) -> usize {
        let line_range = self.line_ranges[self.line_idx(byte_idx)].clone();

        // We're nearly there. If the line contains any tab characters (it shouldn't!), we'll
        // replace them and then get the line.
        let line = &self.content[line_range.start..byte_idx];
        let width = line.width();

        let n_tabs = line.as_bytes().iter().filter(|&b| b == &b'\t').count();

        // Because `unicode_width` registers tabs as having zero width when part of a larger string,
        // we need to add that in for ourselves. We'll say that each tab is equivalent to four
        // spaces :P
        width + n_tabs * 4
    }

    /// An internal helper function to produce the `lines` field of `FileInfo`
    fn make_lines(content: &str) -> Vec<Range<usize>> {
        let content_mem_addr = content as *const str as *const u8 as usize;

        content
            .lines()
            .map(|line| {
                let line_mem_addr = line as *const str as *const u8 as usize;
                let start = line_mem_addr - content_mem_addr;
                let end = start + line.len();

                start..end
            })
            .collect()
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
    file_path: PathBuf,
) -> hydra::Result<IoResult<FileInfo>> {
    // wrap with `Ok` because there's never any other DB requirements here
    Ok(match fs::read_to_string(&file_path).await {
        Err(err) => Err(Arc::new(IoError {
            reported: AtomicBool::new(false),
            err,
        })),
        Ok(content) => {
            let line_ranges = FileInfo::make_lines(&content);
            let name = file_path.to_string_lossy().into();

            let mut file = None;
            db.register_file(job, |id| {
                let f = Arc::new(FileInfo {
                    id,
                    path: file_path,
                    name,
                    content,
                    line_ranges,
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
    pub start: usize,
    pub end: usize,
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
