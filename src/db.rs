//! The central database side of the compiler, responsible for handling and serving queries

use crate::error::{self, ToError};
use crate::token_tree::FileTokenTree;
use crate::utils::Guarded;
use crate::{ast, token_tree, tokens};
use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, RwLock};
use std::{fs, io};
use unicode_width::UnicodeWidthStr;

/// A container for tracking all of the files that may be used through the process of compilation
///
/// This struct is essentially a wrapper around a `HashMap<PathBuf, Arc<FileState>>`, where the files are
/// indexed by their canonicalized path (from the source). "Pretty" formatting for their path names
/// are given stored individually, within the [`FileState`] struct.
///
/// Typical usage will use the [`file`] method to access a [`FileState`], which lazily computes all
/// of the information that might be used later. Individual files are added via the [`reserve`]
/// method, which does no actual computation.
///
/// Individual `FileState`s also track any errors that accumulate through the course of their
/// action, which can all be printed with the [`print_errors`] method.
///
/// [`FileState`]: struct.FileState.html
/// [`file`]: #method.file
/// [`reserve`]: #method.reserve
/// [`print_errors`]: #method.print_errors
pub struct Files {
    files: Mutex<HashMap<PathBuf, Arc<FileState>>>,
}

/// All of the information that may be given about a single file in isolation
///
/// This includes the various pieces of information necessary to produce the AST. This will be
/// expanded in the future as more functionality is added to the compiler.
//
// A note on internals:
//
// Each of the types with lifetimes here are given 'static - this is because they all reference
// items that are stored locally within this struct. Many, for example, reference the raw contents
// of the file - these are stored in `raw_file`, but might be required by all of the fields below
// it!
//
// In order to account for this, we'd like to wrap these in `Pin`, but that severely limits some
// (otherwise safe) functionality. So we give them a 'static lifetime and simply treat them
// carefully whenever we use them - this mostly translates to a manual implementation of `Drop`.
pub struct FileState {
    path: String,

    /// The full contents of the file
    file_info: RwLock<Option<Result<FileInfo, io::Error>>>,

    /// The "simple" tokens in the file. This value will be `None` if not yet computed, and
    /// `Some(None)` if the value could not be computed due to a previous error
    simple_tokens: RwLock<Option<Option<SimpleTokenOutput<'static>>>>,

    /// The token tree from the file. Like `simple_tokens`, this will be `None` if not yet computed,
    /// and `Some(None)` if the value couldn't be computed due to a previous error
    token_tree: RwLock<Option<Option<TokenTreeOutput<'static>>>>,

    /// The abstract syntax tree for the file.
    ast: RwLock<Option<Option<AstOutput<'static>>>>,

    /// The local cache of messages for errors that might have occured during the end-to-end process
    /// of creating the AST. These will be ordered by the process in which they occured (e.g.
    /// tokenizing before parsing), and will
    errors: Mutex<Vec<error::Builder>>,
    // TODO types: Option<TypeCheckOutput>,
    // TODO asm: Option<AsmOutput>,
}

/// A collection of information about a file
///
/// This includes the file's content and a cache of where each line begins.
pub struct FileInfo {
    /// The string containing the bytes of the file. This *must not* be changed post-initialization.
    content: String,

    /// A list of each line in the file's content, given by its starting byte index and the text of
    /// the entire line. This is used when formatting error messages in order to give the line
    /// containing a given byte index.
    ///
    /// The strings are *not* actually static - they reference `content`, but have had their
    /// lifetime extended so that they can be stored within the same structure.
    lines: Vec<LineInfo<'static>>,
}

/// The filtered output type from simple tokenization
///
/// The actual type given by [`crate::tokens`] is instead a list of `Result`s - we filter them out
/// here in order to pass them into creating token trees.
///
/// The `tokens` field contains all of the tokens that occured before any error, and the
/// `early_err` field indicates whether there was an error during tokenizing that has prevented the
/// entire contents of the file from being included in the list of tokens.
///
/// [`crate::tokens`]: ../tokens/index.html
pub struct SimpleTokenOutput<'a> {
    pub tokens: Vec<tokens::SimpleToken<'a>>,
    pub early_err: bool,
}

/// The output type from producing token trees
type TokenTreeOutput<'a> = token_tree::FileTokenTree<'a>;

/// The output type from producing
type AstOutput<'a> = Vec<ast::item::Item<'a>>;

impl Files {
    /// Creates a new, empty set of files
    ///
    /// Individual files should be added with the [`reserve`] method.
    ///
    /// [`reserve`]: #method.reserve.html
    pub fn new() -> Self {
        Files {
            files: Mutex::new(HashMap::new()),
        }
    }

    /// A function to help with mocking the file state; only available when testing
    ///
    /// This function is essentially provides the equivalent of calling [`Files::reserve`] with the
    /// given path, alongside setting the return value for [`FileState::get_content`] to always give
    /// `input`.
    ///
    /// NOTE: because this is for *mocking* the typical usage, this function does not attempt to
    /// canonicalize the path input into the store.
    ///
    /// [`Files::reserve`]: #method.reserve
    /// [`FileState::get_content`]: struct.FileState.html#method.get_content
    #[cfg(test)]
    pub fn mock_single_file(name: impl AsRef<Path>, content: &str) -> Self {
        let mut files = HashMap::new();

        let mut fs = FileState::reserve(name.as_ref().to_string_lossy());
        fs.file_info = RwLock::new(Some(Ok(String::from(content).into())));
        files.insert(name.as_ref().into(), Arc::new(fs));

        Files {
            files: Mutex::new(files),
        }
    }

    /// Ensures a [`FileState`] with the given file path will be present
    ///
    /// This should be called before any call to [`file`] where the given path might not have been
    /// loaded. The path need not be canonicalized, though it should either be relative to the
    /// current working directory or be absolute.
    ///
    /// [`FileState`]: struct.FileState.html
    pub fn reserve(&mut self, path: impl AsRef<Path>) {
        // We attempt to get the absolute, canonical path for the file. If this somehow fails, we
        // simply use the path we already had.
        let abs_path = path
            .as_ref()
            .canonicalize()
            .unwrap_or_else(|_| path.as_ref().into());

        let mut guard = self.files.lock().unwrap();

        if !guard.contains_key(&abs_path) {
            // TODO: We could allow the user to specify this manually
            let path_name: String = abs_path.to_string_lossy().into();
            guard.insert(abs_path, Arc::new(FileState::reserve(path_name)));
        }
    }

    /// Gets a [`FileState`] with the given path from the hashmap, panicking if it is not present
    pub fn file(&self, path: impl AsRef<Path>) -> Arc<FileState> {
        let abs_path = path
            .as_ref()
            .canonicalize()
            .unwrap_or_else(|_| path.as_ref().into());
        self.files.lock().unwrap().get(&abs_path).unwrap().clone()
    }

    /// Prints all of the errors that occured throughout the lifetime of this object
    ///
    /// This method consumes its target, because the errors are destroyed as they are printed. The
    /// total number of errors encountered are returned.
    pub fn print_errors(self) -> usize {
        // Because the errors need to be able to access a `Files` to format, we can't have the
        // hashmap locked when we're printing them. To get around this, we'll drain all of the
        // errors into a single list before we print them.

        let mut errors = Vec::new();
        for file in self.files.lock().unwrap().values() {
            errors.extend(file.errors.lock().unwrap().drain(..));
        }

        let count = errors.len();

        // Now we'll print all of the errors
        for err in errors {
            eprintln!("{}", err.pretty_fmt(&self));
        }

        count
    }
}

impl<'a> FileState {
    /// Creates a new `FileState` without attempting to open the corresponding file
    fn reserve(path: impl Into<String>) -> Self {
        FileState {
            path: path.into(),
            file_info: RwLock::new(None),
            simple_tokens: RwLock::new(None),
            token_tree: RwLock::new(None),
            ast: RwLock::new(None),
            errors: Mutex::new(Vec::new()),
        }
    }

    /// Gets the content of the file, as given by `self.path`
    ///
    /// If the file has not yet been read, this will read the file and produce any error generated.
    /// Otherwise, the stored content (or resulting error) will be used. If there *was* an error,
    /// this will add it to the internal store, after calling `handle_err` to create a message. The
    /// passed function can be used to create detailed error messages indicating where the user
    /// *actually* went wrong (beyond simply "failed to open file").
    pub fn get_content(
        &'a self,
        handle_err: impl FnOnce(&io::Error) -> error::Builder,
    ) -> Result<impl 'a + Guarded<Output = &'a FileInfo>, ()> {
        // If we haven't already generated information about the file, we'll put it here.
        //
        // We encase this in a check with a read guard because the read-write lock wouldn't be
        // useful if we required obtaining write access to the contents in order to produce a read
        // guard.
        if self.file_info.read().unwrap().is_none() {
            // We'll now attempt to get unique access.
            let mut write_guard = self.file_info.write().unwrap();

            // If it's *still* none, we'll read the file to provide the content
            if write_guard.is_none() {
                *write_guard = Some(fs::read_to_string(&self.path).map(FileInfo::from));
            }
        }

        let read_guard = self.file_info.read().unwrap();

        if let Err(e) = read_guard.as_ref().unwrap().as_ref() {
            self.errors.lock().unwrap().push(handle_err(e));
            return Err(());
        }

        fn map<'a, D: 'a + Deref<Target = Result<FileInfo, io::Error>>>(res: &D) -> &'a FileInfo {
            // The lifetime extension here *is* unsafe, but it's generally okay because the file
            // content won't change once it's been created.
            let res: &'a D = unsafe { std::mem::transmute(res) };
            res.as_ref().unwrap()
        }

        Ok(crate::utils::Mapped {
            provider: crate::utils::Guard {
                provider: read_guard,
                map: |ref guard| guard.as_ref().unwrap(),
            },
            map,
        })
    }

    /// Gets the list of [`tokens::SimpleToken`]s corresponding to the content of the file
    ///
    /// If the file has not yet been tokenized, this function will call [`tokens::tokenize`] to do
    /// so. In the event that there was an error reading the file, `handle_err` will be used to
    /// generate an error message to save to the local error store.
    ///
    /// [`tokens::SimpleToken`]: ../tokens/enum.SimpleToken.html
    pub fn get_simple_tokens(
        &'a self,
        handle_err: impl FnOnce(&io::Error) -> error::Builder,
    ) -> impl 'a + Deref<Target = Option<SimpleTokenOutput<'a>>> {
        // If we haven't already tokenized, we'll do it here
        if self.simple_tokens.read().unwrap().is_none() {
            let mut write_guard = self.simple_tokens.write().unwrap();
            if write_guard.is_none() {
                let tokens = match self.get_content(handle_err) {
                    Err(()) => None,
                    Ok(file_info) => {
                        // We'll take contiguous set of valid tokens from the start, producing
                        // errors for the invalid tokens (of those that remain).
                        let content: &str = &file_info.get().content;
                        let mut token_results = crate::tokens::tokenize(content);
                        let n_tokens = token_results.len();

                        // TODO: This might be highly inefficient ~ this should be benchmarked at
                        // some point to determine what the best solution is *in the success case*.
                        let valids = token_results
                            .iter()
                            .cloned()
                            .take_while(Result::is_ok)
                            .map(Result::unwrap)
                            .collect::<Vec<_>>();
                        let invalids = token_results
                            .drain(valids.len()..)
                            .filter_map(Result::err)
                            .collect::<Vec<_>>();

                        let early_err = !invalids.is_empty();

                        // Now we'll produce some errors, if there were any.
                        let offset_fn = |line: &str| {
                            let start = (line as *const str as *const u8 as usize)
                                - (content as *const str as *const u8 as usize);

                            start..start + line.len()
                        };

                        if !invalids.is_empty() {
                            let mut errors = self.errors.lock().unwrap();

                            errors.reserve(invalids.len());
                            errors.extend(
                                invalids
                                    .into_iter()
                                    .map(|t| t.to_error(&(offset_fn, &self.path))),
                            );
                        }

                        Some(SimpleTokenOutput {
                            tokens: valids,
                            early_err,
                        })
                    }
                };

                // Lifetime extension - we do this because we're putting these tokens into the
                // struct that contains the string they reference.
                //
                // This is safe because of (1) the limitations we place on `file_info`, in that
                // the string cannot change, and (2) the implementation of `Drop` guarantees that
                // these tokens won't outlive the string they reference.
                let tokens: Option<SimpleTokenOutput<'static>> =
                    unsafe { std::mem::transmute(tokens) };

                *write_guard = Some(tokens);
            }
        }

        let read_guard = self.simple_tokens.read().unwrap();

        crate::utils::Guard {
            provider: read_guard,
            map: |ref guard| guard.as_ref().unwrap(),
        }
    }

    /// Produces the token tree as given by [`token_tree::file_tree`] on the entire input of the
    /// file
    ///
    /// If the token tree has already been produced, this will simply return the pre-computed
    /// value. Otherwise, if the file was unable to be read, the returned value will be `None`, with
    /// an error message added by `handle_err`.
    ///
    /// [`token_tree::file_tree`]: ../token_tree/index.html
    pub fn get_token_tree(
        &'a self,
        handle_err: impl FnOnce(&io::Error) -> error::Builder,
    ) -> impl 'a + Deref<Target = Option<TokenTreeOutput<'a>>> {
        // If we haven't already constructed the token tree, we'll do that here
        if self.token_tree.read().unwrap().is_none() {
            let mut write_guard = self.token_tree.write().unwrap();
            if write_guard.is_none() {
                let simple_tokens = self.get_simple_tokens(handle_err);
                match Deref::deref(&simple_tokens) {
                    None => *write_guard = Some(None),
                    Some(tokens) => {
                        let token_tree: FileTokenTree =
                            crate::token_tree::file_tree(&tokens.tokens, tokens.early_err);

                        let token_errors = token_tree.collect_errors();
                        if !token_errors.is_empty() {
                            // We're safe to get `file_info` because it should have been done by
                            // now, as we called `get_simple_tokens`. Because we called
                            // `get_simple_tokens`, `file_info` would only have a bad value if the
                            // file couldn't be read - this would mean that `early_err` would be
                            // true and no tokens would be provided to `file_tree`.
                            //
                            // This specific scenario can't result in any errors, so we know that
                            // `file_info` *is* valid.
                            let info_guard = self.file_info.read().unwrap();
                            let content: &str =
                                &info_guard.as_ref().unwrap().as_ref().unwrap().content;

                            let offset_fn = |line: &str| {
                                let start = (line as *const str as *const u8 as usize)
                                    - (content as *const str as *const u8 as usize);

                                start..start + line.len()
                            };

                            let mut errors = self.errors.lock().unwrap();
                            errors.reserve(token_errors.len());
                            errors.extend(
                                token_errors
                                    .into_iter()
                                    .map(|t| t.to_error(&(offset_fn, &self.path))),
                            );
                        }

                        // Lifetime extension ~ we're okay to do this because the token tree
                        // references the string given in `file_info`, which isn't changed until
                        // the `FileState` is dropped. The manual `Drop` implementation additionally
                        // ensures that this is dropped before `file_info`.
                        let token_tree: FileTokenTree<'static> =
                            unsafe { std::mem::transmute(token_tree) };
                        *write_guard = Some(Some(token_tree));
                    }
                }
            }
        }

        let read_guard = self.token_tree.read().unwrap();

        crate::utils::Guard {
            provider: read_guard,
            map: |ref guard| guard.as_ref().unwrap(),
        }
    }

    /// Produces the abstract syntax tree, as given by [`ast::try_parse`] on the entire input of
    /// the file
    ///
    /// If the abstract syntax tree has already been produced, this will simply return the
    /// pre-computed value. Otherwise, this will call `ast::try_parse` to return the value. If the
    /// couldn't be read, the returned value will be `None`, with an error message added by
    /// `handle_err`.
    ///
    /// [`ast::try_parse`]: ../ast/fn.try_parse.html
    pub fn get_ast(
        &'a self,
        handle_err: impl FnOnce(&io::Error) -> error::Builder,
    ) -> impl 'a + Deref<Target = Option<AstOutput<'a>>> {
        // If we haven't already parsed the ast, we'll do that here
        if self.ast.read().unwrap().is_none() {
            let mut write_guard = self.ast.write().unwrap();
            if write_guard.is_none() {
                let token_tree = self.get_token_tree(handle_err);
                match Deref::deref(&token_tree) {
                    None => *write_guard = Some(None),
                    Some(tt) => {
                        // We can unwrap `simple_tokens` twice because (1) we know it's already been
                        // calculated by the time `get_token_tree` finishes, and (2) if the inner
                        // option were `None`, so would `token_tree`.
                        let early_err = (self.simple_tokens.read().unwrap())
                            .as_ref()
                            .unwrap()
                            .as_ref()
                            .unwrap()
                            .early_err;

                        let (items, poisoned, ast_errors) =
                            crate::ast::try_parse(&tt.tokens, early_err);
                        if !ast_errors.is_empty() {
                            let info_guard = self.file_info.read().unwrap();
                            let content: &str =
                                &info_guard.as_ref().unwrap().as_ref().unwrap().content;

                            let end_point = match content {
                                "" => 0..0,
                                _ => (content.len() - 1)..content.len(),
                            };

                            let offset_fn = |string: Option<&str>| match string {
                                Some(s) => {
                                    let start = (s as *const str as *const u8 as usize)
                                        - (content as *const str as *const u8 as usize);

                                    start..start + s.len()
                                }
                                None => end_point.clone(),
                            };

                            let mut errors = self.errors.lock().unwrap();
                            errors.reserve(ast_errors.len());
                            errors.extend(
                                ast_errors
                                    .into_iter()
                                    .map(|t| t.to_error(&(offset_fn, &self.path))),
                            );
                        }

                        let items: Vec<crate::ast::item::Item<'static>> =
                            unsafe { std::mem::transmute(items) };
                        *write_guard = Some(Some(items));
                    }
                }
            }
        }

        let read_guard = self.ast.read().unwrap();

        crate::utils::Guard {
            provider: read_guard,
            map: |ref guard| guard.as_ref().unwrap(),
        }
    }

    /// A convenience wrapper for calling [`FileInfo::line_idx`]
    ///
    /// This function is exactly:
    /// ```
    /// self.get_content(|_| panic!("unexpected io error"))
    ///     .unwrap()
    ///     .get()
    ///     .line_idx(byte_idx)
    /// ```
    ///
    /// [`FileInfo::line_idx`]: struct.FileInfo.html#method.line_idx
    pub fn line_idx(&self, byte_idx: usize) -> usize {
        self.get_content(|_| panic!("unexpected io error"))
            .unwrap()
            .get()
            .line_idx(byte_idx)
    }

    /// A convenience wrapper for calling [`FileInfo::col_idx`]
    ///
    /// This function is exactly:
    /// ```
    /// self.get_content(|_| panic!("unexpected io error"))
    ///     .unwrap()
    ///     .get()
    ///     .col_idx(byte_idx)
    /// ```
    ///
    /// [`FileInfo::col_idx`]: struct.FileInfo.html#method.col_idx
    pub fn col_idx(&self, byte_idx: usize) -> usize {
        self.get_content(|_| panic!("unexpected io error"))
            .unwrap()
            .get()
            .col_idx(byte_idx)
    }

    /// A convenience wrapper for calling [`FileInfo::get_line`]
    ///
    /// This function is exactly:
    /// ```
    /// self.get_content(|_| panic!("unexpected io error"))
    ///     .unwrap()
    ///     .get()
    ///     .get_line(line_idx)
    /// ```
    ///
    /// [`FileInfo::get_line`]: struct.FileInfo.html#method.get_line
    pub fn get_line(&'a self, line_idx: usize) -> Cow<'a, str> {
        self.get_content(|_| panic!("unexpected io error"))
            .unwrap()
            .get()
            .get_line(line_idx)
    }
}

impl Drop for FileState {
    // There's more detail above about why we need to manually implement drop - please refer to the
    // line comments above the `FileState` type definition.
    fn drop(&mut self) {
        use std::sync::{LockResult, RwLockWriteGuard as WriteGuard};

        fn force<'a, T>(res: &'a mut LockResult<WriteGuard<T>>) -> &'a mut T {
            match res.as_mut() {
                Ok(t) => t,
                Err(e) => e.get_mut(),
            }
        }

        drop(force(&mut self.ast.write()).take());
        drop(force(&mut self.token_tree.write()).take());
        drop(force(&mut self.simple_tokens.write()).take());
        drop(force(&mut self.file_info.write()).take());
    }
}

/// The information about a single line of text in a source file
///
/// This contains all of the cached content that might be later used.
struct LineInfo<'a> {
    /// The starting byte index of the line
    start_idx: usize,

    /// The string given directly by the file
    raw: &'a str,
}

impl From<String> for FileInfo {
    fn from(content: String) -> Self {
        let base = content.as_ref() as *const str as *const u8 as usize;

        let lines: Vec<LineInfo> = content
            .lines()
            .map(|line| {
                let start_idx = (line as *const str as *const u8 as usize) - base;

                LineInfo {
                    start_idx,
                    raw: line,
                }
            })
            .collect();

        // Lifetime extension ~ this is only made safe because we drop `lines` before `content`,
        // which is what we borrow from.
        let lines: Vec<LineInfo<'static>> = unsafe { std::mem::transmute(lines) };

        FileInfo { content, lines }
    }
}

impl FileInfo {
    /// Returns the line index of the byte index in this file
    ///
    /// If the character at the given byte index is a newline, it the line on which the newline
    /// character starts will be returned.
    ///
    /// Note that line indices (as returned by this function) start at zero.
    pub fn line_idx(&self, byte_idx: usize) -> usize {
        (self.lines)
            .binary_search_by_key(&byte_idx, |l| l.start_idx)
            .unwrap_or_else(|idx| idx - 1)
    }

    /// Returns the column of the byte index corresponding to the byte index in the this file
    pub fn col_idx(&self, mut byte_idx: usize) -> usize {
        // TODO: This function isn't as efficient as it could be, but that's okay for now - this is
        // only really used in printing errors, so we can get away with it being a little slower.
        //
        // A future improvement might make this faster, but that's not something that urgently
        // needs doing.

        let idx = self.line_idx(byte_idx);

        // And now we'll set the byte index to be within the *line*
        byte_idx -= self.lines[idx].start_idx;

        // We're nearly there. If the line contains any tab characters (it shouldn't!), we'll
        // replace them and then get the line.
        let n_tabs = self.lines[idx]
            .raw
            .as_bytes()
            .iter()
            .filter(|&&b| b == b'\t')
            .count();

        if n_tabs != 0 {
            // Because we're replacing one character with 4, we're increasing the number of bytes
            // by 3 for each tab.
            byte_idx += 3 * n_tabs;

            // Substitute each tab with four spaces - if there's tabs somewhere weird (i.e. not at
            // the start of a line), that's the user's fault, and so they can deal with it not
            // looking perfect
            let line = self.lines[idx].raw.replace('\t', "    ");
            UnicodeWidthStr::width(&line[..byte_idx])
        } else {
            byte_idx = byte_idx.min(self.lines[idx].raw.len());
            UnicodeWidthStr::width(&self.lines[idx].raw[..byte_idx])
        }
    }

    /// Returns the line with the given index from the file
    ///
    /// The returned string will have all tab characters replaced by four spaces.
    pub fn get_line<'a>(&'a self, line_idx: usize) -> Cow<'a, str> {
        let line = &self.lines[line_idx].raw;

        if line.contains('\t') {
            Cow::Owned(line.replace('\t', "    "))
        } else {
            Cow::Borrowed(line)
        }
    }
}

impl Drop for FileInfo {
    fn drop(&mut self) {
        // We need to drop `self.lines` because it references `self.content`
        self.lines.drain(..);
    }
}
