//! An experimental new version of the database, using `hydra`
//!
//! Once merged, this module will fully replace [`db`](../db/index.html).

use crate::token_tree::FileTokenTree;
use crate::tokens::SimpleToken;
use hydra::JobId;
use std::fs;
use std::io;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

// TODO: We actually need to modify `crate::error` to work with the new database
#[derive(Clone)]
pub struct CompilerError;

hydra::make_database! {
    /// The central database used for managing queries of every piece of information in the
    /// compiler
    pub struct Database {
        @single root_file: String,

        @indexed {
            pub emit_error -> errors: CompilerError,
            pub register_file -> files: String,
        }

        impl {
            pub get_file_content: GetFileContent,
            pub get_ast_info: GetAst,
        }
    }
}

/// A wrapper around `io::Error` to track whether an error has been reported to the user
#[derive(Debug)]
pub struct IoError {
    reported: AtomicBool,
    err: io::Error,
}

#[derive(Debug, Copy, Clone)]
pub struct FileId(usize);

pub type IoResult<T> = Result<Arc<T>, Arc<IoError>>;

#[hydra::query(GetFileContent)]
pub async fn file_content(
    db: Database,
    job: &JobId,
    file_name: String,
) -> hydra::Result<IoResult<(FileId, String)>> {
    // This is one of the few things that doesn't cooperate. Ironically, because using async here
    // would require *more* dependencies (and an additional runtime), we actually do blocking io
    // here -- without allowing the runtime to delay.
    //
    // Thankfully, file IO should take an incredibly small amount of time, so we're okay with
    // having a small amount of inefficiency here.

    // wrap with `Ok` because there's never any other DB requirements here
    Ok(match fs::read_to_string(&file_name) {
        Err(err) => Err(Arc::new(IoError {
            reported: AtomicBool::new(false),
            err,
        })),
        Ok(s) => {
            let id = db.register_file(job, file_name).await;

            Ok(Arc::new((FileId(id), s)))
        }
    })
}

/// A wrapper around the simple tokens, token tree, and AST parsed from a file
//
// This type implements `Drop` carefully so that we're allowed to have the self-referential fields
// following `tokens`
#[derive(Debug)]
pub struct AstGroup {
    file_content: Arc<(FileId, String)>,
    tokens: Vec<SimpleToken<'static>>,
    tt: FileTokenTree<'static>,
    items: Vec<crate::ast::Item<'static>>,
}

#[hydra::query(GetAst)]
pub async fn ast_group(
    db: Database,
    job: &JobId,
    file_name: String,
) -> hydra::Result<IoResult<AstGroup>> {
    let file_content = match db.get_file_content(job.new_child(), file_name).await {
        Err(e) => return Err(e),
        Ok(Err(e)) => return Ok(Err(e)),
        Ok(Ok(c)) => c,
    };

    let mut token_results = crate::tokens::tokenize(&file_content.1);
    let tokens: Vec<SimpleToken> = (token_results.iter().cloned())
        .take_while(Result::is_ok)
        .map(Result::unwrap)
        .collect::<Vec<_>>();

    // TODO: Actually store the errors
    let invalids = token_results
        .drain(tokens.len()..)
        .filter_map(Result::err)
        .collect::<Vec<_>>();

    let early_err = !invalids.is_empty();

    let tt: FileTokenTree = crate::token_tree::file_tree(&tokens, early_err);
    let _token_tree_errors = tt.collect_errors();

    let (items, _poisoned, _ast_errors) = crate::ast::try_parse(&tt.tokens, early_err);

    // UNSAFE:
    // We're able to extend the lifetime of everything here because the actual backing string for
    // the reference is kept alive by the `Arc`, which we get through `file_content` -- that's then
    // returned at the end alongside everything else.
    let items: Vec<crate::ast::Item<'static>> = unsafe { std::mem::transmute(items) };
    let tt: FileTokenTree<'static> = unsafe { std::mem::transmute(tt) };
    let tokens: Vec<SimpleToken<'static>> = unsafe { std::mem::transmute(tokens) };

    Ok(Ok(Arc::new(AstGroup {
        file_content,
        tokens,
        tt,
        items,
    })))
}

impl Drop for AstGroup {
    fn drop(&mut self) {
        // Drop all of the items in the opposite order to how they were created
        self.items.drain(..);
        self.tt.tokens.drain(..);
        self.tokens.drain(..);
    }
}
