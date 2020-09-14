//! An experimental new version of the database, using `hydra`
//!
//! Once merged, this module will fully replace [`db`](../db/index.html).

use crate::files::{FileId, FileInfo, GetFile, IoResult};
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
            pub emit_error as usize => errors: CompilerError,
            pub register_file as FileId => files: Arc<FileInfo>,
        }

        impl {
            pub get_file: GetFile,
            pub get_ast_info: GetAst,
        }
    }
}

/// A wrapper around the simple tokens, token tree, and AST parsed from a file
//
// This type implements `Drop` carefully so that we're allowed to have the self-referential fields
// following `tokens`
#[derive(Debug)]
pub struct AstGroup {
    file: Arc<FileInfo>,
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
    let file = match db.get_file(job.new_child(), file_name).await {
        Err(e) => return Err(e),
        Ok(Err(e)) => return Ok(Err(e)),
        Ok(Ok(c)) => c,
    };

    let mut token_results = crate::tokens::tokenize(&file.content);
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
        file,
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
