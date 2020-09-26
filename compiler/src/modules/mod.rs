//! Initial handling for module hierarchies in the source code
//!
//! This takes the AST itself as input, and does not permit cyclic dependencies. The module
//! hierarchy defined here is only within the current package; this stage in the compilation
//! pipeline primarily serves to organize the parsed files into the module stucture they represent.
//!
//! On a technical level, generating the module hierarchy is actually responsible for finding and
//! parsing the directory structure.

// use crate::ast;
use crate::ast::item::{
    ArcConstItem, ArcFnItem, ArcImplItem, ArcStaticItem, ArcTraitItem, ArcTypeItem, ArcUseItem,
};
use crate::db::{Database, JobId};
use crate::files::IoResult;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

mod path;
pub use path::ModulePath;

/// The entrypoint for generating module information
///
/// This function is responsible for generating the parse queries for all of the source files that
/// will be compiled.
#[hydra::query(GetModule)]
async fn module_at_path(
    db: Database,
    job: &JobId,
    path: ModulePath,
) -> hydra::Result<IoResult<Module>> {
    let root_file = db.root_directory().await;
    let file_path = path.append_to(&root_file);

    Module::parse_file_path(db, job, file_path).await
}

/// The file extensions that may be used for source files
///
/// This is defined in a central place so that it can be changed - if necessary - in the future.
static FILE_EXT: &[&str] = &["tc"];

/// A single module, without including any submodules
///
/// We don't include submodules here because otherwise we'd be generating the global structure from
/// a *single* query, making it harder to track the individual pieces that have dependencies.
#[derive(Debug)]
pub struct Module {
    /// The global path to the module
    abs_path: ModulePath,

    /// The set of *named* items defined within the module
    ///
    /// Of the available items given by the AST, named items are defined as everything except
    /// `impl` blocks -- they do not directly define a name. Note that this additionally includes
    /// sub-modules.
    ///
    /// The value in this map will be equal to `None` for any name with multiple definitions.
    named_items: HashMap<String, Option<NamedItem>>,

    /// The `impl` blocks defined within the module
    impls: Vec<ArcImplItem>,
}

#[derive(Debug, Clone)]
enum NamedItem {
    Fn(ArcFnItem),
    // // Macros are not supported yet - they will likely have a distinct method of storage so that
    // // macros may have the same name as other items.
    // Macro(ArcTypeItem),
    Type(ArcTypeItem),
    Trait(ArcTraitItem),
    Const(ArcConstItem),
    Static(ArcStaticItem),
    // // Imports are also not yet supported, but they *will* go here
    // Import(ArcImportItem),
    Use(ArcUseItem),
}

impl Module {
    async fn parse_file_path(
        db: Database,
        job: &JobId,
        path: PathBuf,
    ) -> hydra::Result<IoResult<Self>> {
        match db.ast_info(job.new_child(), path).await {
            _ => todo!(),
        }
    }
}
