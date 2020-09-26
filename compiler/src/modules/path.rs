//! Module path manipulation and file opening

use std::path::{Path, PathBuf};

/// A helper type used for marking the absolute path to a module, starting from the package root
// Internally, we use an empty list to represent the package root
#[derive(Debug, Clone, Hash)]
pub struct ModulePath {
    components: Vec<String>,
}

impl ModulePath {
    /// Returns whether the path points to the package root
    fn is_root(&self) -> bool {
        self.components.is_empty()
    }

    /// Appends the package-internal module path to the given filesystem path
    pub(super) fn append_to(&self, path: &Path) -> PathBuf {
        let mut path: PathBuf = path.into();
        self.components.iter().for_each(|c| path.push(c));

        path
    }
}
