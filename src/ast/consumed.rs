//! A wrapper module for the `Consumed` trait
//!
//! For more information, refer to [the documentation](trait.Consumed.html) for the trait.

use super::*;

/// A trait for providing the number of tokens consumed in the construction of each syntax element
///
/// This is provided as a trait (instead of individual methods) so that certain types that aren't
/// owned in this module (e.g. `Option<Vis>`) may implement this as well. To allow this, there is a
/// blanket implementation of `Consumed` for `Option<T>`, where `T: Consumed`.
pub(super) trait Consumed {
    /// Gives the number of tokens consumed to construct the syntax element
    fn consumed(&self) -> usize;
}

impl<T: Consumed> Consumed for Option<T> {
    fn consumed(&self) -> usize {
        self.as_ref().map(Consumed::consumed).unwrap_or(0)
    }
}

impl<'a> Consumed for Item<'a> {
    fn consumed(&self) -> usize {
        use Item::*;

        match self {
            Fn(fn_decl) => fn_decl.consumed(),
            Macro(macro_def) => macro_def.consumed(),
            Type(type_def) => type_def.consumed(),
            Trait(trait_decl) => trait_decl.consumed(),
            Impl(impl_block) => impl_block.consumed(),
            Const(const_stmt) => const_stmt.consumed(),
            Static(static_stmt) => static_stmt.consumed(),
            Import(import_stmt) => import_stmt.consumed(),
            Use(use_stmt) => use_stmt.consumed(),
        }
    }
}

impl<'a> Consumed for FnDecl<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for MacroDef<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for TypeDecl<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for TraitDef<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for ImplBlock<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for ConstStmt<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for StaticStmt<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for ImportStmt<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for UseStmt<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for ProofStmts<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for Vis<'a> {
    fn consumed(&self) -> usize {
        match self {
            Vis::Pub { .. } => 1,
        }
    }
}
