//! The main parser
//!
//! The definition of the syntax can be found in the neighboring file, 'bnf.md'. This is how each
//! piece of the parser is defined, with additional ambiguities elaborated upon.

pub mod errors;

// We blanket import everything from the parser submodules so that everything can be under a single
// namespace.
mod item;
pub use item::*;

use crate::token_tree::{self, Kwd, Token, TokenKind};
use errors::{Error, Source};

/// An alias used internally for representing the type of token lists given by [`token_tree`]
///
/// [`token_tree`]: ../token_tree/index.html
type TokenSlice<'a> = &'a [Result<Token<'a>, token_tree::Error<'a>>];

pub fn try_parse<'a>(
    mut tokens: TokenSlice<'a>,
    ends_early: bool,
) -> (Vec<Item<'a>>, Vec<Error<'a>>) {
    let mut items = Vec::new();
    let mut errors = Vec::new();

    while !tokens.is_empty() {
        match Item::consume_from(tokens, ends_early, None, &mut errors) {
            Ok(item) => {
                tokens = &tokens[item.consumed()..];
                items.push(item);
            }
            Err(Some(consumed)) => tokens = &tokens[consumed..],
            Err(None) => break,
        }
    }

    (items, errors)
}

#[derive(Debug)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    src: TokenSlice<'a>,
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    Placeholder(&'a str),
}

#[derive(Debug, Copy, Clone)]
pub enum Node<'a> {
    Item(&'a Item<'a>),
    Expr(&'a Expr<'a>),
}

/// A trait for providing the number of tokens consumed in the construction of each syntax element
///
/// This is provided as a trait (instead of individual methods) so that certain types that aren't
/// owned in this module (e.g. `Option<Vis>`) may implement this as well. To allow this, there is a
/// blanket implementation of `Consumed` for `Option<T>`, where `T: Consumed`.
trait Consumed {
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
            // Macro(macro_def) => macro_def.consumed(),
            // Type(type_def) => type_def.consumed(),
            // Trait(trait_decl) => trait_decl.consumed(),
            // Impl(impl_block) => impl_block.consumed(),
            Const(const_stmt) => const_stmt.consumed(),
            // Static(static_stmt) => static_stmt.consumed(),
            // Import(import_stmt) => import_stmt.consumed(),
            // Use(use_stmt) => use_stmt.consumed(),
            _ => todo!(),
        }
    }
}

impl<'a> Consumed for FnDecl<'a> {
    fn consumed(&self) -> usize {
        self.src.len()
    }
}

impl<'a> Consumed for ConstStmt<'a> {
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
