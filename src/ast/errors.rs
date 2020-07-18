//! Error types and messages for parsing into the AST

use super::TokenSlice;
use crate::error::{Builder as ErrorBuilder, ToError};
use crate::token_tree::{self, Kwd, Token};
use std::ops::Range;

pub enum Error<'a> {
    /// One of the leading keywords for an item was expected, but some other token was found.
    ExpectedItemKwd {
        kwds: &'static [Kwd],
        found: Source<'a>,
    },

    /// We parsed the `const` keyword as the start of an `Item`, but didn't find what we were
    /// expecting - either an `FnDecl` or a `ConstStmt`.
    ///
    /// Function declarations are started by `[ "const" ] [ "pure" ] "fn"`, whereas const
    /// statements are started by `"const" Ident`.
    ///
    /// This is a more specialized error because it exists for a very specific case to provide a
    /// better error message.
    ExpectedAfterItemConst {
        /// The token giving us the "const" keyword
        before: &'a Token<'a>,
        /// The token (or EOF) that we found instead
        found: Source<'a>,
    },

    /// Certain `Item`s are not allowed to have proof statements before them. This error allows us
    /// to give a clear error message when this type of mistake has been made.
    ProofStmtsDisallowedBeforeItem {
        stmts: TokenSlice<'a>,
        item_kind: ItemKind,
    },

    /// Certain `Item`s aren't allowed to have visibility qualifiers before them. This error allows
    /// us to give a clear error message when this type of mistake has been made.
    VisDisallowedBeforeItem {
        vis: Source<'a>,
        item_kind: ItemKind,
    },

    /// If parsing an item starts with `["const", "pure"]` or `["pure", "const"]`, we expect `"fn"`
    /// next. In the event that this wasn't what we found, we have a special case here because it
    /// might not be completely clear to the user what went wrong.
    ConstPureExpectedFn {
        /// The two tokens preceeding what we expected to be a "fn" keyword
        before: [&'a Token<'a>; 2],
        /// The token (or EOF) that we found instead
        found: Source<'a>,
    },

    /// Whenever we have an item definition starting with the "pure" keyword, we're expecting a
    /// function declaration. We're therefore expecting the next token to be either a "const"
    /// keyword or "fn" keyword.
    PureItemExpectedFnDecl {
        /// The token giving the "pure" keyword
        before: &'a Token<'a>,
        /// The token (or EOF) that we found instead
        found: Source<'a>,
    },

    /// A catch-all error for generically expecting certain tokens or syntax elements
    Expected {
        kind: ExpectedKind<'a>,
        found: Source<'a>,
    },
}

/// An individual source for a range of the source text, used within error messages.
#[derive(Debug, Copy, Clone)]
pub enum Source<'a> {
    EndDelim(&'a Token<'a>),
    TokenResult(Result<&'a Token<'a>, token_tree::Error<'a>>),
    EOF,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ItemKind {
    Const,
    ImplBlock,
    ImportStmt,
    UseStmt,
}

#[derive(Debug, Copy, Clone)]
pub enum ExpectedKind<'a> {
    Ident(IdentContext<'a>),
    FnBody { fn_src: TokenSlice<'a> },
    FnBodyOrReturnType { fn_src: TokenSlice<'a> },
}

#[derive(Debug, Copy, Clone)]
pub enum IdentContext<'a> {
    /// The identifier used to name functions, provided immediately following the `fn` keyword. The
    /// attached slice of tokens gives the keywords used that indicate a function declaration.
    FnDeclName(TokenSlice<'a>),
}

#[derive(Debug, Copy, Clone)]
pub enum GenericParamsContext<'a> {
    /// The generic parameters used in a function declaration. The attached slice of tokens gives
    /// the keywords and name that indicate a function declaration.
    FnDecl(TokenSlice<'a>),
}

#[derive(Debug, Copy, Clone)]
pub enum TypeContext<'a> {
    /// The optional return type used in a function declaration. The attached slice of tokens gives
    /// all of the preceeding parts of the item.
    FnDeclReturn(TokenSlice<'a>),
}

impl<F: Fn(&str) -> Range<usize>> ToError<(F, &str)> for Error<'_> {
    fn to_error(self, _aux: &(F, &str)) -> ErrorBuilder {
        todo!()
    }
}
