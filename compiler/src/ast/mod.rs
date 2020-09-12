//! The main parser
//!
//! The definition of the syntax can be found in the neighboring file, 'bnf.md'. This is how each
//! piece of the parser is defined, with additional ambiguities elaborated upon.

#[macro_use]
mod macros;
mod consumed;
pub mod errors;
use errors::*;

#[cfg(test)]
mod tests;

// We blanket import everything from the parser submodules so that everything can be under a single
// namespace.
pub mod expr;
pub mod item;
pub mod literals;
pub mod pattern;
pub mod type_or_expr;
pub mod types;

use self::{expr::*, item::*, literals::*, pattern::*, type_or_expr::*, types::*};

use crate::token_tree::{self, Delim, Kwd, Punc, Token, TokenKind};
use consumed::Consumed;

/// An alias used internally for representing the type of token lists given by [`token_tree`]
///
/// [`token_tree`]: ../token_tree/index.html
type TokenSlice<'a> = &'a [TokenResult<'a>];

/// An alias used internally for representing a single reference to a token produced by
/// [`token_tree`].
///
/// [`token_tree`]: ../token_tree/index.html
type TokenResult<'a> = Result<Token<'a>, token_tree::Error<'a>>;

pub fn try_parse<'a>(
    tokens: TokenSlice<'a>,
    ends_early: bool,
) -> (Vec<Item<'a>>, bool, Vec<Error<'a>>) {
    let mut errors = Vec::new();

    let (items, poisoned) = Item::parse_all(tokens, ends_early, None, &mut errors);
    (items, poisoned, errors)
}
