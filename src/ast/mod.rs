//! The main parser
//!
//! The definition of the syntax can be found in the neighboring file, 'bnf.md'. This is how each
//! piece of the parser is defined, with additional ambiguities elaborated upon.

#[macro_use]
mod macros;
mod consumed;
pub mod errors;
use errors::*;

// We blanket import everything from the parser submodules so that everything can be under a single
// namespace.
pub mod expr;
pub mod item;
pub mod literals;
pub mod pattern;
pub mod types;

use self::{expr::*, item::*, literals::*, pattern::*, types::*};

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
    mut tokens: TokenSlice<'a>,
    ends_early: bool,
) -> (Vec<Item<'a>>, Vec<Error<'a>>) {
    let mut items = Vec::new();
    let mut errors = Vec::new();

    while !tokens.is_empty() {
        match Item::consume(tokens, ends_early, None, &mut errors) {
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

#[derive(Debug, Copy, Clone)]
pub enum Node<'a> {
    Item(&'a Item<'a>),
    Expr(&'a Expr<'a>),
}
