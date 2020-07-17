//! The main parser
//!
//! The definition of the syntax can be found in the neighboring file, 'bnf.md'. This is how each
//! piece of the parser is defined, with additional ambiguities elaborated upon.

mod consumed;
pub mod errors;

// We blanket import everything from the parser submodules so that everything can be under a single
// namespace.
mod item;
pub use item::*;

use crate::token_tree::{self, Kwd, Token, TokenKind};
use consumed::Consumed;
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
