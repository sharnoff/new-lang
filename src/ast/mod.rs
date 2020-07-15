//! The main parser
//!
//! The definition of the syntax can be found in the neighboring file, 'bnf.md'. This is how each
//! piece of the parser is defined, with additional ambiguities elaborated upon.

pub mod errors;

use crate::token_tree::{Token, TokenKind};
use errors::Error;

pub fn try_parse<'a>(
    tokens: &'a [Token<'a>],
    ends_early: bool,
) -> Vec<Result<Item<'a>, Error<'a>>> {
    todo!()
}

#[derive(Debug, Clone)]
pub struct Item<'a> {
    src: &'a [Token<'a>],
    kind: ItemKind<'a>,
}

#[derive(Debug, Clone)]
enum ItemKind<'a> {
    Fn(FnDecl<'a>),
    Macro(MacroDef<'a>),
    Type(TypeDef<'a>),
    Trait(TraitDecl<'a>),
    Impl(ImplBlock<'a>),
    Const(ConstStmt<'a>),
    Static(StaticStmt<'a>),
    Import(ImportStmt<'a>),
    Use(UseStmt<'a>),
}

// These are all placeholders until they're properly written
type FnDecl<'a> = &'a str;
type MacroDef<'a> = &'a str;
type TypeDef<'a> = &'a str;
type TraitDecl<'a> = &'a str;
type ImplBlock<'a> = &'a str;
type ConstStmt<'a> = &'a str;
type StaticStmt<'a> = &'a str;
type ImportStmt<'a> = &'a str;
type UseStmt<'a> = &'a str;

pub enum Node<'a> {
    Item(&'a Item<'a>),
}

impl<'a> Item<'a> {
    fn parse_from(tokens: &'a [Token<'a>]) -> Result<Item<'a>, bool> {
        todo!()
    }
}
