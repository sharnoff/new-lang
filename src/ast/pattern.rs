//! Pattern parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Pattern variants                                                                               //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Pattern<'a> {
    Struct(StructPattern<'a>),
    Tuple(TuplePattern<'a>),
    Array(ArrayPattern<'a>),
    Name(NamePattern<'a>),
    Assign(AssignPattern<'a>),
    Ref(RefPattern<'a>),
}

#[derive(Debug)]
pub struct StructPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    path: Option<Path<'a>>,
    fields: Vec<FieldPattern<'a>>,
    has_dots: Option<&'a Token<'a>>,
}

#[derive(Debug)]
pub struct TuplePattern<'a> {
    pub(super) src: TokenSlice<'a>,
    path: Option<Path<'a>>,
    elements: Vec<Pattern<'a>>,
    has_dots: Option<&'a Token<'a>>,
}

#[derive(Debug)]
pub struct ArrayPattern<'a> {
    pub(super) src: &'a Token<'a>,
    path: Option<Path<'a>>,
    elements: Vec<Pattern<'a>>,
    has_dots: Option<&'a Token<'a>>,
}

#[derive(Debug)]
pub struct NamePattern<'a> {
    pub(super) src: TokenSlice<'a>,
    is_mut: Option<&'a Token<'a>>,
    name: Ident<'a>,
}

#[derive(Debug)]
pub struct AssignPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    assignee: Assignee<'a>,
}

#[derive(Debug)]
pub struct RefPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Box<Pattern<'a>>,
}

impl<'a> Pattern<'a> {
    pub fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Pattern<'a>, Option<usize>> {
        todo!()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * FieldPattern                                                                                 //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct FieldPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    binding: Option<Pattern<'a>>,
}
