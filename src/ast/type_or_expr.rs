//! Parsing for places where we might either have a type *or* an expression

use super::*;

#[derive(Debug, Clone)]
pub enum TypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
    Ambiguous(AmbiguousTypeOrExpr<'a>),
}

#[derive(Debug, Clone)]
pub enum AmbiguousTypeOrExpr<'a> {
    Named(Path<'a>),
    Ref(RefTypeOrExpr<'a>),
    Tuple(TupleTypeOrExpr<'a>),
    Struct(StructTypeOrExpr<'a>),
    Array(ArrayTypeOrExpr<'a>),
}

#[derive(Debug, Clone)]
pub struct RefTypeOrExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    ref_token: &'a Token<'a>,
    value: Box<TypeOrExpr<'a>>,
}

#[derive(Debug, Clone)]
pub struct TupleTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    elements: Vec<TypeOrExpr<'a>>,
}

#[derive(Debug, Clone)]
pub struct StructTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    fields: Vec<StructFieldTypeOrExpr<'a>>,
    poisoned: bool,
}

#[derive(Debug, Clone)]
pub struct StructFieldTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    name: Ident<'a>,
    value: TypeOrExpr<'a>,
}

#[derive(Debug, Clone)]
pub struct ArrayTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    value: Box<TypeOrExpr<'a>>,
}

impl<'a> TypeOrExpr<'a> {
    pub fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TypeOrExpr<'a>, Option<usize>> {
        todo!()
    }
}
