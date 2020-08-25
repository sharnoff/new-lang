//! Parsing for places where we might either have a type *or* an expression

use super::*;

#[derive(Debug, Clone)]
pub enum MaybeTypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
    Ambiguous(TypeOrExpr<'a>),
}

#[derive(Debug, Clone)]
pub enum TypeOrExpr<'a> {
    Named(Path<'a>),
    Ref(RefTypeOrExpr<'a>),
    Tuple(TupleTypeOrExpr<'a>),
    Struct(StructTypeOrExpr<'a>),
    Array(ArrayTypeOrExpr<'a>),
}

#[derive(Debug, Clone)]
pub struct RefTypeOrExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub ref_token: &'a Token<'a>,
    pub value: Box<TypeOrExpr<'a>>,
}

#[derive(Debug, Clone)]
pub struct TupleTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub elements: Vec<TypeOrExpr<'a>>,
    pub poisoned: bool,
}

#[derive(Debug, Clone)]
pub struct StructTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<StructFieldTypeOrExpr<'a>>,
    pub poisoned: bool,
}

#[derive(Debug, Clone)]
pub struct StructFieldTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub name: Ident<'a>,
    pub value: TypeOrExpr<'a>,
}

#[derive(Debug, Clone)]
pub struct ArrayTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub value: Box<TypeOrExpr<'a>>,
}

impl<'a> TypeOrExpr<'a> {
    pub fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: TokenSlice<'a>,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MaybeTypeOrExpr<'a>, Option<usize>> {
        todo!()
    }
}
