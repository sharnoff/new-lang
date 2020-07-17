//! Type parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types                                                                                          //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Type<'a> {
    Named(NamedType<'a>),
    Ref(RefType<'a>),
    Mut(MutType<'a>),
    Array(ArrayType<'a>),
    Struct(StructType<'a>),
    Tuple(TupleType<'a>),
    Enum(EnumType<'a>),
}

#[derive(Debug)]
pub struct NamedType<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    generic_args: GenericArgs<'a>,
    refinements: Option<Refinements<'a>>,
}

#[derive(Debug)]
pub struct RefType<'a> {
    pub(super) src: TokenSlice<'a>,
    ty: Box<Type<'a>>,
}

#[derive(Debug)]
pub struct MutType<'a> {
    pub(super) src: TokenSlice<'a>,
    has_not: Option<&'a Token<'a>>,
    ty: Box<Type<'a>>,
}

#[derive(Debug)]
pub struct ArrayType<'a> {
    pub(super) src: &'a Token<'a>,
    ty: Box<Type<'a>>,
    length: Option<Expr<'a>>,
}

#[derive(Debug)]
pub struct StructType<'a> {
    pub(super) src: &'a Token<'a>,
    fields: Vec<StructTypeField<'a>>,
}

#[derive(Debug)]
pub struct TupleType<'a> {
    pub(super) src: &'a Token<'a>,
    elems: Vec<Type<'a>>,
}

#[derive(Debug)]
pub struct EnumType<'a> {
    pub(super) src: TokenSlice<'a>,
    variants: Vec<(Ident<'a>, Type<'a>)>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper bits                                                                                    //
// * StructTypeField                                                                              //
// * Refinements                                                                                  //
//   * Refinement                                                                                 //
// * TypeBound                                                                                    //
// * GenericArgs                                                                                  //
//   * GenericArg                                                                                 //
//     * TypeGenericArg                                                                           //
//     * ConstGenericArg                                                                          //
//     * RefGenericArg                                                                            //
// * Trait                                                                                        //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct StructTypeField<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    ty: Option<Type<'a>>,
    bound: Option<TypeBound<'a>>,
    default: Option<Expr<'a>>,
}

#[derive(Debug)]
pub struct Refinements<'a> {
    pub(super) src: TokenSlice<'a>,
    refs: Vec<Refinement<'a>>,
}

#[derive(Debug)]
pub enum Refinement<'a> {
    Ref(RefRefinement<'a>),
    Init(InitRefinement<'a>),
}

#[derive(Debug)]
pub struct RefRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    is_mut: Option<&'a Token<'a>>,
    expr: Expr<'a>,
}

#[derive(Debug)]
pub struct InitRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    not: Option<&'a Token<'a>>,
    maybe: Option<&'a Token<'a>>,
}

#[derive(Debug)]
pub struct TypeBound<'a> {
    pub(super) src: TokenSlice<'a>,
    refinements: Option<Refinements<'a>>,
    traits: Vec<Trait<'a>>,
}

#[derive(Debug)]
pub struct GenericArgs<'a> {
    pub(super) src: TokenSlice<'a>,
    args: Vec<GenericArg<'a>>,
    traits: Vec<Trait<'a>>,
}

#[derive(Debug)]
pub enum GenericArg<'a> {
    Type(TypeGenericArg<'a>),
    Bound(TypeBoundGenericArg<'a>),
    Const(ConstGenericArg<'a>),
    Ref(RefGenericArg<'a>),
}

#[derive(Debug)]
pub struct TypeGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Option<Ident<'a>>,
    type_arg: Type<'a>,
}

#[derive(Debug)]
pub struct TypeBoundGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    bound: TypeBound<'a>,
}

#[derive(Debug)]
pub struct ConstGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Option<Ident<'a>>,
    value: Expr<'a>,
}

#[derive(Debug)]
pub struct RefGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    refinement: Refinement<'a>,
}

#[derive(Debug)]
pub struct Trait<'a> {
    pub(super) src: TokenSlice<'a>,
    path: Path<'a>,
    generic_args: GenericArgs<'a>,
}
