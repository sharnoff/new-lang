//! Type parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types                                                                                          //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A single concrete type
///
/// The BNF definition for types is:
/// ```text
/// Type = Ident [ GenericArgs ] [ Refinements ]
///      | "&" [ Refinements ] Type
///      | [ "!" ] "mut" Type
///      | "[" Type [ ";" Expr ] "]" Refinemnts
///      | "{" [ StructField { "," StructField } [ "," ] ] "}"
///      | "(" [ Type        { "," Type        } [ "," ] ] ")"
///      | "enum" "{" { Ident Type "," } "}" .
/// ```
/// There *are* many different variants here. These definitions could be equally written with the
/// types that represent them, with:
/// ```text
/// Type = NamedType
///      | RefType
///      | MutType
///      | ArrayType
///      | StructType
///      | TupleType
///      | EnumType .
/// ```
///
/// One of the last key things to note is that while `[ "!" ] "mut"` is *syntactically* allowed
/// before any type (hence `mut mut int` is valid), repetitions of this prefix are not
/// *semantically* allowed. This validation is left until later.
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

impl<'a> Type<'a> {
    /// Consumes a `Type` as a prefix of the given tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Type<'a>, Option<usize>> {
        // This parser is relatively simple; we can just parse based on the type of token that we
        // find. The syntax for each individual type is fairly distinct; we don't need to account
        // for special cases.
        make_getter!(macro_rules! get, tokens, ends_early, errors);

        let fst = get!(
            0,
            Err(e) => Error::Expected {
                kind: ExpectedKind::Type(ctx),
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::Type(ctx),
                found: end_source!(containing_token),
            },
        );

        macro_rules! consume {
            ($type:ident, $variant:ident) => {{
                $type::consume(tokens, ends_early, containing_token, errors).map(Type::$variant)
            }};
        }

        use Delim::{Curlies, Parens, Squares};
        use TokenKind::{Ident, Keyword, Punctuation, Tree};

        match &fst.kind {
            Ident(_) => consume!(NamedType, Named),
            Punctuation(Punc::And) => consume!(RefType, Ref),
            Punctuation(Punc::Not) | Keyword(Kwd::Mut) => consume!(MutType, Mut),
            Tree { delim: Squares, .. } => consume!(ArrayType, Array),
            Tree { delim: Curlies, .. } => consume!(StructType, Struct),
            Tree { delim: Parens, .. } => consume!(TupleType, Tuple),
            Keyword(Kwd::Enum) => consume!(EnumType, Enum),
            _ => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::Type(ctx),
                    found: Source::TokenResult(Ok(fst)),
                });

                return Err(None);
            }
        }
    }
}

impl<'a> NamedType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<NamedType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> RefType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<RefType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> MutType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MutType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> ArrayType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ArrayType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> StructType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<StructType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> TupleType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TupleType<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> EnumType<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<EnumType<'a>, Option<usize>> {
        todo!()
    }
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

impl<'a> TypeBound<'a> {
    pub fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeBoundContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TypeBound<'a>, Option<usize>> {
        todo!()
    }
}
