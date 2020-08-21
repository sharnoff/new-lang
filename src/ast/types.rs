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
/// Type = Path [ Refinements ]
///      | "&" [ Refinements ] Type
///      | [ "!" ] "mut" Type
///      | "[" Type [ ";" Expr ] "]" [ Refinemnts ]
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
#[derive(Debug, Clone)]
pub enum Type<'a> {
    Named(NamedType<'a>),
    Ref(RefType<'a>),
    Mut(MutType<'a>),
    Array(ArrayType<'a>),
    Struct(StructType<'a>),
    Tuple(TupleType<'a>),
    Enum(EnumType<'a>),
}

/// A named type
///
/// Named types are given by their path (including optional generic arguments) and any refinements.
///
/// The BNF is defined as:
/// ```text
/// NamedType = Path [ Refinements ] .
/// ```
/// Note that [`Path`] is defined such that we can expand this definition to:
/// ```text
/// NamedType = Ident [ GenericsArgs ] { "." Ident [ GenericsArgs ] } [ Refinements ] .
/// ```
/// which then shows where generics arguments are allowed.
///
/// All of the carefulness around path ambiguity applies here - as such, the standard parser for
/// this type cannot be used in cases where there might be ambiguity around the generic arguments.
///
/// [`Path`]: ../expr/struct.Path.html
#[derive(Debug, Clone)]
pub struct NamedType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub path: Path<'a>,
    pub refinements: Option<Refinements<'a>>,
}

#[derive(Debug, Clone)]
pub struct RefType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub ty: Box<Type<'a>>,
}

#[derive(Debug, Clone)]
pub struct MutType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub has_not: Option<&'a Token<'a>>,
    pub ty: Box<Type<'a>>,
}

#[derive(Debug, Clone)]
pub struct ArrayType<'a> {
    pub(super) src: &'a Token<'a>,
    pub ty: Box<Type<'a>>,
    pub length: Option<Expr<'a>>,
}

#[derive(Debug, Clone)]
pub struct StructType<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<StructTypeField<'a>>,
}

#[derive(Debug, Clone)]
pub struct TupleType<'a> {
    pub(super) src: &'a Token<'a>,
    pub elems: Vec<Type<'a>>,
}

#[derive(Debug, Clone)]
pub struct EnumType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub variants: Vec<(Ident<'a>, Type<'a>)>,
}

impl<'a> Type<'a> {
    /// Consumes a `Type` as a prefix of the given tokens
    ///
    /// Please note that this function should not be used wherever there might be ambiguity about
    /// generic arguments - e.g. in type binding expressions.
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

        macro_rules! consume {
            ($type:ident, $variant:ident) => {{
                $type::consume(tokens, ends_early, containing_token, errors).map(Type::$variant)
            }};
        }

        use TokenKind::{Ident, Keyword, Punctuation, Tree};

        make_expect!(tokens, 0, ends_early, containing_token, errors);
        expect!((
            Ident(_) => consume!(NamedType, Named),
            Punctuation(Punc::And) => consume!(RefType, Ref),
            Punctuation(Punc::Not) | Keyword(Kwd::Mut) => consume!(MutType, Mut),
            Tree { delim, .. } => {
                let fst = tokens[0].as_ref().unwrap();
                let res = match delim {
                    Delim::Squares => ArrayType::parse(fst, errors).map(Type::Array),
                    Delim::Curlies => StructType::parse(fst, errors).map(Type::Struct),
                    Delim::Parens => TupleType::parse(fst, errors).map(Type::Tuple),
                };

                res.map_err(|()| Some(1))
            },
            Keyword(Kwd::Enum) => consume!(EnumType, Enum),
            @else ExpectedKind::Type(ctx),
        ))
    }
}

impl<'a> NamedType<'a> {
    /// Consumes a named type as a prefix of the given tokens
    ///
    /// Please note that this function should not be used wherever there might be ambiguity about
    /// generic arguments.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<NamedType<'a>, Option<usize>> {
        // The BNF is duplicated here for a brief explanation:
        //   Path [ GenericsArgs ] [ Refinements ]
        // The rest of the function is pretty short, so this should suffice.

        let path = Path::consume(tokens, ends_early, containing_token, errors).map_err(|_| None)?;
        let mut consumed = path.consumed();

        let refinements =
            Refinements::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|_| None)?;
        consumed += refinements.consumed();

        Ok(NamedType {
            src: &tokens[..consumed],
            path,
            refinements,
        })
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
    fn parse(token: &'a Token<'a>, errors: &mut Vec<Error<'a>>) -> Result<ArrayType<'a>, ()> {
        todo!()
    }
}

impl<'a> StructType<'a> {
    fn parse(token: &'a Token<'a>, errors: &mut Vec<Error<'a>>) -> Result<StructType<'a>, ()> {
        todo!()
    }
}

impl<'a> TupleType<'a> {
    fn parse(token: &'a Token<'a>, errors: &mut Vec<Error<'a>>) -> Result<TupleType<'a>, ()> {
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
// * GenericsArgs                                                                                  //
//   * GenericsArg                                                                                 //
//     * TypeGenericsArg                                                                           //
//     * ConstGenericsArg                                                                          //
//     * RefGenericsArg                                                                            //
//     * AmbiguousGenericsArg                                                                      //
//     * TypeOrExpr                                                                               //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct StructTypeField<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub ty: Option<Type<'a>>,
    pub bound: Option<TypeBound<'a>>,
    pub default: Option<Expr<'a>>,
}

#[derive(Debug, Clone)]
pub struct Refinements<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refs: Vec<Refinement<'a>>,
}

#[derive(Debug, Clone)]
pub enum Refinement<'a> {
    Ref(RefRefinement<'a>),
    Init(InitRefinement<'a>),
}

#[derive(Debug, Clone)]
pub struct RefRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    pub is_mut: Option<&'a Token<'a>>,
    pub expr: Expr<'a>,
}

#[derive(Debug, Clone)]
pub struct InitRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    pub not: Option<&'a Token<'a>>,
    pub maybe: Option<&'a Token<'a>>,
}

#[derive(Debug, Clone)]
pub struct TypeBound<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refinements: Option<Refinements<'a>>,
    pub traits: Vec<Path<'a>>,
}

/// A collection of generics arguments
///
/// Individual generic arguments are represented by the [`GenericsArg`] type, which exists solely as
/// a helper for this type. The BNF definition for the combination of these two types is:
/// ```text
/// GenericsArgs = "<" "(" GenericsArg { "," GenericsArg } [ "," ] ")" ">"
///             | "<" GenericsArg ">" .
/// GenericsArg = [ Ident ":" ] Type
///            | [ Ident ":" ] BlockExpr
///            | "ref" Expr .
/// ```
///
/// Generics arguments are a large part of the ambiguity present in the sytnax. To keep complexity
/// localized, the primary parser for this type ([`try_consume`]) simply assumes no ambiguity - it
/// must be dealt with externally.
///
/// There is additionally ambiguity present *within* singular generics arguments themselves. This
/// is explained further in the documentation for [`GenericsArg`].
///
/// [`GenericsArg`]: enum.GenericsArg.html
/// [`try_consume`]: #method.try_consume
#[derive(Debug, Clone)]
pub struct GenericsArgs<'a> {
    pub(super) src: TokenSlice<'a>,
    pub args: Vec<GenericsArg<'a>>,
    pub poisoned: bool,
}

/// A single generics argument
///
/// Before reading the documentation for this type, please first refer to the larger-picture
/// explanation given in the documentation for [`GenericsArgs`].
///
/// This type is the singular generics argument, defined with the following BNF:
/// ```text
/// GenericsArg = [ Ident ":" ] Type
///            | [ Ident ":" ] BlockExpr
///            | "ref" Expr .
/// ```
/// Even though it may appear as such at first glance, this definition does not have any ambiguity
/// (so long as we permit a longer-than-usual lookahead). This definition *is* complex, however, so
/// the bulk of the effort of disambiguating between the first two variants is done within the main
/// parser method, [`consume`].
///
/// Each of the variants shown above directly correspond the variants of this enum, in the same
/// order.
///
/// [`GenericsArgs`]: struct.GenericsArgs.html
/// [`consume`]: #method.consume
#[derive(Debug, Clone)]
pub enum GenericsArg<'a> {
    Type(TypeGenericsArg<'a>),
    Const(ConstGenericsArg<'a>),
    Ref(RefGenericsArg<'a>),
    Ambiguous(AmbiguousGenericsArg<'a>),
}

#[derive(Debug, Clone)]
pub struct TypeGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub type_arg: Type<'a>,
}

#[derive(Debug, Clone)]
pub struct ConstGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub value: Expr<'a>,
}

#[derive(Debug, Clone)]
pub struct RefGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Expr<'a>,
}

#[derive(Debug, Clone)]
pub struct AmbiguousGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub refs: Vec<&'a Token<'a>>,
    pub path: PathComponent<'a>,
}

#[derive(Debug)]
pub enum TypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
    Ambiguous {
        consumed: usize,
        refs: Vec<&'a Token<'a>>,
        path: PathComponent<'a>,
    },
}

impl<'a> Refinements<'a> {
    pub fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<Refinements<'a>>, Option<usize>> {
        todo!()
    }
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

impl<'a> GenericsArgs<'a> {
    /// Attempts to consume generics arguments as a prefix of the given tokens, failing with
    /// `Ok(None)` if the tokens clearly do not start with generics arguments.
    ///
    /// More specifically, this returns `Ok(None)` if the first element of the tkens is not a
    /// less-than token (`"<"`). Otherwise, this will fully attempt to parse, generating all
    /// relevant erorrs and returning `Err` upon complete failure.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    ///
    /// Please additionally note that this function should not be used wherever there might be
    /// ambiguity due to these generic arguments.
    pub fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<GenericsArgs<'a>>, Option<usize>> {
        // Marked TODO because the generics parsing here hasn't yet been modified to disallow
        // multiple arguments without parentheses.
        todo!()
        /*
        // First, we'll check for whether there's a "<". If there isn't, we'll just return.
        match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Lt) => (),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        }

        let mut consumed = 1;
        let mut poisoned = false;
        let mut args = Vec::new();

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        loop {
            let arg_res = GenericsArg::consume(
                &tokens[consumed..],
                &tokens[..consumed],
                ends_early,
                containing_token,
                errors,
            );
            match arg_res {
                Ok(a) => {
                    consumed += a.consumed();
                    args.push(a);
                }
                Err(None) => return Err(None),
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
            }

            expect!((
                // If we find ">", it's the end of the generic arguments.
                TokenKind::Punctuation(Punc::Gt) => {
                    consumed += 1;
                    break;
                },
                // If we find ",", we're expecting another generic arguments
                TokenKind::Punctuation(Punc::Comma) => {
                    consumed += 1;
                    continue;
                },
                @else ExpectedKind::GenericsArgDelim { prev_tokens: &tokens[consumed..] },
            ));
        }

        Ok(Some(GenericsArgs {
            src: &tokens[..consumed],
            args,
            poisoned,
        }))
        */
    }

    // Note: returns generics args, poisoned, consumed
    pub fn consume_inner(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(Vec<GenericsArg<'a>>, bool, usize), Option<usize>> {
        todo!()
    }

    pub fn can_be_expr(args: &[GenericsArg]) -> bool {
        todo!()
    }
}

impl<'a> GenericsArg<'a> {
    /// Consumes a single generics argument as a prefix of the tokens given
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    ///
    /// This is primarily a helper function for [`GenericsArgs::consume`]. For more information,
    /// refer to the documentation on either of these types.
    ///
    /// [`GenericsArgs::consume`]: struct.GenericsArgs.html#consume
    fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericsArg<'a>, Option<usize>> {
        // Parsing a generics argument is somewhat complicated - this is due to the fact that two
        // of the variants share their first two tokens, but only optionally. Reference arguments
        // can be determined immediately becuase they start with "ref", so parsing for those is
        // delegated to `RefGenericsArg::consume`

        let mut consumed = 0;
        make_getter!(macro_rules! get, tokens, ends_early, errors);
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let fst = get!(
            0,
            Err(e) => Error::Expected {
                kind: ExpectedKind::GenericsArg { prev_tokens },
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::GenericsArg { prev_tokens },
                found: end_source!(containing_token),
            },
        );

        let mut name = match &fst.kind {
            TokenKind::Keyword(Kwd::Ref) => {
                return RefGenericsArg::consume(tokens, ends_early, containing_token, errors)
                    .map_err(|_| None)
                    .map(GenericsArg::Ref);
            }
            TokenKind::Ident(name) => Some(Ident { src: fst, name }),
            _ => None,
        };

        // We make this a loop so that we can break out of the block if it turns out that the name
        // we originally saw wasn't for one of the generics arguments.
        if name.is_some() {
            // Because we just parsed an identifier, we'll see if the generics argument starts with
            //   Ident ":"
            // If it doesn't, it's entirely possible that the starting identifier was instead as
            // part of a type parameter (not a block expression, though), but only if the token
            // following the identifier is one of the following set:
            //   { "|",  "," , ">" , "<" }
            //     └┬┘   └┬┘   └┬┘   └┬┘
            //      │     └──┬──┘    Ident is the name of a type, followed by generic arguments
            //      │   Ident *is* the type, followed by next generic arg / end of generic args
            //      │   list
            //  Ident *is* the type, followed by refinements
            expect!((
                // Per the comment above, we'll discard the original identifier, as it must be part
                // of the type.
                TokenKind::Punctuation(Punc::Comma)
                | TokenKind::Punctuation(Punc::Gt)
                | TokenKind::Punctuation(Punc::Or)
                | TokenKind::Punctuation(Punc::Lt) => name = None,
                // Otherwise, if we find `Ident ":"`, we'll consume both and parse the type from
                // the new starting point
                TokenKind::Punctuation(Punc::Colon) => consumed = 2,
                // Anything else wouldn't have been vaid either way, so we'll
                @else ExpectedKind::GenericsArgFollowIdent {
                    prev_tokens,
                    ident: fst,
                },
            ));
        }

        // Past this point, we konw that whatwe hae left is either a type or an expression. We'll
        // make use of `TypeOrExpr::consume` to handle this.
        let res = TypeOrExpr::consume(
            &tokens[consumed..],
            prev_tokens,
            ends_early,
            containing_token,
            errors,
        );

        match res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(consumed + c)),
            Ok(TypeOrExpr::Type(type_arg)) => {
                consumed += type_arg.consumed();
                Ok(GenericsArg::Type(TypeGenericsArg {
                    src: &tokens[..consumed],
                    name,
                    type_arg,
                }))
            }
            Ok(TypeOrExpr::Expr(value)) => {
                consumed += value.consumed();
                Ok(GenericsArg::Const(ConstGenericsArg {
                    src: &tokens[..consumed],
                    name,
                    value,
                }))
            }
            Ok(TypeOrExpr::Ambiguous {
                consumed: c,
                refs,
                path,
            }) => {
                consumed += c;
                Ok(GenericsArg::Ambiguous(AmbiguousGenericsArg {
                    src: &tokens[..consumed],
                    name,
                    refs,
                    path,
                }))
            }
        }
    }
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

impl<'a> RefGenericsArg<'a> {
    /// Consumes a single `ref` generics argument as a prefix of the input
    ///
    /// Because this function is only ever called as a helper to [`GenericsArg::consume`], this
    /// assumes that the first token will be the keyword `ref`, and will panic if this is not the
    /// case.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<RefGenericsArg<'a>, Option<usize>> {
        // We'll just assert that it *was* the `ref` keyword here.
        match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Ref) => (),
                _ => panic!("Expected keyword `ref`, found token kind {:?}", &t.kind),
            },
            res => panic!("Expected keyword `ref`, found {:?}", res),
        }

        let expr = Expr::consume(
            &tokens[1..],
            // We use `FnArgs` as the delimiter here because it (roughly) has the same properties
            // as function arguments, and that's all that we really need for the context of
            // possible errors generated here.
            ExprDelim::FnArgs,
            false,
            None,
            None,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + 1))?;
        let consumed = expr.consumed() + 1;

        Ok(RefGenericsArg {
            src: &tokens[..consumed],
            expr,
        })
    }
}
