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
/// Type = Path [ GenericArgs ] [ Refinements ]
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
/// NamedType = Ident [ GenericArgs ] { "." Ident [ GenericArgs ] } [ Refinements ] .
/// ```
/// which then shows where generics arguments are allowed.
///
/// All of the carefulness around path ambiguity applies here - as such, the standard parser for
/// this type cannot be used in cases where there might be ambiguity around the generic arguments.
///
/// [`Path`]: ../expr/struct.Path.html
#[derive(Debug)]
pub struct NamedType<'a> {
    pub(super) src: TokenSlice<'a>,
    path: Path<'a>,
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
        //   Path [ GenericArgs ] [ Refinements ]
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
    traits: Vec<Path<'a>>,
}

/// A collection of generics arguments
///
/// Individual generic arguments are represented by the [`GenericArg`] type, which exists solely as
/// a helper for this type. The BNF definition for the combination of these two types is:
/// ```text
/// GenericArgs = "<" GenericArg { "," GenericArg } [ "," ] ">"
/// GenericArg = [ Ident ":" ] Type
///            | [ Ident ":" ] BlockExpr
///            | "ref" Expr .
/// ```
///
/// Generics arguments are a large part of the ambiguity present in the sytnax. To keep complexity
/// localized, the primary parser for this type ([`try_consume`]) simply assumes no ambiguity - it
/// must be dealt with externally.
///
/// There is additionally ambiguity present *within* singular generics arguments themselves. This
/// is explained further in the documentation for [`GenericArg`].
///
/// [`GenericArg`]: enum.GenericArg.html
/// [`try_consume`]: #method.try_consume
#[derive(Debug)]
pub struct GenericArgs<'a> {
    pub(super) src: TokenSlice<'a>,
    args: Vec<GenericArg<'a>>,
    poisoned: bool,
}

/// A single generics argument
///
/// Before reading the documentation for this type, please first refer to the larger-picture
/// explanation given in the documentation for [`GenericArgs`].
///
/// This type is the singular generics argument, defined with the following BNF:
/// ```text
/// GenericArg = [ Ident ":" ] Type
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
/// [`GenericArgs`]: struct.GenericArgs.html
/// [`consume`]: #method.consume
#[derive(Debug)]
pub enum GenericArg<'a> {
    Type(TypeGenericArg<'a>),
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
pub struct ConstGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Option<Ident<'a>>,
    value: Expr<'a>,
}

#[derive(Debug)]
pub struct RefGenericArg<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Expr<'a>,
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

impl<'a> GenericArgs<'a> {
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
    ) -> Result<Option<GenericArgs<'a>>, Option<usize>> {
        make_getter!(macro_rules! get, tokens, ends_early, errors);

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

        loop {
            let arg_res = GenericArg::consume(
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

            let next = get!(
                consumed,
                Err(e) => Error::Expected {
                    kind: ExpectedKind::GenericArgDelim { prev_tokens: &tokens[consumed..] },
                    found: Source::TokenResult(Err(*e)),
                },
                None => Error::Expected {
                    kind: ExpectedKind::GenericArgDelim { prev_tokens: &tokens[consumed..] },
                    found: end_source!(containing_token),
                },
            );

            match &next.kind {
                // If we find ">", it's the end of the generic arguments.
                TokenKind::Punctuation(Punc::Gt) => {
                    consumed += 1;
                    break;
                }
                // If we find ",", we're expecting another generic arguments
                TokenKind::Punctuation(Punc::Comma) => {
                    consumed += 1;
                    continue;
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericArgDelim {
                            prev_tokens: &tokens[..consumed],
                        },
                        found: Source::TokenResult(Ok(next)),
                    });

                    return Err(None);
                }
            }
        }

        Ok(Some(GenericArgs {
            src: &tokens[..consumed],
            args,
            poisoned,
        }))
    }
}

impl<'a> GenericArg<'a> {
    /// Consumes a single generics argument as a prefix of the tokens given
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    ///
    /// This is primarily a helper function for [`GenericArgs::consume`]. For more information,
    /// refer to the documentation on either of these types.
    ///
    /// [`GenericArgs::consume`]: struct.GenericArgs.html#consume
    fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericArg<'a>, Option<usize>> {
        // Parsing a generics argument is somewhat complicated - this is due to the fact that two
        // of the variants share their first two tokens, but only optionally. Reference arguments
        // can be determined immediately becuase they start with "ref", so parsing for those is
        // delegated to `RefGenericArg::consume`

        make_getter!(macro_rules! get, tokens, ends_early, errors);

        let fst = get!(
            0,
            Err(e) => Error::Expected {
                kind: ExpectedKind::GenericArg { prev_tokens },
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::GenericArg { prev_tokens },
                found: end_source!(containing_token),
            },
        );

        let mut name = match &fst.kind {
            TokenKind::Keyword(Kwd::Ref) => {
                return RefGenericArg::consume(
                    tokens,
                    prev_tokens,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map_err(|_| None)
                .map(GenericArg::Ref);
            }
            TokenKind::Ident(name) => Some(Ident { src: fst, name }),
            _ => None,
        };

        let mut must_be_type = false;
        let mut consumed = 0;

        // We make this a loop so that we can break out of the block if it turns out that the name
        // we originally saw wasn't for one of the generics arguments.
        if name.is_some() {
            // Because we just parsed an identifier, we'll see if the generics argument starts with
            //   Ident ":"
            // If it doesn't, it's entirely possible that the starting identifier was instead as
            // part of a type parameter (not a block expression, though), but only if the token
            // following the identifier is one of the following set:
            //   { "," , ">" , "<"  }
            //     └┬┘   └┬┘   └┬┘
            //      └──┬──┘    Ident is the name of a type, followed by generic arguments
            //    Ident is *is* the type, followed by next generic arg / end of generic args list
            let expect_colon_token = get!(
                1,
                Err(e) => Error::Expected {
                    kind: ExpectedKind::GenericArg { prev_tokens },
                    found: Source::TokenResult(Err(*e)),
                },
                None => Error::Expected {
                    kind: ExpectedKind::GenericArg { prev_tokens },
                    found: end_source!(containing_token),
                },
            );

            match &expect_colon_token.kind {
                TokenKind::Punctuation(p) => match p {
                    // Per the comment above, we'll break out of this loop to parse the type
                    Punc::Comma | Punc::Gt | Punc::Lt => {
                        name = None;
                        must_be_type = true;
                    }
                    // If we found a colon, we'll mark that we actually used the identifier and
                    // colon, leaving `name` as it is.
                    Punc::Colon => consumed = 2,
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::GenericArgFollowIdent {
                                prev_tokens,
                                ident: fst,
                            },
                            found: Source::TokenResult(Ok(expect_colon_token)),
                        });

                        return Err(None);
                    }
                },
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericArgFollowIdent {
                            prev_tokens,
                            ident: fst,
                        },
                        found: Source::TokenResult(Ok(expect_colon_token)),
                    });

                    return Err(None);
                }
            }
        }

        // Past this point, we now consume what we have left as either a type or a block
        // expression. We'll attempt to parse it as an expression first, but only if the

        let next = get!(
            consumed,
            Err(e) => Error::Expected {
                kind: ExpectedKind::GenericArgAfterIdent {
                    prev_tokens,
                    name: name.map(|_| fst),
                },
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::GenericArgAfterIdent {
                    prev_tokens,
                    name: name.map(|_| fst),
                },
                found: end_source!(containing_token),
            },
        );

        let can_be_block_expr = match &next.kind {
            TokenKind::Tree {
                delim: Delim::Curlies,
                ..
            } => true,
            _ => false,
        };

        if can_be_block_expr && !must_be_type {
            let mut block_expr_errors = Vec::new();
            let block_expr = BlockExpr::parse(
                tokens.get(consumed),
                end_source!(containing_token),
                &mut block_expr_errors,
            )
            .map(Expr::Block)
            .ok();

            if let Some(value) = block_expr {
                if block_expr_errors.is_empty() {
                    consumed += value.consumed();
                    return Ok(GenericArg::Const(ConstGenericArg {
                        src: &tokens[..consumed],
                        name,
                        value,
                    }));
                }
            }

            // TODO: Currently, we might get *very* bad errors if the user provides some complex
            // constant argument here (i.e. large BlockExpr with an error partway through).
            // Realistically, this should be very rare, but it's an important case to deal with.
        }

        // Now, we'll try to parse it as a type
        let mut type_arg_errors = Vec::new();
        let type_arg = Type::consume(
            &tokens[consumed..],
            TypeContext::GenericArg {
                prev_tokens,
                name: name.map(|_| fst),
            },
            ends_early,
            containing_token,
            &mut type_arg_errors,
        )
        .ok();

        // If there weren't any errors from attempting to parse as a type - or if it couldn't be
        // anything else, we'll return the type.
        if let Some(type_arg) = type_arg {
            if !can_be_block_expr || must_be_type || type_arg_errors.is_empty() {
                consumed += type_arg.consumed();
                return Ok(GenericArg::Type(TypeGenericArg {
                    src: &tokens[..consumed],
                    name,
                    type_arg,
                }));
            }
        }

        // Now, we know that there's errors for both options. We'll generate an appropriate error
        errors.push(Error::Expected {
            kind: ExpectedKind::GenericArgAfterIdent {
                prev_tokens,
                name: name.map(|_| fst),
            },
            found: Source::TokenResult(Ok(next)),
        });

        Err(None)
    }
}

impl<'a> RefGenericArg<'a> {
    /// Consumes a single `ref` generics argument as a prefix of the input
    ///
    /// Because this function is only ever called as a helper to [`GenericArg::consume`], this
    /// assumes that the first token will be the keyword `ref`, and will panic if this is not the
    /// case.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<RefGenericArg<'a>, Option<usize>> {
        // We'll just assert that it *was* the `ref` keyword here.
        match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Ref) => (),
                _ => panic!("Expected keyword `ref`, found token kind {:?}", &t.kind),
            },
            res => panic!("Expected keyword `ref`, found {:?}", res),
        }

        /*
        // FIXME: This must be uncommented once expression parsing is implemented
        let expr = Expr::consume(___).map_err(|cs| cs.map(|c| c + 1))?;
        let consumed = expr.consumed() + 1;

        Ok(RefGenericArg {
            src: &tokens[..consumed],
            expr,
        })
        */

        todo!()
    }
}
