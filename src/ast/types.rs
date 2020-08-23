//! Type parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Types                                                                                          //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A single concrete type
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

/// A reference type
///
/// Reference types are denoted by a leading ampersand (`&`), any refinements on the reference
/// itself, and finally the type being referenced. This is described formally with the following
/// BNF definition:
/// ```text
/// RefType = "&" [ Refinements ] Type .
/// ```
#[derive(Debug, Clone)]
pub struct RefType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refinements: Option<Refinements<'a>>,
    pub ty: Box<Type<'a>>,
}

/// An indication that a type is strictly allowed or disallowed being mutable
///
/// This is mostly a syntactic helper construct to things like references, though it does have usage
/// on its own. A couple different use-cases might look like:
/// ```text
/// type Foo {
///     x: &mut Bar,
///     // ^^^^ reference with mutable access to value of type `Bar`
///     y: !mut Baz,
///     // ^^^^ indicates that `y` cannot be modified after construction
/// }
/// ```
///
/// Note that the types `&T` and `&!mut T` are equivalent; references only provide immutable access
/// by default.
///
/// And finally, it should be noted that while this sort of mutability prefix is *syntactically*
/// allowed before any type, it's semantically invalid before itself - i.e. `mut mut T` and other
/// forms like it are disallowed. Validating this is left until later.
#[derive(Debug, Clone)]
pub struct MutType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub has_not: Option<&'a Token<'a>>,
    pub ty: Box<Type<'a>>,
}

/// An array type, given by an element type and optionally the length
///
/// These are represented by the following BNF definition:
/// ```text
/// ArrayType = "[" Type [ ";" Expr ] "]" [ Refinements ] .
/// ```
///
/// Arrays are one of the few compound types that can be given refinements. This is essentially
/// it's crucial in certain cases to be able to specify the length of slices without directly
/// naming the type, e.g:
/// ```text
/// fn get<(ref r, T)>(vals: &|ref r| [T] |this.len() < idx|, idx: usize) -> &|ref r| T { ... }
/// ```
///
/// Obviously this is overly complicated - the user probably should have put the bounds on `vals`
/// in a proof statement instead - but this sort of specification about anonymous array types *is*
/// necessary, so it's here.
#[derive(Debug, Clone)]
pub struct ArrayType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub ty: Box<Type<'a>>,
    pub length: Option<Expr<'a>>,
    pub refinements: Option<Refinements<'a>>,

    /// Whether there were some kind of unexpected tokens inside the initial token tree containing
    /// this type
    pub poisoned: bool,
}

/// An anonymous struct type, given by each of the named fields
///
/// While the type represented here is, strictly speaking, anonymous, the binding in type
/// declarations can have the effect of making a named (i.e. non anonymous) type. That's a lot of
/// words to say that this type is only anonymous if it isn't the primary type in a type
/// declaration.
///
/// Anyways, `struct` types are represented by this combination of BNF definitions:
/// ```text
/// StructType = "{" [ StructField { "," StructField } [ "," ] ] "}" .
/// StructTypeField = [ Vis ] Ident ":" Type [ "=" Expr ] .
/// ```
#[derive(Debug, Clone)]
pub struct StructType<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<StructTypeField<'a>>,
    pub poisoned: bool,
}

/// A helper type for [`StructType`](struct.StructType.html)
///
/// This syntax element has the following BNF definition:
/// ```text
/// StructTypeField = [ Vis ] Ident ":" Type [ "=" Expr ] .
/// ```
#[derive(Debug, Clone)]
pub struct StructTypeField<'a> {
    pub(super) src: TokenSlice<'a>,
    pub vis: Option<Vis<'a>>,
    pub name: Ident<'a>,
    pub ty: Type<'a>,
    pub value: Option<Expr<'a>>,
}

/// An anonymous tuple type
///
/// Tuple types consist of an ordered list of types, each of which *may* have visibility
/// qualifiers, even though they are only valid in certain contexts.
///
/// The BNF definition here is split into two parts to reflect the structure of the code:
/// ```text
/// TupleType = "(" [ TupleTypeElement { "," TupleTypeElement } [ "," ] ] ")" .
/// TupleTypeElement = [ Vis ] Type .
/// ```
#[derive(Debug, Clone)]
pub struct TupleType<'a> {
    pub(super) src: &'a Token<'a>,
    pub elems: Vec<TupleTypeElement<'a>>,
}

/// A single tuple type element; a helper for [`TupleType`](struct.TupleType.html)
///
/// These satisfy the following BNF definition:
/// ```text
/// TupleTypeElement = [ Vis ] Type .
/// ```
#[derive(Debug, Clone)]
pub struct TupleTypeElement<'a> {
    pub(super) src: TokenSlice<'a>,
    pub vis: Option<Vis<'a>>,
    pub ty: Type<'a>,
}

/// An anonymous enum type
///
/// Enums are composed of a set of variants, each of which is given by (in rare circumstances) an
/// optional leading visibility qualifier, the name of the variant, and (optionally) a type for the
/// variant.
///
/// These are given by the following BNF definitions:
/// ```text
/// EnumType = "enum" "{" [ EnumVariant { "," EnumVariant } [ "," ] ] "}" .
/// EnumVariant = [ Vis ] Ident [ Type ] .
/// ```
///
/// Note that this description is not complete; the comma after a variant may be omitted when that
/// variant is assigned a struct type.
#[derive(Debug, Clone)]
pub struct EnumType<'a> {
    pub(super) src: TokenSlice<'a>,
    pub variants: Vec<EnumVariant<'a>>,
}

/// A single variant definition in an `enum` type; a helper for [`EnumType`](struct.EnumType.html)
///
/// These are given by the following BNF definition:
/// ```text
/// EnumVariant = [ Vis ] Ident [ Type ] .
/// ```
#[derive(Debug, Clone)]
pub struct EnumVariant<'a> {
    pub(super) src: TokenSlice<'a>,
    pub vis: Option<Vis<'a>>,
    pub name: Ident<'a>,
    pub ty: Option<Type<'a>>,
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
//     * RefRefinement                                                                            //
//     * InitRefinement                                                                           //
// * TypeBound                                                                                    //
// * GenericsArgs                                                                                 //
//   * GenericsArg                                                                                //
//     * TypeGenericsArg                                                                          //
//     * ConstGenericsArg                                                                         //
//     * RefGenericsArg                                                                           //
//     * AmbiguousGenericsArg                                                                     //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct Refinements<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refs: Vec<Refinement<'a>>,
}

#[derive(Debug, Clone)]
pub enum Refinement<'a> {
    Ref(RefRefinement<'a>),
    Init(InitRefinement<'a>),
    Expr(Expr<'a>),
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
///              | "<" GenericsArg ">" .
/// GenericsArg = [ Ident ":" ] Type
///             | [ Ident ":" ] BlockExpr
///             | "ref" Expr .
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
///             | [ Ident ":" ] BlockExpr
///             | "ref" Expr .
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
    pub value: TypeOrExpr<'a>,
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
        // First, we'll check for whether there's a "<". If there isn't, we'll just return.
        let leading_angle = match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Lt) => t,
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };

        // Otherwise, we'll expect the "inner" portion of generics arguments afterwards

        let (args, poisoned, cs) =
            GenericsArgs::consume_inner(&tokens[1..], ends_early, containing_token, errors)
                .map_err(p!(Some(c) => Some(1 + c)))?;

        let mut consumed = cs + 1;

        match tokens.get(consumed) {
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericsArgCloseAngleBracket {
                        args_tokens: &tokens[1..consumed],
                    },
                    found: Source::TokenResult(Err(*e)),
                });

                return Err(None);
            }
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericsArgCloseAngleBracket {
                        args_tokens: &tokens[1..consumed],
                    },
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Gt) => consumed += 1,
                TokenKind::Punctuation(Punc::Comma)
                    if GenericsArgs::can_be_single_arg(&args, consumed - 1)
                        && !might_be_generics_arg(&tokens[consumed..]) =>
                {
                    errors.push(Error::GenericsArgsNotEnclosed {
                        leading_angle,
                        arg: &tokens[1..consumed],
                        comma: t,
                    });

                    return Err(None);
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericsArgCloseAngleBracket {
                            args_tokens: &tokens[1..consumed],
                        },
                        found: Source::TokenResult(Ok(t)),
                    });

                    return Err(None);
                }
            },
        }

        Ok(Some(GenericsArgs {
            src: &tokens[..consumed],
            args,
            poisoned,
        }))
    }

    // Note: returns generics args, poisoned, consumed
    pub fn consume_inner(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(Vec<GenericsArg<'a>>, bool, usize), Option<usize>> {
        todo!()

        /*
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
        */
    }

    pub fn can_be_expr(args: &[GenericsArg]) -> bool {
        todo!()
    }

    /// Returns whether the list of generics arguments might instead constitute a single argument
    ///
    /// This function should be given the list of generics arguments supplied to it, alongside the
    /// number of tokens that were reported as consumed in order to create it
    pub fn can_be_single_arg(args: &[GenericsArg], consumed: usize) -> bool {
        todo!()
    }
}

/// Returns whether the given tokens might start with a generics argument
///
/// This is used for creating better error messages, and is not / should not be relied on for the
/// correctness of the parser.
///
/// As such, the current implementation just returns `true` - this will be changed in the future.
// TODO: See above note; this should be changed.
fn might_be_generics_arg(_tokens: TokenSlice) -> bool {
    true
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
        // A helper function to get the kind of the token at `idx`
        let kind = |idx: usize| Some(&tokens.get(idx)?.as_ref().ok()?.kind);

        let mut consumed = 0;

        // Some of generics args (i.e. consts and types) may be labeled with a name.
        let name = match (kind(0), kind(1)) {
            (Some(TokenKind::Ident(name)), Some(TokenKind::Punctuation(Punc::Colon))) => {
                consumed += 2;

                Some(Ident {
                    src: &tokens[0].as_ref().unwrap(),
                    name,
                })
            }
            _ => None,
        };

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let res = expect!((
            // Reference generics args can't be named
            TokenKind::Keyword(Kwd::Ref) if name.is_some() => {
                errors.push(Error::NamedReferenceGenericsArg {
                    name: name.unwrap(),
                    ref_kwd: &tokens[consumed].as_ref().unwrap(),
                });

                Err(None)
            },
            TokenKind::Keyword(Kwd::Ref) => {
                return RefGenericsArg::consume(tokens, ends_early, containing_token, errors)
                    .map_err(|_| None)
                    .map(GenericsArg::Ref);
            },
            _ => {
                TypeOrExpr::consume(&tokens[consumed..], prev_tokens, ends_early, containing_token, errors)
            },
            @else ExpectedKind::GenericsArg { prev_tokens },
        ));

        match res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(consumed + c)),
            Ok(type_or_expr) => {
                consumed += type_or_expr.consumed();

                Ok(match type_or_expr {
                    TypeOrExpr::Type(ty) => GenericsArg::Type(TypeGenericsArg {
                        src: &tokens[..consumed],
                        name,
                        type_arg: ty,
                    }),
                    TypeOrExpr::Expr(ex) => GenericsArg::Const(ConstGenericsArg {
                        src: &tokens[..consumed],
                        name,
                        value: ex,
                    }),
                    TypeOrExpr::Ambiguous { .. } => todo!(),
                })
            }
        }
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
        .map_err(p!(Some(c) => Some(c + 1)))?;
        let consumed = expr.consumed() + 1;

        Ok(RefGenericsArg {
            src: &tokens[..consumed],
            expr,
        })
    }
}
