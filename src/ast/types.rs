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
/// StructType = "{" [ StructTypeField { "," StructTypeField } [ "," ] ] "}" .
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
    pub poisoned: bool,
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
    pub poisoned: bool,
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

/// An abstraction over parsing functions - helper type for [`Type::parse_delimited`]
///
/// This is essentially just the minimum required abstraction to allow `parse_delimited` to take in
/// any of [`StructTypeField`], [`TupleTypeElement`], or [`EnumVariant`] as the individual piece repeated.
///
/// [`Type::parse_delimited`]: enum.Type.html#method.parse_delimited
/// [`StructTypeField`]: struct.StructTypeField.html
/// [`TupleTypeElement`]: struct.TupleTypeElement.html
/// [`EnumVariant`]: struct.EnumVariant.html
type InnerParserFn<'a, T> = fn(
    TokenSlice<'a>,
    TypeContext<'a>,
    bool,
    &'a Token<'a>,
    &mut Vec<Error<'a>>,
) -> Result<T, Option<usize>>;

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
            ($type:ident, $variant:ident $(, $ctx:expr)?) => {{
                $type::consume(tokens, $($ctx,)? ends_early, containing_token, errors).map(Type::$variant)
            }};
        }

        use TokenKind::{Ident, Keyword, Punctuation, Tree};

        make_expect!(tokens, 0, ends_early, containing_token, errors);
        expect!((
            Ident(_) => consume!(NamedType, Named),
            Punctuation(Punc::And) => consume!(RefType, Ref, ctx),
            Punctuation(Punc::Not) | Keyword(Kwd::Mut) => consume!(MutType, Mut, ctx),
            Tree { delim, inner, .. } => {
                let fst = tokens[0].as_ref().unwrap();
                match delim {
                    Delim::Squares => consume!(ArrayType, Array, ctx),
                    Delim::Curlies => StructType::parse(fst, inner, errors, ctx).map(Type::Struct)
                        .map_err(|()| Some(1)),
                    Delim::Parens => TupleType::parse(fst, inner, errors, ctx).map(Type::Tuple)
                        .map_err(|()| Some(1)),
                }
            },
            Keyword(Kwd::Enum) => consume!(EnumType, Enum, ctx),
            @else ExpectedKind::Type(ctx),
        ))
    }

    /// A helper function to extract the common elements of [struct], [tuple], and [enum] parsing
    ///
    /// [struct]: struct.StructType.html#method.parse
    /// [tuple]: struct.TupleType.html#method.parse
    /// [enum]: struct.EnumType.html#method.parse
    ///
    /// For some type `T`, this will parse the following BNF construction from the set of `inner`
    /// tokens:
    /// ```text
    /// [ T { "," T } [ "," ] ]
    /// ```
    /// Note that this is essentially the region between curly braces for [`StructType`]s (with
    /// `T = StructTypeField`) and the region between parentheses for [`TupleType`]s (with
    /// `T = TupleTypeElement`).
    ///
    /// There are a couple additions on top of this: Firstly, the comma between values of `T` may
    /// be omitted if `require_trailing_comma` returns true for that type. And secondly, the
    /// `expected_comma` field allows different error types to be produced, depending on the
    /// context in which this function is used.
    ///
    /// This function returns the list of inner values parsed, alongside a boolean that's true
    /// whenever there was some error in parsing that significantly poisoned the values produced.
    fn parse_delimited<T: Consumed>(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        consume_inner: InnerParserFn<'a, T>,
        ctx: TypeContext<'a>,
        require_trailing_comma: impl Fn(&T) -> bool,
        expected_comma: ExpectedKind<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(Vec<T>, bool), ()> {
        let ends_early = false;

        let mut consumed = 0;
        let mut poisoned = false;
        let mut values = Vec::new();

        while consumed < inner.len() {
            let res = consume_inner(&inner[consumed..], ctx, ends_early, src, errors);
            let mut requires_comma = true;

            match res {
                Ok(val) => {
                    consumed += val.consumed();
                    requires_comma = require_trailing_comma(&val);
                    values.push(val);
                }
                // If the very first field failed, we're probably not looking at what we thought we
                // were.
                Err(None) if consumed == 0 => return Err(()),
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
            }

            // After consuming the field, we'll expect a trailing comma (unless it's allowed to be
            // omitted). If we don't find a trailing comma, but we've already encountered previous
            // errors, we'll just exit without raising an additional error for this one.
            match inner.get(consumed) {
                None => break,
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ if !requires_comma => (),
                    _ => {
                        errors.push(Error::Expected {
                            kind: expected_comma,
                            found: Source::TokenResult(Ok(t)),
                        });

                        poisoned = true;
                        break;
                    }
                },
                _ if poisoned => break,
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: expected_comma,
                        found: Source::TokenResult(Err(*e)),
                    });

                    poisoned = true;
                    break;
                }
            }
        }

        Ok((values, poisoned))
    }

    /// Returns whether the given token can start a type
    fn is_starting_token(token_res: &Result<Token, token_tree::Error>) -> bool {
        match token_res {
            Ok(token) => match &token.kind {
                // NamedType
                TokenKind::Ident(_)
                // RefType
                | TokenKind::Punctuation(Punc::And)
                // MutType
                | TokenKind::Punctuation(Punc::Not) | TokenKind::Keyword(Kwd::Mut)
                // ArrayType
                | TokenKind::Tree { delim: Delim::Squares, .. }
                // StructType
                | TokenKind::Tree { delim: Delim::Curlies, .. }
                // TupleType
                | TokenKind::Tree { delim: Delim::Parens, .. }
                // EnumType
                | TokenKind::Keyword(Kwd::Enum) => true,
                _ => false,
            },
            Err(e) => match e {
                token_tree::Error::UnclosedDelim(_, _) => true,
                _ => false,
            },
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
    /// Consumes a reference type as a prefix of the given tokens
    ///
    /// This function expects the starting token to be an ampersand (`&`) and will panic if this is
    /// not the case.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<RefType<'a>, Option<usize>> {
        // We're expecting '&' at the start:
        assert_token!(
            tokens.first() => "ampersand (`&`)",
            Ok(t) && TokenKind::Punctuation(Punc::And) => (),
        );

        let mut consumed = 1;

        let refinements =
            Refinements::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += refinements.consumed();

        let ty = Type::consume(
            &tokens[consumed..],
            ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        Ok(RefType {
            src: &tokens[..consumed],
            refinements,
            ty: Box::new(ty),
        })
    }
}

impl<'a> MutType<'a> {
    /// Consumes a "mut" type as a prefix of the given tokens
    ///
    /// This function will assume that the starting token will either be an exclamation mark (`!`)
    /// or the keyword `mut`. If neither of these are true, it will panic.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MutType<'a>, Option<usize>> {
        let has_not = assert_token!(
            tokens.first() => "not (`!`) or keyword `mut`",
            Ok(t) && TokenKind::Keyword(Kwd::Mut) => None,
                     TokenKind::Punctuation(Punc::Not) => Some(t),
        );

        let mut consumed = 1;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        if has_not.is_some() {
            expect!((
                TokenKind::Keyword(Kwd::Mut) => consumed += 1,
                @else ExpectedKind::MutTypeKeyword(ctx),
            ));
        }

        Type::consume(
            &tokens[consumed..],
            ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))
        .map(|ty| MutType {
            src: &tokens[..consumed],
            has_not,
            ty: Box::new(ty),
        })
    }
}

impl<'a> ArrayType<'a> {
    /// Consumes an array type as a prefix of the given tokens
    ///
    /// This function will assume that the first token will be a sqare-bracket delimited token
    /// tree, and will panic if that is not the case.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ArrayType<'a>, Option<usize>> {
        let (fst_token, inner, inner_ends_early) = assert_token!(
            tokens.first() => "square-bracket token tree",
            Ok(t) && TokenKind::Tree { delim: Delim::Squares, inner, .. } => (t, inner, false),
        );

        // For just the square-brackets portion, we're expecting something of the form:
        //   "[" Type [ ";" Expr ] "]"
        // So we can plainly do the following pieces:
        let ty = Type::consume(inner, ctx, inner_ends_early, Some(fst_token), errors)
            .map_err(|_| Some(1))?;

        let mut length = None;
        let mut poisoned = false;

        // After the type, we're expecting either ";" or the end
        if inner.len() > ty.consumed() {
            make_expect!(
                inner,
                ty.consumed(),
                inner_ends_early,
                Some(fst_token),
                errors
            );
            expect!((
                TokenKind::Punctuation(Punc::Semi) => (),
                @else ExpectedKind::ArrayTypeSemi(ctx),
            ));

            let mut consumed = ty.consumed() + 1;
            length = Expr::consume(
                &inner[consumed..],
                ExprDelim::Nothing,
                Restrictions::default(),
                inner_ends_early,
                Some(fst_token),
                errors,
            )
            .ok();

            consumed += length.consumed();

            // If we critically failed to parse the expression, that error should have been fairly
            // contained, so we'll just mark the internal portion of the type as poisoned and not
            // bother with bubbling the *returned* error indicator
            if length.is_none() {
                poisoned = true;
            }

            // And after the expression (assuming parsing was successful) we'll expect the end of
            // the internal bits
            if inner.len() > consumed && !poisoned {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ArrayTypeInnerEnd,
                    found: Source::from(&inner[consumed]),
                });

                // Like above, we'll just continue if there was an error here
                poisoned = true;
            }
        }

        // The final thing we need to do is to check for refinements in the outer token tree!
        let refinements =
            Refinements::try_consume(&tokens[1..], ends_early, containing_token, errors)
                .map_err(p!(Some(c) => Some(c + 1)))?;

        let consumed = 1 + refinements.consumed();

        Ok(ArrayType {
            src: &tokens[..consumed],
            ty: Box::new(ty),
            length,
            refinements,
            poisoned,
        })
    }
}

impl<'a> StructType<'a> {
    /// Parses an anonymous struct type from the given inner tokens of a curly brace enclosed token
    /// tree
    ///
    /// This function *does not* check that the token it is given as the source is actually a
    /// curly-brace delimited token tree; this must be ensured by the caller as it is assumed to be
    /// true elsewhere.
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
        ctx: TypeContext<'a>,
    ) -> Result<StructType<'a>, ()> {
        Type::parse_delimited(
            src,
            inner,
            StructTypeField::consume,
            ctx,
            StructTypeField::requires_trailing_comma,
            ExpectedKind::StructTypeFieldDelim,
            errors,
        )
        .map(|(fields, poisoned)| StructType {
            src,
            fields,
            poisoned,
        })
    }
}

impl<'a> StructTypeField<'a> {
    /// Consumes a single field of a struct type as a prefix of the given tokens
    ///
    /// This function makes no assumptions about the input
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: &'a Token<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<StructTypeField<'a>, Option<usize>> {
        // Struct type fields aren't too complicated. They're essentially defined by the following
        // BNF:
        //   StructTypeField = [ Vis ] Ident ":" Type [ "=" Expr ] .
        let vis = Vis::try_consume(tokens);

        let mut consumed = vis.consumed();
        make_expect!(tokens, consumed, ends_early, Some(containing_token), errors);

        let ident_ctx = IdentContext::StructTypeField;
        let name = Ident::parse(
            tokens.get(consumed),
            ident_ctx,
            end_source!(Some(containing_token)),
            errors,
        )
        .map_err(|()| None)?;

        consumed += 1;

        expect!((
            TokenKind::Punctuation(Punc::Colon) => consumed += 1,
            @else ExpectedKind::StructTypeFieldColon,
        ));

        // If we get Err(Some(_)), we'll keep trying tp consume tokens so that *we* can return
        // Err(Some(_)) with better accuracy to the caller
        let ty_res = Type::consume(
            &tokens[consumed..],
            ctx,
            ends_early,
            Some(containing_token),
            errors,
        );
        let ty: Option<Type> = match ty_res {
            Ok(t) => {
                consumed += t.consumed();
                Some(t)
            }
            Err(Some(c)) => {
                consumed += c;
                None
            }
            Err(None) => return Err(None),
        };

        let mut value: Option<Expr> = None;

        // And now, if we find '=' after the type, we'll try to parse an expression
        if let Some(TokenKind::Punctuation(Punc::Eq)) = kind!(tokens)(consumed) {
            consumed += 1;
            let expr = Expr::consume(
                &tokens[consumed..],
                // While not strictly speaking a struct expression, this is pretty close, so we'll
                // use it.
                ExprDelim::StructFields,
                Restrictions::default(),
                ends_early,
                Some(containing_token),
                errors,
            )
            .map_err(p!(Some(c) => Some(consumed + c)))?;

            consumed += expr.consumed();
            value = Some(expr);
        }

        match ty {
            // If we left the type as 'None' before, we failed to parse. We'll return
            // `Err(Some(_))`
            None => Err(Some(consumed)),
            // Otherwise, everything was fine:
            Some(ty) => Ok(StructTypeField {
                src: &tokens[..consumed],
                vis,
                name,
                ty,
                value,
            }),
        }
    }

    /// Returns whether the struct field is required to have a trailing comma. This is false only
    /// for fields where the type is an anonymous struct.
    fn requires_trailing_comma(&self) -> bool {
        match self.ty {
            Type::Struct(_) => false,
            _ => true,
        }
    }
}

impl<'a> TupleType<'a> {
    /// Parses a tuple type from the given inner tokens of a parentheses-enclosed token tree
    ///
    /// This function *does not* check that the token it is given as the source is actually a
    /// parenthetical token tree; this must be ensured by the caller as it is assumed to be true
    /// elsewhere.
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
        ctx: TypeContext<'a>,
    ) -> Result<TupleType<'a>, ()> {
        Type::parse_delimited(
            src,
            inner,
            TupleTypeElement::consume,
            ctx,
            |_| true,
            ExpectedKind::TupleTypeElemDelim,
            errors,
        )
        .map(|(elems, poisoned)| TupleType {
            src,
            elems,
            poisoned,
        })
    }
}

impl<'a> TupleTypeElement<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: &'a Token<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TupleTypeElement<'a>, Option<usize>> {
        // Tuple type elements are pretty simple. They're defined by the following BNF:
        //   [ Vis ] Type
        // See!
        //
        // We'll just breeze through this - not too many comments should be necessary
        let vis = Vis::try_consume(tokens);

        let mut consumed = vis.consumed();

        let ty = Type::consume(
            &tokens[consumed..],
            ctx,
            ends_early,
            Some(containing_token),
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += ty.consumed();

        Ok(TupleTypeElement {
            src: &tokens[..consumed],
            vis,
            ty,
        })
    }
}

impl<'a> EnumType<'a> {
    /// Consumes an `enum` type as a prefix of the given tokens
    ///
    /// This function will assume that the first token is the keyword `enum`, and will panic if
    /// this is not the case.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<EnumType<'a>, Option<usize>> {
        assert_token!(
            tokens.first() => "keyword `enum`",
            Ok(t) && TokenKind::Keyword(Kwd::Enum) => (),
        );

        match tokens.get(1) {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => Type::parse_delimited(
                    t,
                    inner,
                    EnumVariant::consume,
                    ctx,
                    EnumVariant::requires_trailing_comma,
                    ExpectedKind::EnumTypeVariantDelim,
                    errors,
                )
                .map_err(|()| None)
                .map(|(variants, poisoned)| EnumType {
                    src: &tokens[..2],
                    variants,
                    poisoned,
                }),
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::EnumTypeCurlies,
                        found: Source::TokenResult(Ok(t)),
                    });

                    Err(None)
                }
            },
            Some(Err(token_tree::Error::UnclosedDelim(Delim::Curlies, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::EnumTypeCurlies,
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }
            None => {
                if ends_early {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::EnumTypeCurlies,
                        found: end_source!(containing_token),
                    });
                }

                Err(None)
            }
        }
    }
}

impl<'a> EnumVariant<'a> {
    /// Consumes a single enum variant as a prefix of the given tokens
    ///
    /// This function makes no assumptions about the inputs.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: &'a Token<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<EnumVariant<'a>, Option<usize>> {
        // The BNF for enum variants makes the rest of this function clear:
        //   EnumVariant = [ Vis ] Ident [ Type ] .

        let vis = Vis::try_consume(tokens);
        let mut consumed = vis.consumed();

        let ident_ctx = IdentContext::EnumVariant;
        let name = Ident::parse(
            tokens.get(consumed),
            ident_ctx,
            end_source!(Some(containing_token)),
            errors,
        )
        .map_err(|()| None)?;

        consumed += 1;

        let mut ty = None;

        // If there's a token immediately after the name that
        if let Some(next) = tokens.get(consumed) {
            if Type::is_starting_token(next) {
                let t = Type::consume(
                    &tokens[consumed..],
                    ctx,
                    ends_early,
                    Some(containing_token),
                    errors,
                )
                .map_err(p!(Some(c) => Some(c + consumed)))?;

                consumed += t.consumed();
                ty = Some(t);
            }
        }

        Ok(EnumVariant {
            src: &tokens[..consumed],
            vis,
            name,
            ty,
        })
    }

    /// Returns whether the enum variant is required to have a trailing comma. This is false only
    /// for variants with a type as an anonymous struct
    fn requires_trailing_comma(&self) -> bool {
        match self.ty {
            Some(Type::Struct(_)) => false,
            _ => true,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper bits                                                                                    //
// * StructTypeField                                                                              //
// * Refinements                                                                                  //
//   * Refinement                                                                                 //
//     * RefRefinement                                                                            //
//     * InitRefinement                                                                           //
// * GenericsArgs                                                                                 //
//   * GenericsArg                                                                                //
//     * TypeGenericsArg                                                                          //
//     * ConstGenericsArg                                                                         //
//     * RefGenericsArg                                                                           //
//     * AmbiguousGenericsArg                                                                     //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A collection of refinements as part of a type
///
/// There are many types of refinements - these are broadly defined by the following pair of BNF
/// constructions:
/// ```text
/// Refinements = "|" Refinement { "," Refinement } [ "," ] "|" .
/// Refinement = "ref" Expr
///            | [ "!" | "?" ] "init"
///            | Expr .
/// ```
#[derive(Debug, Clone)]
pub struct Refinements<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refs: Vec<Refinement<'a>>,
    pub poisoned: bool,
}

/// A single refinement; a helper type for [`Refinements`](struct.Refinements.html)
#[derive(Debug, Clone)]
pub enum Refinement<'a> {
    Ref(RefRefinement<'a>),
    Init(InitRefinement<'a>),
    Expr(Expr<'a>),
}

/// A reference refinement, indicating the value that a reference borrows
///
/// This is defined by the following BNF construction:
/// ```text
/// RefRefinement = "ref" Expr .
/// ```
#[derive(Debug, Clone)]
pub struct RefRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Expr<'a>,
}

/// A refinement indicating the initialization status of a value
///
/// This is defined by the following BNF construction:
/// ```text
/// InitRefinement = [ "!" | "?" ] "init" .
/// ```
/// Note that, in line with the construction above, either one of `not` or `maybe` may be true, but
/// never both. For clarification, `maybe` gives the token source of the question mark, if it is
/// there.
#[derive(Debug, Clone)]
pub struct InitRefinement<'a> {
    pub(super) src: TokenSlice<'a>,
    pub not: Option<&'a Token<'a>>,
    pub maybe: Option<&'a Token<'a>>,
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
///             | [ Ident ":" ] Expr
///             | "ref" Expr .
/// ```
/// This definition permits some thorough ambiguity between types an expressions. That ambiguity
/// isn't handled here, but with the [`type_or_expr`] module.
///
/// Each of the variants shown above directly correspond the variants of this enum, in the same
/// order, with `Ambiguous` providing a catch-all for cases where it cannot be determined whether
/// the generics argument is a type or an expression.
///
/// [`GenericsArgs`]: struct.GenericsArgs.html
/// [`type_or_expr`]: ../type_or_expr/index.html
#[derive(Debug, Clone)]
pub enum GenericsArg<'a> {
    Type(TypeGenericsArg<'a>),
    Const(ConstGenericsArg<'a>),
    Ref(RefGenericsArg<'a>),
    Ambiguous(AmbiguousGenericsArg<'a>),
}

/// A typed generics argument
///
/// These are represented by the following BNF:
/// ```text
/// TypeGenericsArg = [ Ident ":" ] Type .
/// ```
#[derive(Debug, Clone)]
pub struct TypeGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub type_arg: Type<'a>,
}

/// A constant generics argument, using a compile-time-evaluated expression
///
/// These are represented by the following BNF:
/// ```text
/// ConstGenericsArg = [ Ident ":" ] Expr .
/// ```
#[derive(Debug, Clone)]
pub struct ConstGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub value: Expr<'a>,
}

/// A "reference" generics argument
///
/// These are represented by the following BNF:
/// ```text
/// RefGenericsArg = "ref" Expr .
/// ```
#[derive(Debug, Clone)]
pub struct RefGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Expr<'a>,
}

/// A generics argument that may either be a [type] or [const]
///
/// [type]: TypeGenericsArg.html
/// [const]: ConstGenericsArg.html
#[derive(Debug, Clone)]
pub struct AmbiguousGenericsArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub value: TypeOrExpr<'a>,
}

impl<'a> Refinements<'a> {
    /// Attempts to consume refinements as part of a type
    ///
    /// Please note that this function does not handle any ambiguity that may be present when types
    /// are being parsed inside an expression context.
    pub fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<Refinements<'a>>, Option<usize>> {
        match kind!(tokens)(0) {
            Some(TokenKind::Punctuation(Punc::Or)) => (),
            _ => return Ok(None),
        }

        // After the initial "|", we'll progressively parse individual refinements
        let mut consumed = 0;
        let mut poisoned = false;
        let mut refs = Vec::new();

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        // NOTE: When this loop breaks, we have set `consumed` without the trailing pipe, even
        // though we *have* asserted that it's there. It makes the loop slightly cleaner
        loop {
            // We don't allow empty refinements
            if consumed != 0 {
                if let Some(TokenKind::Punctuation(Punc::Or)) = kind!(tokens)(consumed) {
                    break;
                }
            }

            let res =
                Refinement::consume(&tokens[consumed..], ends_early, containing_token, errors);
            match res {
                Ok(re) => {
                    consumed += re.consumed();
                    refs.push(re);
                }
                Err(Some(c)) => {
                    consumed += c;
                    poisoned = true;
                }
                Err(None) => return Err(None),
            }

            expect!((
                TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                TokenKind::Punctuation(Punc::Or) => break,
                @else ExpectedKind::RefinementDelim,
            ));
        }

        Ok(Some(Refinements {
            src: &tokens[..consumed + 1],
            refs,
            poisoned,
        }))
    }
}

impl<'a> Refinement<'a> {
    /// Consumes a single refinement as a prefix of the tokens
    ///
    /// This function makes no assumptions about its input.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Refinement<'a>, Option<usize>> {
        // There are a few types of refinements available:
        //   Refinement = "ref" Expr
        //              | [ "!" | "?" ] "init"
        //              | Expr .
        //
        // Because there's a couple optional pieces for `InitRefinement`s, we'll define a helper
        // closure to factor out the common pieces.

        let make_init = |has_not, has_maybe| {
            let not = match has_not {
                true => Some(tokens[0].as_ref().unwrap()),
                false => None,
            };

            let maybe = match has_maybe {
                true => Some(tokens[0].as_ref().unwrap()),
                false => None,
            };

            let src = match has_not || has_maybe {
                true => &tokens[..2],
                false => &tokens[..1],
            };

            Ok(Refinement::Init(InitRefinement { src, not, maybe }))
        };

        match (kind!(tokens)(0), kind!(tokens)(1)) {
            // Expecting an "init" refinement, with leading "!"
            (Some(TokenKind::Punctuation(Punc::Not)), Some(TokenKind::Keyword(Kwd::Init))) => {
                make_init(true, false)
            }
            // Expecting an "init" refinement, with leading "?"
            (Some(TokenKind::Punctuation(Punc::Question)), Some(TokenKind::Keyword(Kwd::Init))) => {
                make_init(false, true)
            }
            // Expecting an "init" refinement without any leading modifiers
            (Some(TokenKind::Keyword(Kwd::Init)), _) => make_init(false, false),
            // Expecting a "ref" refinement - *with* a leading "mut"
            (Some(TokenKind::Keyword(Kwd::Ref)), _) => Expr::consume(
                &tokens[1..],
                ExprDelim::Comma,
                Restrictions::default().no_pipe(),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(p!(Some(c) => Some(c + 1)))
            .map(|expr| {
                let src = &tokens[..expr.consumed() + 1];
                Refinement::Ref(RefRefinement { src, expr })
            }),
            // Otherwise, we'll simply expect an expression as our
            _ => Expr::consume(
                tokens,
                ExprDelim::Comma,
                Restrictions::default().no_pipe(),
                ends_early,
                containing_token,
                errors,
            )
            .map(Refinement::Expr),
        }
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
                    if GenericsArgs::can_be_single_arg(&args)
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

    /// Consumes the "inner" portion of generics arguments, returning the arguments, whether they
    /// were poisoned, and the total number of tokens consumed.
    ///
    /// This function makes no expectations of the input.
    pub fn consume_inner(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(Vec<GenericsArg<'a>>, bool, usize), Option<usize>> {
        // This function isn't completely trivial (and a lot of it is taken up by various kinds of
        // error handling), so we'll go through the general structure here.
        //
        // Background: There's essentially two ways that we can have generics arguments. These are
        // either a single generics argument OR a parenthetically-enclosed *list* of generics
        // arguments.
        //
        // So: if the first token is a parenthetical token tree, we'll parse multiple generics
        // arguments inside. Otherwise, we'll just assume that there's a single generics argument
        // there to parse.
        let mut do_single = || {
            GenericsArg::consume(tokens, &[], ends_early, containing_token, errors).map(|arg| {
                let consumed = arg.consumed();
                (vec![arg], false, consumed)
            })
        };

        let (src, inner, inner_ends_early) = match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Tree {
                    delim: Delim::Parens,
                    inner,
                    ..
                } => (t, inner, false),
                _ => return do_single(),
            },
            _ => return do_single(),
        };

        // So we only get to this point if we're parsing the internal portion of the parenthetical
        // block. We *also* want to handle a particular case if there aren't any tokens in the
        // list.
        //
        // If we have generics that look something like: Foo<()>, it's a *single* argument, either
        // a type or an expression.
        if inner.is_empty() {
            let arg = GenericsArg::Ambiguous(AmbiguousGenericsArg {
                src: &tokens[..1],
                name: None,
                value: TypeOrExpr::Tuple(TupleTypeOrExpr {
                    src,
                    elements: vec![],
                    poisoned: false,
                }),
            });

            return Ok((vec![arg], false, 1));
        }

        // With that out of the way, we'll loop through the inner tokens, consuming all of the
        // generics arguments available.

        let mut consumed = 0;
        let mut args = Vec::new();
        let mut poisoned = false;

        while consumed < inner.len() {
            let res = GenericsArg::consume(
                &inner[consumed..],
                &inner[..consumed],
                inner_ends_early,
                Some(src),
                errors,
            );

            match res {
                Ok(arg) => {
                    consumed += arg.consumed();
                    args.push(arg);
                }

                // If the very first argument failed, we might not be looking at what we though, so
                // we'll just return.
                Err(None) if consumed == 0 => return Err(None),
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
            }

            // After consuming the argument, we'll expect a trailing comma (unless it's allowed to
            // be omitted). If we don't find a trailing comma, but we've already encountered
            // previous errors, we'll just exit without raising an additional error for this one.
            match inner.get(consumed) {
                None => break,
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::GenericsArgDelim,
                            found: Source::TokenResult(Ok(t)),
                        });

                        poisoned = true;
                        break;
                    }
                },
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericsArgDelim,
                        found: Source::TokenResult(Err(*e)),
                    });

                    poisoned = true;
                    break;
                }
            }
        }

        // We only actually consumed a single token, because we were working within the single
        // token tree
        Ok((args, poisoned, 1))
    }

    /// Returns whether the list of generics arguments can form an expression
    ///
    /// What's important to note here is that implied in the list is that the arguments are inside
    /// a parethentical token tree, in a list delimited by commas.
    pub fn can_be_expr(args: &[GenericsArg]) -> bool {
        args.iter().all(|arg| match arg {
            // An individual argument can be part of a larger expression only if:
            //   1. It is either Const or Ambiguous
            //   2. It has no name
            GenericsArg::Const(ConstGenericsArg { name, .. })
            | GenericsArg::Ambiguous(AmbiguousGenericsArg { name, .. }) => name.is_none(),
            _ => false,
        })
    }

    /// Returns whether the list of generics arguments might instead constitute a single argument
    ///
    /// This function should be given the list of generics arguments supplied to it, alongside the
    /// number of tokens that were reported as consumed in order to create it
    pub fn can_be_single_arg(args: &[GenericsArg]) -> bool {
        if args.len() == 1 {
            return true;
        }

        enum Kind {
            Type,
            Expr,
        }

        let mut kind = None;

        for arg in args {
            match arg {
                // If we have multiple arguments and one of them is a reference argument, there's
                // no way that these are all either a type or an expression
                GenericsArg::Ref(_) => return false,
                // If we find a conflict between the argument types we've already seen and the one
                // we're currently looking at, these definitely can't be a single argument.
                //
                // We also require that none of the arguments have names, because otherwise they
                // couldn't be a single expression or type.
                GenericsArg::Type(TypeGenericsArg { name, .. }) => match kind {
                    Some(Kind::Expr) => return false,
                    _ if name.is_some() => return false,
                    _ => kind = Some(Kind::Type),
                },
                GenericsArg::Const(ConstGenericsArg { name, .. }) => match kind {
                    Some(Kind::Type) => return false,
                    _ if name.is_some() => return false,
                    _ => kind = Some(Kind::Expr),
                },
                // Ambiguous generics arguments are roughly the same, though they can't conflict
                // with `kind`
                GenericsArg::Ambiguous(AmbiguousGenericsArg { name, .. }) => {
                    if name.is_some() {
                        return false;
                    }
                }
            }
        }

        true
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
        let mut consumed = 0;

        // Some of generics args (i.e. consts and types) may be labeled with a name.
        let name = match (kind!(tokens)(0), kind!(tokens)(1)) {
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
            _ => TypeOrExpr::consume(
                &tokens[consumed..],
                prev_tokens,
                Restrictions::default().no_angle_bracket(),
                ends_early,
                containing_token,
                errors
            ),
            @else ExpectedKind::GenericsArg { prev_tokens },
        ));

        match res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(consumed + c)),
            Ok(type_or_expr) => {
                consumed += type_or_expr.consumed();

                Ok(match type_or_expr {
                    MaybeTypeOrExpr::Type(ty) => GenericsArg::Type(TypeGenericsArg {
                        src: &tokens[..consumed],
                        name,
                        type_arg: ty,
                    }),
                    MaybeTypeOrExpr::Expr(ex) => GenericsArg::Const(ConstGenericsArg {
                        src: &tokens[..consumed],
                        name,
                        value: ex,
                    }),
                    MaybeTypeOrExpr::Ambiguous(value) => {
                        GenericsArg::Ambiguous(AmbiguousGenericsArg {
                            src: &tokens[..consumed],
                            name,
                            value,
                        })
                    }
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
        assert_token!(
            tokens.first() => "keyword `ref`",
            Ok(t) && TokenKind::Keyword(Kwd::Ref) => (),
        );

        let expr = Expr::consume(
            &tokens[1..],
            // We use `FnArgs` as the delimiter here because it (roughly) has the same properties
            // as function arguments, and that's all that we really need for the context of
            // possible errors generated here.
            ExprDelim::FnArgs,
            Restrictions::default().no_angle_bracket(),
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
