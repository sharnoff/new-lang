use super::*;

/// A collection of generics parameters, given as part of a type or function declarations
///
/// This is provided separately (instead of just [`Vec<GenericsParam>`]) so that we can track and
/// refer to the source for the set of parameters as a whole group.
///
/// Briefly, the BNF for generics parameters is:
/// ```text
/// GenericsParams = "<" GenericsParam { "," GenericsParam } [ "," ] ">" .
/// ```
/// For more information, see [`GenericsParam`].
///
/// [`Vec<GenericsParam>`]: struct.GenericsParam.html
/// [`GenericsParam`]: struct.GenericsParam.html
#[derive(Debug, Clone)]
pub struct GenericsParams<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub params: Vec<GenericsParam<'a>>,
    pub poisoned: bool,
}

/// A single generic parameter, given as part of a type or function declaration
///
/// The BNF can be defined by either of these equivalent definitions:
/// ```text
/// GenericsParam = Ident [ "::" TypeBound ] [ "=" Type ]
///              | "const" Ident ":" Type [ "=" Expr ] .
///              | "ref" Ident .
/// "          " = GenericTypeParam
///              | GenericConstParam
///              | GenericRefParam
/// ```
/// These variants are represented by [`GenericTypeParam`], [`GenericConstParam`], and
/// [`GenericRefParam`], respectively, as shown with the second definition. For more information,
/// refer to the documentation for those types individually.
///
/// [`GenericTypeParam`]: struct.GenericTypeParam.html
/// [`GenericConstParam`]: struct.GenericConstParam.html
/// [`GenericRefParam`]: struct.GenericRefParam.html
#[derive(Debug, Clone)]
pub enum GenericsParam<'a> {
    Type(GenericTypeParam<'a>),
    Const(GenericConstParam<'a>),
    Ref(GenericRefParam<'a>),
}

/// A generic type parameter, given as part of a type or function declaration
///
/// Type parameters are the most common generics parameter. There are however, two others - to see
/// the full set, refer to [`GenericsParam`].
///
/// The BNF definition for a single generic type parameter is:
/// ```text
/// GenericTypeParam = Ident [ "::" TypeBound ] [ "=" Type ] .
/// ```
/// All type parameters are given by their name, possibly followed by a [type bound], which
/// restricts type arguments to those that implement a set of traits. Additionally, default values
/// for these types can be given by the trailing [`"=" Type`].
///
/// [`GenericsParam`]: struct.GenericsParam.html
/// [type bound]: ../struct.TypeBound.html
/// [`"=" Type`]: ../../types/enum.Type.html
#[derive(Debug, Clone)]
pub struct GenericTypeParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub bound: Option<TypeBound<'a>>,
    pub default_type: Option<Type<'a>>,
}

/// A generic constant parameter, given as part of a type or function declaration
///
/// `const` parameters are one of three generics parameters; for the full set, see
/// [`GenericsParam`].
///
/// These are defined by the folowing BNF:
/// ```text
/// GenericConstParam = "const" Field .
/// ```
/// Note that [`Field`] is primarily a helper type, and is defined to be:
/// ```text
/// Field = Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ] .
/// ```
/// This allows `const` parameters to be generic in type as well as in value.
///
/// [`GenericsParam`]: enum.GenericsParam.html
/// [`Field`]: ../struct.Field.html
#[derive(Debug, Clone)]
pub struct GenericConstParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub field: Field<'a>,
}

/// A generic "ref" parameter, given as part of a type or function declaration
///
/// "ref" parameters allow for making types or functions generic on the lifetime of a referenced
/// value. They are one of three types of generics parameters; for the full set, see
/// [`GenericsParams`].
///
/// These are defined by the following BNF construction:
/// ```text
/// GenericRefParam = "ref" Ident .
/// ```
///
/// [`GenericsParam`]: enum.GenericsParam.html
#[derive(Debug, Clone)]
pub struct GenericRefParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub ref_name: Ident<'a>,
}

impl<'a> GenericsParams<'a> {
    /// Attempts to consume generics parameters as a prefix of the given tokens, failing with
    /// `Ok(None)` if the tokens clearly do not start with generics parameters.
    ///
    /// More specifically, this returns `Ok(None)` if the first element of the tokens is not a
    /// less-than token (`"<"`). Otherwise, this will fully attempt to parse, generating all
    /// relevant errors and returning `Err` upon complete failure.
    ///
    /// This function will produce an error and return `Err(None)` if the first token is either a
    /// tokenizer error or does not exist. The latter of these is an adjustment that ideally
    /// wouldn't be the case, but allows better error messages if this function takes that
    /// responsibility.
    pub(super) fn try_consume(
        tokens: TokenSlice<'a>,
        ctx: GenericsParamsContext<'a>,
        allow_start_err: impl Fn(&token_tree::Error) -> bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<GenericsParams<'a>>, Option<usize>> {
        // First, we'll check for whether there's a "<". If there isn't, we'll just return.
        match tokens.first() {
            Some(Ok(token)) => match &token.kind {
                TokenKind::Punctuation(Punc::Gt) => (),
                _ => return Ok(None),
            },
            Some(Err(e)) => {
                if allow_start_err(e) {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericsParams(ctx),
                        found: Source::TokenResult(Err(*e)),
                    });
                }

                return Err(None);
            }
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericsParams(ctx),
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
        }

        let mut consumed = 1;
        let mut poisoned = false;
        let mut params = Vec::new();

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        loop {
            let param_res = GenericsParam::consume(
                &tokens[consumed..],
                ctx,
                &tokens[..consumed],
                ends_early,
                containing_token,
                errors,
            );
            match param_res {
                Ok(p) => {
                    consumed += p.consumed();
                    params.push(p);
                }
                Err(None) => return Err(None),
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
            }

            expect!((
                Ok(_),
                // If we find ">", it's the end of the generics parameters.
                TokenKind::Punctuation(Punc::Gt) => {
                    consumed += 1;
                    break;
                },
                // If we find ",", we're expecting another generics parameter
                TokenKind::Punctuation(Punc::Comma) => {
                    consumed += 1;
                    continue;
                },
                @else(return None) => ExpectedKind::GenericsParamDelim {
                    ctx,
                    prev_tokens: &tokens[..consumed],
                },
            ));
        }

        Ok(Some(GenericsParams {
            src: &tokens[..consumed],
            params,
            poisoned,
        }))
    }
}

impl<'a> GenericsParam<'a> {
    /// Consumes a single generics parameter as a prefix of the given tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    ///
    /// The value of `prev_tokens` gives the tokens already used in the greater scope of consuming
    /// a set of generics parameters, so that error messages may mention it explicitly.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericsParam<'a>, Option<usize>> {
        // Let's have a brief look at the first tokens of the BNF for a generics parameter:
        //   GenericsParam = Ident  ...
        //                | "const" ...
        //                | "ref"   ...
        // We can clearly see that these are the only options available, but we should be conscious
        // of how users might make mistakes. Expanding some of the definition now, we can see some
        // of the overlap between the items and how they might be mistakenly parsed as the others.
        //   GenericsParam =        Ident [ "::" TypeBound ]            [ "=" Type ]
        //                | "const" Ident ( "::" TypeBound | ":" Type ) [ "=" Expr ]
        //                | "ref"   Ident
        // "ref" parameters generally don't overlap with the others. For the other two, take the
        // following example:
        //   "Foo: Display = Bar"
        // The user might have meant to write "const Foo: Display = Bar" OR "Foo :: Display = Bar"
        //                                     ^^^^^                             ^^
        // - and it isn't immediately clear which one it was. To manage this, we'll separately trap
        // error mesages from the later portions of the generics parameter to make our best guess as
        // to what went wrong.
        //
        // Because this function has a lot of control flow, we'll also lay out a flow chart for
        // where we suspect the error was:
        //             +-----> "::" --> Full errors (TypeParam)
        //             |
        //             |        +-----> Successful trait --> (replace w/ "::"), assume [ "=" Type ]
        //             |        |
        // START --> Ident --> ":" ---> Succcessful type --> (missing const), assume [ "=" Expr ]
        //   |         |        |
        //   |         |        +-----> else --> Full errors (TypeParam; ":" mismatch)
        //   |         |
        //   |         +-----> else --> Full errors (TypeParam)
        //   |
        //   +-----> "const" --> Full errors (ConstParam)
        //   |
        //   +-----> "ref"   --> Full errors (RefParam)

        let mut consumed = 0;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        expect!((
            Ok(_),
            // This is the more complex case as we mentioned above - we'll continue with it in this
            // function.
            TokenKind::Ident(_) => (),
            // We'll delegate to other functions for everything else.
            TokenKind::Keyword(Kwd::Const) => {
                return GenericConstParam::consume(tokens, ends_early, containing_token, errors)
                    .map(GenericsParam::Const);
            },
            TokenKind::Keyword(Kwd::Ref) => {
                return GenericRefParam::consume(tokens, ends_early, containing_token, errors)
                    .map(GenericsParam::Ref)
            },
            @else(return Some) => ExpectedKind::GenericsParam { ctx, prev_tokens },
        ));

        consumed += 1;

        let snd_token = expect!((
            Ok(snd),
            // We're leaving the advanced error handling to *this* function, so we'll continue.
            TokenKind::Punctuation(Punc::Colon) => snd,
            TokenKind::Punctuation(Punc::DoubleColon) => {
                return GenericTypeParam::consume(
                    tokens,
                    ctx,
                    &tokens[..consumed],
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(GenericsParam::Type)
            },

            // For anything else, we leave it to `GenericTypeParam::consume` to generate the proper
            // error message
            _ => {
                return GenericTypeParam::consume(
                    tokens,
                    ctx,
                    &tokens[..consumed],
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(GenericsParam::Type)
            },
            @else(return Some) => ExpectedKind::GenericTypeParamColons { ctx, prev_tokens },
        ));

        consumed += 1;

        // At this point, we've found the tokens `[ Ident, ":", .. ]`. The flowchart now looks like
        // this:
        //              +-----> Successful trait --> (replace w/ "::"), assume [ "=" Type ]
        //              |
        //   Ident --> ":" ---> Succcessful type --> (missing const), assume [ "=" Expr ]
        //              |
        //              +-----> else --> Full errors (TypeParam; ":" mismatch)
        //
        // So, we'll attempt to parse the remaining pieces, first trying to parse the rest of a
        // type bound - and if that fails, we'll try a type instead.
        //
        // If they both fail, we'll simply fall back to `GenericTypeParam::consume`, which will
        // generate more appropriate error messages.
        //
        // We'll attempt to parse these two pieces (without passing through extra errors) by
        // giving them individual error `Vec`s to push to, so that it doesn't mess up the master
        // error set.

        let mut type_bound_errors = Vec::new();
        let type_bound_res = TypeBound::consume(
            &tokens[consumed..],
            ends_early,
            containing_token,
            &mut type_bound_errors,
        );

        // If we didn't get any errors from parsing this as a type bound, we'll continue with that
        // - hopefully it was intended to be a type parameter.
        //
        // Thankfully, in the vast majority of cases where it was actually intended to be a const
        // parameter, it will be a *named* type parameter, which will typically be matched by a
        // type bound, so we can check again later if the thing parsed as a trait here turns out to
        // actually be a type.
        if type_bound_errors.is_empty() && type_bound_res.is_ok() {
            return GenericTypeParam::consume(
                tokens,
                ctx,
                &tokens[..consumed],
                ends_early,
                containing_token,
                errors,
            )
            .map(GenericsParam::Type);
        }

        // Otherwise, we'll see if this can be successfully parsed as as a type
        let mut type_errors = Vec::new();
        let type_res = Type::consume(
            &tokens[consumed..],
            TypeContext::GenericConstParam {
                param: &tokens[..consumed],
                ctx,
            },
            ends_early,
            containing_token,
            &mut type_errors,
        );

        // If we parsed a type *but not a type bound*, then the most likely case is that the user
        // forgot to put "const" in front of a const parameter. We'll give them an error indicating
        // as such.
        if type_res.is_ok() {
            let type_res_consumed = type_res.as_ref().unwrap().consumed();

            // FIXME: If we find `"=" Expr` here, add that length to the full source.
            errors.push(Error::GenericConstParamMissingConst {
                full_src: &tokens[..consumed + type_res_consumed],
                type_src: &tokens[consumed..consumed + type_res_consumed],
            });

            return Err(Some(consumed + type_res_consumed));
        }

        // If neither of these worked, we'll go back to assuming it's a `GenericTypeParam`, and
        // produce the error from finding ":" instead of "::".
        errors.push(Error::Expected {
            kind: ExpectedKind::GenericTypeParamColons { ctx, prev_tokens },
            found: Source::TokenResult(Ok(snd_token)),
        });

        Err(Some(consumed))
    }
}

impl<'a> GenericTypeParam<'a> {
    /// Consumes a single generic type parameter as a prefix of the given tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericTypeParam<'a>, Option<usize>> {
        // Generics type parameters have the following form:
        //   Ident [ "::" TypeBound ] [ "=" Type ]
        // The rest of this function is fairly simple, following from this.
        let mut consumed = 0;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let ident_ctx = IdentContext::TypeParam(ctx, prev_tokens);
        let name = Ident::parse(
            tokens.get(consumed),
            IdentContext::TypeParam(ctx, prev_tokens),
            end_source!(containing_token),
            errors,
        )
        // TODO: Recover after failure here
        .map_err(|()| None)?;

        consumed += 1;

        let mut bound = None;
        let mut default_type = None;

        for _ in 0..2 {
            let after_type_bound = bound.is_some();
            let expected_kind = ExpectedKind::TypeParamFollowOn {
                after_type_bound,
                ctx,
                prev_tokens,
                param: &tokens[..consumed],
            };

            expect!((
                Ok(_),
                // If we haven't already consumed a type bound, we'll do that now
                TokenKind::Punctuation(Punc::DoubleColon) if !after_type_bound => {
                    consumed += 1;
                    bound = Some(
                        TypeBound::consume(
                            &tokens[consumed..],
                            ends_early,
                            containing_token,
                            errors,
                        )
                        .map_err(|_| None)?,
                    );
                },
                // Otherwise, if we find a "=", we'll consume a type here
                TokenKind::Punctuation(Punc::Eq) => {
                    consumed += 1;
                    default_type = Some(
                        Type::consume(
                            &tokens[consumed..],
                            TypeContext::GenericTypeParam {
                                param: &tokens[..consumed],
                                ctx,
                            },
                            ends_early,
                            containing_token,
                            errors,
                        )
                        .map_err(|_| None)?,
                    );

                    break;
                },
                // We'll also note the other possible tokens that are allowed to follow this
                TokenKind::Punctuation(Punc::Gt)
                | TokenKind::Punctuation(Punc::Comma) => break,
                // And finally, we'll produce an error if the token wasn't any of the ones we
                // thought it would be
                @else(return None) => expected_kind,
            ));
        }

        Ok(GenericTypeParam {
            src: &tokens[..consumed],
            name,
            bound,
            default_type,
        })
    }
}

impl<'a> GenericConstParam<'a> {
    /// Consumes a single generic `const` parameter as a prefix of the given tokens
    ///
    /// This function assumes that the first token it is given is the keyword `const`, and will
    /// panic if this is not the case.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericConstParam<'a>, Option<usize>> {
        // The BNF for constant parameters is fairly simple - most of the work is done by the
        // `Field` parser, so the BNF ends up simply being:
        //   GenericConstParam = "const" Field .
        //
        // The first thing we'll do, however, is to assert hat the tokens we were given *do* start
        // with the keyword `const`:
        assert_token!(
            tokens.first() => "keyword `const`",
            Ok(t) && TokenKind::Keyword(Kwd::Const) => (),
        );

        // We offset by 1 on each piece here because we've already consumed the "const" token
        let field = Field::consume(
            &tokens[1..],
            FieldContext::GenericConstParam,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + 1)))?;

        let consumed = field.consumed() + 1;

        Ok(GenericConstParam {
            src: &tokens[..consumed],
            field,
        })
    }
}

impl<'a> GenericRefParam<'a> {
    /// Consumes a generic "ref" parameter as a prefix of the given tokens
    ///
    /// This function assumes that the first token in the list is the keyword `ref`, and will panic
    /// if this is not the case.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericRefParam<'a>, Option<usize>> {
        assert_token!(
            tokens.first() => "keyword `const`",
            Ok(t) && TokenKind::Keyword(Kwd::Ref) => (),
        );

        make_expect!(tokens, 1, ends_early, containing_token, errors);
        expect!((
            Ok(t),
            TokenKind::Ident(name) => {
                Ok(GenericRefParam {
                    src: &tokens[..2],
                    ref_name: Ident { src: t, name },
                })
            },
            @else(return None) => ExpectedKind::Ident(IdentContext::GenericRefParam),
        ))
    }
}
