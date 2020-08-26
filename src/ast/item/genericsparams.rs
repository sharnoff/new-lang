use super::*;

/// A collection of generic parameters, given as part of a type or function declarations
///
/// This is provided separately (instead of just [`Vec<GenericParam>`]) so that we can track and
/// refer to the set of parameters as a whole group.
///
/// Briefly, the BNF for generic parameters is:
/// ```text
/// GenericParams = "<" GenericParam { "," GenericParam } [ "," ] ">" .
/// ```
/// For more information, see [`GenericParam`].
///
/// [`Vec<GenericParam>`]: struct.GenericParam.html
/// [`GenericParam`]: struct.GenericParam.html
#[derive(Debug, Clone)]
pub struct GenericParams<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub params: Vec<GenericParam<'a>>,
    pub poisoned: bool,
}

/// A single generic parameter, given as part of a type or function declaration
///
/// The BNF can be defined by either of these equivalent definitions:
/// ```text
/// GenericParam = Ident [ "::" TypeBound ] [ "=" Type ]
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
pub enum GenericParam<'a> {
    Type(GenericTypeParam<'a>),
    Const(GenericConstParam<'a>),
    Ref(GenericRefParam<'a>),
}

/// A generic type parameter, given as part of a type or function declaration
///
/// Type parameters are the most common generic parameter. There are however, two others - to see
/// the full set, refer to [`GenericParam`].
///
/// The BNF definition for a single generic type parameter is:
/// ```text
/// GenericTypeParam = Ident [ "::" TypeBound ] [ "=" Type ] .
/// ```
/// All type parameters are given by their name, possibly followed by a [type bound], which
/// restricts type arguments to those that implement a set of traits. Additionally, default values
/// for these types can be given by the trailing [`"=" Type`].
///
/// [`GenericParam`]: struct.GenericParam.html
/// [type bound]: ../types/struct.TypeBound.html
/// [`"=" Type`]: ../types/enum.Type.html
#[derive(Debug, Clone)]
pub struct GenericTypeParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub bound: Option<TypeBound<'a>>,
    pub default_type: Option<Type<'a>>,
}

#[derive(Debug, Clone)]
pub struct GenericConstParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub ty: Type<'a>,
    pub default: Option<Expr<'a>>,
}

#[derive(Debug, Clone)]
pub struct GenericRefParam<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub ref_name: Ident<'a>,
}

impl<'a> GenericParams<'a> {
    /// Attempts to consume generic parameters as a prefix of the given tokens, failing with
    /// `Ok(None)` if the tokens clearly do not start with generic parameters.
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
        ctx: GenericParamsContext<'a>,
        allow_start_err: impl Fn(&token_tree::Error) -> bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<GenericParams<'a>>, Option<usize>> {
        make_getter!(macro_rules! get, tokens, ends_early, errors);

        // First, we'll check for whether there's a "<". If there isn't, we'll just return.
        match tokens.first() {
            Some(Ok(token)) => match &token.kind {
                TokenKind::Punctuation(Punc::Gt) => (),
                _ => return Ok(None),
            },
            Some(Err(e)) => {
                if allow_start_err(e) {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericParams(ctx),
                        found: Source::TokenResult(Err(*e)),
                    });
                }

                return Err(None);
            }
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericParams(ctx),
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
        }

        let mut consumed = 1;
        let mut poisoned = false;
        let mut params = Vec::new();

        loop {
            let param_res = GenericParam::consume(
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

            let next = get!(
                consumed,
                Err(e) => Error::Expected {
                    kind: ExpectedKind::GenericParamDelim {
                        ctx,
                        prev_tokens: &tokens[..consumed],
                    },
                    found: Source::TokenResult(Err(*e)),
                },
                None => Error::Expected {
                    kind: ExpectedKind::GenericParamDelim {
                        ctx,
                        prev_tokens: &tokens[..consumed],
                    },
                    found: end_source!(containing_token),
                },
            );

            match &next.kind {
                // If we find ">", it's the end of the generic parameters.
                TokenKind::Punctuation(Punc::Gt) => {
                    consumed += 1;
                    break;
                }
                // If we find ",", we're expecting another generic parameter
                TokenKind::Punctuation(Punc::Comma) => {
                    consumed += 1;
                    continue;
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::GenericParamDelim {
                            ctx,
                            prev_tokens: &tokens[..consumed],
                        },
                        found: Source::TokenResult(Ok(next)),
                    });

                    return Err(None);
                }
            }
        }

        Ok(Some(GenericParams {
            src: &tokens[..consumed],
            params,
            poisoned,
        }))
    }
}

impl<'a> GenericParam<'a> {
    /// Consumes a single generic parameter as a prefix of the given tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    ///
    /// The value of `prev_tokens` gives the tokens already used in the greater scope of consuming
    /// a set of generic parameters, so that error messages may mention it explicitly.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ctx: GenericParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericParam<'a>, Option<usize>> {
        // Let's have a brief look at the first tokens of the BNF for a generic parameter:
        //   GenericParam = Ident   ...
        //                | "const" ...
        //                | "ref"   ...
        // We can clearly see that these are the only options available, but we should be conscious
        // of how users might make mistakes. Expanding some of the definition now, we can see some
        // of the overlap between the items and how they might be mistakenly parsed as the others.
        //   GenericParam =         Ident [ "::" [ Refinements ] Trait { "+" Trait } ] [ "=" Type ]
        //                | "const" Ident   ":"                  Type                  [ "=" Expr ]
        //                | "ref"   Ident
        // "ref" parameters generally don't overlap with the others. For the other two, take the
        // following example:
        //   "Foo: Display = Bar"
        // The user might have meant to write "const Foo: Display = Bar" OR "Foo :: Display = Bar"
        //                                     ^^^^^                             ^^
        // - and it isn't immediately clear which one it was. To manage this, we'll separately trap
        // error mesages from the later portions of the generic parameter to make our best guess as
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

        make_getter!(macro_rules! get, tokens, ends_early, errors);
        let mut consumed = 0;

        let fst_token = get!(
            consumed,
            Err(e) => Error::Expected {
                kind: ExpectedKind::GenericParam { ctx, prev_tokens },
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::GenericParam { ctx, prev_tokens },
                found: end_source!(containing_token),
            },
        );
        consumed += 1;

        match &fst_token.kind {
            // This is the more complex case as we mentioned above - we'll continue with it in this
            // function.
            TokenKind::Ident(_) => (),
            // We'll delegate to other functions for everything else.
            TokenKind::Keyword(Kwd::Const) => {
                return GenericConstParam::consume(tokens, ends_early, containing_token, errors)
                    .map(GenericParam::Const);
            }
            TokenKind::Keyword(Kwd::Ref) => {
                return GenericRefParam::consume(tokens, ends_early, containing_token, errors)
                    .map(GenericParam::Ref)
            }
            _ => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericParam { ctx, prev_tokens },
                    found: Source::TokenResult(Ok(fst_token)),
                });

                // FIXME: This should do some recovery here to find the next generic parameter,
                // given by the commas, instead of trying again immediately.
                return Err(Some(consumed));
            }
        }

        let snd_token = get!(
            consumed,
            Err(e) => Error::Expected {
                kind: ExpectedKind::GenericTypeParamColons { ctx, prev_tokens },
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::Expected {
                kind: ExpectedKind::GenericTypeParamColons { ctx, prev_tokens },
                found: end_source!(containing_token),
            },
        );
        consumed += 1;

        match &snd_token.kind {
            TokenKind::Punctuation(Punc::DoubleColon) => {
                return GenericTypeParam::consume(
                    tokens,
                    ctx,
                    &tokens[..consumed],
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(GenericParam::Type)
            }

            // We're leaving the advanced error handling to *this* function, so we'll continue.
            TokenKind::Punctuation(Punc::Colon) => (),

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
                .map(GenericParam::Type)
            }
        }

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
            TypeBoundContext::GenericTypeParam {
                param: &tokens[..consumed],
                ctx,
            },
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
            .map(GenericParam::Type);
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
        ctx: GenericParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericTypeParam<'a>, Option<usize>> {
        // Generic type parameters have the following form:
        //   Ident [ "::" TypeBound ] [ "=" Type ]
        // The rest of this function is fairly simple, following from this.
        make_getter!(macro_rules! get, tokens, ends_early, errors);
        let mut consumed = 0;

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

            let token = get!(
                consumed,
                Err(e) => Error::Expected {
                    kind: expected_kind,
                    found: Source::TokenResult(Err(*e)),
                },
                None => Error::Expected {
                    kind: expected_kind,
                    found: end_source!(containing_token),
                },
            );

            use TokenKind::Punctuation;

            match &token.kind {
                Punctuation(Punc::DoubleColon) if !after_type_bound => {
                    consumed += 1;
                    bound = Some(
                        TypeBound::consume(
                            &tokens[consumed..],
                            TypeBoundContext::GenericTypeParam {
                                param: &tokens[..consumed],
                                ctx,
                            },
                            ends_early,
                            containing_token,
                            errors,
                        )
                        .map_err(|_| None)?,
                    );
                }
                Punctuation(Punc::Eq) => {
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
                }
                // We'll also note the other possible tokens that are allowed to follow this
                Punctuation(Punc::Gt) | Punctuation(Punc::Comma) => break,
                _ => {
                    errors.push(Error::Expected {
                        kind: expected_kind,
                        found: Source::TokenResult(Ok(token)),
                    });

                    // TODO: recover after failure here
                    return Err(None);
                }
            }
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
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericConstParam<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> GenericRefParam<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<GenericRefParam<'a>, Option<usize>> {
        todo!()
    }
}
