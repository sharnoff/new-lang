use super::*;

/// A function declaration, independent of where it occurs
///
/// Note that this also includes function declarations that may be part of a trait definition, and
/// so they are allowed here to not have a body. This is left to be validated later, as part of a
/// separate pass.
///
/// Nevertheless, we'll briefly touch on some of the context-specific semantic validity of function
/// delcarations (and what each component signifies).
///
/// The BNF definition for function declarations is:
/// ```text
/// FnDecl = ProofStmts [ Vis ] [ "const" ] [ "pure" ] "fn" Ident [ GenericsParams ]
///          FnParams [ "->" Type ] ( ";" | BlockExpr ) .
/// ```
/// The first few syntactic elements ([`ProofStmts`] through [`GenericsParams`]) should be fairly
/// self-explanatory - these work as expected and are valid in any context. After these, the
/// validity of certain components of [`FnParams`] changes depending on the context, but nothing
/// about the enclosing `FnDecl` due to it - for more information, see the documentation about the
/// type. After the parameters, the return type is typically given - this may be omitted if equal
/// to `()`.
///
/// Finally, the implementation may be given or replaced by a semicolon. Body-less functions are
/// only valid inside trait definitions.
///
/// Note also that visibility qualifiers are not allowed within trait definitions; each item takes the
/// visibility of the parent trait.
///
/// [`ProofStmts`]: ../proofstmts/struct.ProofStmts.html
/// [`GenericsParams`]: ../genericsparams/struct.GenericsParams.html
/// [`FnParams`]: struct.FnParams.html
#[derive(Debug, Clone)]
pub struct FnDecl<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub proof_stmts: Option<ProofStmts<'a>>,
    pub vis: Option<Vis<'a>>,
    pub is_const: Option<&'a Token<'a>>,
    pub is_pure: Option<&'a Token<'a>>,
    pub name: Ident<'a>,
    pub generic_params: Option<GenericsParams<'a>>,
    pub params: FnParams<'a>,
    pub return_ty: Option<Type<'a>>,
    pub body: Option<BlockExpr<'a>>,
}

/// The parameters of a function; a helper type for [`FnDecl`]
///
/// This type is defined by the following pair of BNF constructs:
/// ```text
/// FnParams = "(" MethodReceiver [ "," Field { "," Field } ] [ "," ] ")"
///          | "("                [     Field { "," Field } [ "," ] ] ")" .
/// MethodReceiver = [ "&" [ Refinements ] ] [ "mut" ] "self" [ Refinements ] .
/// ```
///
/// [Method receivers] are only semantically valid within [`impl` blocks], as they indicate that the
/// defined function may be called on the implementing type. This distinction is not made at
/// parse-time, and instead must be validated later.
///
/// The source for this type is represented by the single parenthetical token tree containing all
/// of the parameters.
///
/// [`FnDecl`]: struct.FnDecl.html
/// [Method receivers]: struct.MethodReceiver.html
/// [`impl` blocks]: ../implblock/struct.ImplBlock.html
#[derive(Debug, Clone)]
pub struct FnParams<'a> {
    pub(in crate::ast) src: &'a Token<'a>,
    pub receiver: Option<MethodReceiver<'a>>,
    pub params: Vec<Field<'a>>,
    pub poisoned: bool,
}

/// A method receiver; a helper type for [`FnParams`]
///
/// Method receivers are a construct available for function declarations within [`impl` blocks], to
/// indicate that the function may be called on the implementing type. As is mentioned elsewhere,
/// method receivers are parsed regardless of the context, and then validation is a task left to
/// the consumer of the AST.
///
/// This struct is defined by the following BNF construction:
/// ```text
/// MethodReceiver = [ "&" [ Refinements ] [ "mut" ] ] "self" [ Refinements ] .
/// ```
///
/// [`FnParams`]: struct.FnParams.html
/// [`impl` blocks]: ../implblock/struct.ImplBlock.html
#[derive(Debug, Clone)]
pub struct MethodReceiver<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub maybe_ref: Option<MethodReceiverRef<'a>>,
    pub self_refinements: Option<Refinements<'a>>,
}

/// A helper type for [`MethodReceiver`] to collect the optional portions that are only available
/// when referencing `self`
///
/// Formally, this type represents the following optional piece of the `MethodReceiver` BNF:
/// ```text
/// MethodRecieverRef = "&" [ Refinements ] [ "mut" ] .
/// ```
///
/// [`MethodReceiver`]: struct.MethodReceiver.html
#[derive(Debug, Clone)]
pub struct MethodReceiverRef<'a> {
    pub ref_token: &'a Token<'a>,
    pub refinements: Option<Refinements<'a>>,
    pub has_mut: Option<&'a Token<'a>>,
}

impl<'a> FnDecl<'a> {
    /// Consumes a function declaration as a prefix of the given set of tokens
    ///
    /// There are many pieces of context passed into this function in order to prevent
    /// double-verification of some of the common elements for every item.
    ///
    /// `ident_idx` gives the index in the tokens where the function's name (given as an identifier)
    /// is expected. For example, given the following set of tokens:
    /// ```text
    /// [ Keyword(Const), Keyword(Fn), Ident("foo"), .. ]
    /// ```
    /// `ident_idx` will be equal to 2. The tokens up to `ident_idx` are guaranteed to be valid for
    /// a function declaration (with the values parsed from them given by the various parameters:
    /// `proof_stmts`, `vis`, `is_const`, and `is_pure`). While it is given that
    /// `tokens[ident_idx - 1]` will be the "fn" keyword, it is not guaranteed that there is an
    /// identifier token at `ident_idx`.
    ///
    /// In the event of an error, this function may either return `None` to indicate that parsing
    /// within the current token tree should not continue, or `Some` to give the number of tokens
    /// that were consumed in parsing here.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        proof_stmts_consumed: usize,
        vis: Option<Vis<'a>>,
        is_const: Option<&'a Token<'a>>,
        is_pure: Option<&'a Token<'a>>,
    ) -> Result<FnDecl<'a>, ItemParseErr> {
        // The first token that we're given is an identifier - we'll get the token here.
        let name = Ident::parse(
            tokens.get(ident_idx),
            IdentContext::FnDeclName(&tokens[proof_stmts_consumed..ident_idx]),
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| ItemParseErr {
            consumed: (ident_idx + 1).min(tokens.len()),
        })?;

        let mut consumed = ident_idx + 1;

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let generic_params = GenericsParams::try_consume(
            &tokens[consumed..],
            GenericsParamsContext::FnDecl(&tokens[proof_stmts_consumed..consumed]),
            |err| match err {
                token_tree::Error::UnclosedDelim(Delim::Parens, _, _) => true,
                _ => false,
            },
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;

        consumed += generic_params.consumed();

        // A temporary enum for marking where to go next if parsing the parameters failed
        // The relevance of this type is made clear below.
        enum FailedParamsGoto {
            ReturnType,
            Body,
        }

        // After any generic parameters, we expect the parameters to the function. Because these
        // are in a parentheses-enclosed token tree, we only pass a single token
        let params = expect!((
            Ok(t),
            TokenKind::Tree { delim: Delim::Curlies, inner, .. } => {
                consumed += 1;
                Ok(FnParams::parse(t, inner, errors))
            },
            _ => {
                // If we couldn't find the function parameters, we'll check whether continuing is
                // feasible. This is essentially a set of heuristics for guess whether the user
                // *did* intend to write a function here.
                //
                // Here's some examples that we might want to explicitly account for have:
                //   fn foo -> Bar { ... }    // forgetting the parens, 1/2
                //   fn foo { ... }           // forgetting the parens, 2/2
                //   fn foo = bar() + baz;    // you aren't allowed to assign to functions
                //   fn foo \n\n type Bar ... // user forgot to finish writing this
                // Because of this, we get the following table of tokens that would cause us to
                // continue (and to which point):
                //     ┌────────────────┬─────────────────────┐
                //     │ Token sequence │ Continue (where)?   │
                //     ├────────────────┼─────────────────────┤
                //     │ [ "->", .. ]   │ Yes (return type)   │
                //     │ [ "{",  .. ]   │ Yes (body)*         │
                //     │ [ "=",  .. ]   │ No (custom error)** │
                //     │ else           │ No                  │
                //     └────────────────┴─────────────────────┘
                //      * Curly braces could also be a type, but the function body will be more
                //        common, so we use that instead.
                //     ** TODO: This error message has not yet been written - this syntax may be
                //        added in a future version.
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::ThinArrow) => Err(FailedParamsGoto::ReturnType),
                    TokenKind::Tree { delim: Delim::Curlies, .. } => Err(FailedParamsGoto::Body),
                    @else { return Err(ItemParseErr { consumed }) } => @no_error,
                ))
            },
            @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::FnParams {
                fn_start: &tokens[ident_idx-1..consumed]
            },
        ));

        let do_ret_ty = match &params {
            Ok(_) | Err(FailedParamsGoto::ReturnType) => true,
            Err(FailedParamsGoto::Body) => false,
        };

        let return_ty = if !do_ret_ty {
            None
        } else {
            // The return type may or may not be present - if it is, it'll be preceeded by a
            // thin-arrow ("->")
            expect!((
                Ok(_),
                TokenKind::Punctuation(Punc::ThinArrow) => {
                    consumed += 1;

                    Some(
                        Type::consume(
                            &tokens[consumed..],
                            TypeContext::FnDeclReturn(&tokens[..consumed]),
                            ends_early,
                            containing_token,
                            errors,
                        )
                        .map_err(ItemParseErr::add(consumed))?
                    )
                },
                // The next token might be either of: curlies or a semicolon to account for the
                // function body.
                TokenKind::Tree { delim: Delim::Curlies, ..  } => None,
                TokenKind::Punctuation(Punc::Semi) => None,

                @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::FnBodyOrReturnType {
                    fn_src: &tokens[..consumed],
                },
            ))
        };

        // Get the function body - this might instead be left as a semicolon, so we're looking
        // for tokens that are either ";" or "{" .. "}".

        let body = expect!((
            Ok(t),
            // The body of the function may be left out in certain cases
            TokenKind::Punctuation(Punc::Semi) => {
                consumed += 1;
                None
            },
            TokenKind::Tree { delim: Delim::Curlies, .. } => {
                BlockExpr::parse(
                    tokens.get(consumed),
                    ends_early,
                    end_source!(containing_token),
                    errors,
                )
                .map(Some)
                .map_err(|()| ItemParseErr { consumed })?
            },
            @else { return Err(ItemParseErr { consumed }) } => {
                ExpectedKind::FnBody { fn_src: &tokens[..consumed] }
            }
        ));

        params
            .map_err(|_| ItemParseErr { consumed })
            .map(|params| FnDecl {
                src: &tokens[..consumed],
                proof_stmts,
                vis,
                is_const,
                is_pure,
                name,
                generic_params,
                params,
                return_ty,
                body,
            })
    }
}

impl<'a> FnParams<'a> {
    /// Parses function parameters from the given token
    ///
    /// This function expects the source token to be a parenthetically-enclosed token tree, but
    /// does not check this.
    ///
    /// The only type of failure available to this function is through marking the internal portion
    /// of the parameters as poisoned.
    pub(super) fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> FnParams<'a> {
        let ends_early = false;

        // Because function parameters are mostly made up of a couple components, this parsing
        // function isn't all that complicated.
        //
        // The BNF definition for function parameters gives us:
        //   FnParams = "(" MethodReceiver [ "," Field { "," Field } ] [ "," ] ")"
        //            | "("                [     Field { "," Field } [ "," ] ] ")" .
        // But we don't need to worry about the outer parentheses, so we can just focus on parsing
        // the (simpler) bit of:
        //   MethodReceiver [ "," Field { "," Field } ] [ "," ]
        //   |              [     Field { "," Field } [ "," ] ]
        // This is mostly a lot of syntax to precisely say the following: Method receivers and
        // other fields are both optional, independent of each other, and they may both have
        // trailing commas. If we have both, however, there must be a comma between them.

        // We'll set up a few things to start off with, just so that early returns are uniform
        let mut consumed = 0;
        let mut receiver = None;
        let mut params = Vec::new();
        let mut poisoned = false;

        make_expect!(inner, consumed, ends_early, Some(src), errors);

        // First will be a helper macro to handle error returns:
        macro_rules! return_err {
            () => {{
                return FnParams {
                    src,
                    receiver,
                    params,
                    poisoned: true,
                };
            }};
        }

        // We'll also define a helper macro in order to allow handling the return types we get from
        // parsing - we want to continue with either of Ok(_) or Err(Some(_)), but return
        macro_rules! handle {
            (Ok(_) $($rest:tt)*) => { handle!(Ok(t) => $($rest)*) };
            (Ok($bind:ident) => $process:expr, $result:expr) => {{
                match $result {
                    Ok($bind) => {
                        consumed += $bind.consumed();
                        $process
                    }
                    Err(Some(c)) => {
                        consumed += c;
                        poisoned = true;
                    }
                    Err(None) => return_err!(),
                }
            }};
        }

        // And with that macro out of the way, the rest of this becomes very simple!
        //
        // First, we attempt to parse the receiver
        handle!(Ok(r) => receiver = r, MethodReceiver::try_consume(inner, ends_early, src, errors));

        // Then, if that's not the end of the tokens, we're expecting a trailing comma:
        if receiver.is_some() && consumed < inner.len() {
            expect!((
                Ok(_),
                TokenKind::Punctuation(Punc::Comma) => consumed + 1,
                @else { return_err!() } => ExpectedKind::FnParamsDelim,
            ));
        }

        // And then we loop over all of the elements
        while consumed < inner.len() {
            handle!(
                Ok(p) => params.push(p),
                Field::consume(
                    &inner[consumed..],
                    FieldContext::FnParam,
                    ends_early,
                    Some(src),
                    errors,
                )
            );

            // After the parameter, we'll expect a comma if there's more tokens
            //
            // This is exactly the same as above, for a trailing comma after the receiver
            if consumed < inner.len() {
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::Comma) => consumed + 1,
                    @else { return_err!() } => ExpectedKind::FnParamsDelim,
                ));
            }
        }

        FnParams {
            src,
            receiver,
            params,
            poisoned,
        }
    }
}

impl<'a> MethodReceiver<'a> {
    /// Attempts to consume a method receiver as a prefix of the given tokens
    fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: &'a Token<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<MethodReceiver<'a>>, Option<usize>> {
        if tokens.is_empty() {
            return Ok(None);
        }

        let mut consumed = 0;
        make_expect!(tokens, consumed, ends_early, Some(containing_token), errors);

        let maybe_ref = expect!((
            Ok(ref_token),
            TokenKind::Punctuation(Punc::And) => {
                consumed += 1;

                let refinements = Refinements::try_consume(
                    &tokens[consumed..],
                    ends_early,
                    Some(containing_token),
                    errors,
                )
                .map_err(p!(Some(c) => Some(c + consumed)))?;
                consumed += refinements.consumed();

                // After the refinements, we'll see if we have "mut" to indicate that it's a
                // mutable reference
                let has_mut = expect!((
                    Ok(mut_token),
                    TokenKind::Keyword(Kwd::Mut) => Some(mut_token),
                    _ => None,
                    @else(return None) => ExpectedKind::MethodReceiverMutOrSelf,
                ));

                consumed += has_mut.consumed();

                Some(MethodReceiverRef { ref_token, refinements, has_mut })
            },
            _ => None,
            @else(return None) => ExpectedKind::MethodReceiverOrParam,
        ));

        expect!((
            Ok(_),
            TokenKind::Keyword(Kwd::SelfKwd) => consumed += 1,
            // We're only really expecting `self` if we've already found other pieces of the
            // receiver. If we haven't, it's fine for it not to be there.
            _ if maybe_ref.is_none() => return Ok(None),
            @else(return None) => ExpectedKind::MethodReceiverSelf,
        ));

        // And then, as our final component, we'll see if there's any refinements on `self`:
        let self_refinements = Refinements::try_consume(
            &tokens[consumed..],
            ends_early,
            Some(containing_token),
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += self_refinements.consumed();

        Ok(Some(MethodReceiver {
            src: &tokens[..consumed],
            maybe_ref,
            self_refinements,
        }))
    }
}
