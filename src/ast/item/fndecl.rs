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
/// [`ProofStmts`]: struct.ProofStmts.html
/// [`GenericsParams`]: struct.GenericsParams.html
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

#[derive(Debug, Clone)]
pub struct FnParams<'a> {
    pub(in crate::ast) src: &'a Token<'a>,
    pub self_prefix: Option<FnParamsReceiver<'a>>,
    pub args: Vec<StructTypeField<'a>>,
}

#[derive(Debug, Clone)]
pub struct FnParamsReceiver<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub is_ref: Option<&'a Token<'a>>,
    pub ref_refinements: Option<Refinements<'a>>,
    pub is_mut: Option<&'a Token<'a>>,
    pub self_refinements: Option<Refinements<'a>>,
}

impl<'a> FnDecl<'a> {
    /// Consumes a function declaration as a prefix of the given set of tokens
    ///
    /// The index in the tokens where the function's name (given as an identifier) is expected. For
    /// example, given the following set of tokens:
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
    ) -> Result<FnDecl<'a>, Option<usize>> {
        // The first token that we're given is an identifier - we'll get the token here.
        let name = Ident::parse(
            tokens.get(ident_idx),
            IdentContext::FnDeclName(&tokens[proof_stmts_consumed..ident_idx]),
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| Some(tokens.len().min(ident_idx + 1)))?;

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
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += generic_params.consumed();

        // A temporary enum for marking where to go next if parsing the parameters failed
        // The relevance of this type is made clear below.
        enum FailedParamsGoto {
            ReturnType,
            Body,
        }

        // After any generic parameters, we expect the parameters to the function. Because these
        // are in a parentheses-enclosed token tree, we only pass a single token
        let params = match FnParams::parse(
            tokens.get(consumed),
            end_source!(containing_token),
            errors,
        ) {
            Ok(ps) => {
                // We account for `consumed` here because some of the error cases
                // *don't* increment it
                consumed += 1;
                Ok(ps)
            }
            Err(()) => {
                // If we failed to parse the function parameters, we'll check whether continuing is
                // feasible. This is essentialy a set of heuristics for guessing whether the user
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
                //     ** This error message is actually taken care of inside of `FnParams::parse`

                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::ThinArrow) => Err(FailedParamsGoto::ReturnType),
                    TokenKind::Tree { delim: Delim::Curlies, .. } => Err(FailedParamsGoto::Body),
                    @else(return Some) => @no_error,
                ))
            }
        };

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
                        .map_err(p!(Some(c) => Some(c + consumed)))?,
                    )
                },
                // The next token might be either of: curlies or a semicolon to account for the
                // function body.
                TokenKind::Tree { delim: Delim::Curlies, ..  } => None,
                TokenKind::Punctuation(Punc::Semi) => None,

                @else(return Some) => ExpectedKind::FnBodyOrReturnType {
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
                .map_err(|()| Some(consumed))?
            },
            @else(return Some) => ExpectedKind::FnBody { fn_src: &tokens[..consumed] },
        ));

        params.map_err(|_| Some(consumed)).map(|params| FnDecl {
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
    /// Because function parameters are always enclosed in parentheses, the single token is
    /// expected to be a parentheses-enclosed block.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub(super) fn parse(
        token: Option<&'a TokenResult<'a>>,
        none_source: Source<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<FnParams<'a>, ()> {
        todo!()
    }
}
