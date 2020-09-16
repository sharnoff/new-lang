use super::*;
use crate::files::{FileInfo, Span};

/// An "impl" block - either as a standalone type or for implementing a trait
///
/// While syntactically allowed as normal items, "impl" blocks are not allowed within trait
/// definitions or other impl blocks.
///
/// The BNF for impl blocks is fairly simple:
/// ```text
/// ImplBlock = "impl" [ Trait "for" ] Type ( ImplBody | ";" ) .
/// ```
/// Because some of the prefixes that are allowed for other items aren't allowed here (namely:
/// [`ProofStmts`] and [`Vis`]), there are a few steps taken in constructing error messages to be
/// more helpful to the user. In this case, it's done with the error variants
/// [`ProofStmtsDisallowedBeforeItem`] and [`VisDisallowedBeforeItem`].
///
/// Aside from this bit of extra care, the syntax here is mainly so simple because it's built of
/// other pieces. Impl blocks are allowed to provide standalone associated items for a type, or to
/// specifically implement a trait. The rest of the semantics around the validity of type/trait
/// pairs is complex and subject to change, so it will not be discussed here.
///
/// [`ProofStmts`]: struct.ProofStmts.html
/// [`Vis`]: enum.Vis.html
/// [`ProofStmtsDisallowedBeforeItem`]: ../errors/enum.Error.html#variant.ProofStmtsDisallowedBeforeItem
/// [`VisDisallowedBeforeItem`]: ../errors/enum.Error.html#variant.VisDisallowedBeforeItem
#[derive(Debug, Clone, Consumed)]
pub struct ImplBlock {
    #[consumed(1)] // 1 for leading "impl" keyword
    pub(in crate::ast) src: Span,
    // +1 for trailing "for" keyword
    #[consumed(trait_impl.as_ref().map(|t| t.consumed() + 1).unwrap_or(0))]
    pub trait_impl: Option<Path>,
    pub impl_ty: Type,

    /// The body of the `impl` block, if it is present. This type will be `None` if there was no
    /// body (i.e. if the item had a trailing semicolon).
    #[consumed(1)]
    pub body: Option<ImplBody>,
}

/// A helper type for [`ImplBlock`](struct.ImplBlock.html)
///
/// The source for this type is the single curly-brace enclosed token tree. For more general
/// information, please refer to the documentation for `ImplBlock`.
#[derive(Debug, Clone, Consumed)]
pub struct ImplBody {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    pub items: Vec<Item>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

impl ImplBlock {
    /// Consumes an `impl` block as a prefix of the given tokens
    ///
    /// This function assumes that the first token it is given is the keyword `impl`, and will
    /// panic if this is not the case.
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<ImplBlock, ItemParseErr> {
        assert_token!(
            tokens.first() => "keyword `impl`",
            Ok(t) && TokenKind::Keyword(Kwd::Impl) => (),
        );

        let mut consumed = 1;

        // The syntax for `impl` blocks *is* mildly ambiguous.
        //
        // Because there's overlap between the syntax for specifying `Trait`s versus `Type`s, we
        // can't immediately tell which part of the syntax here we're looking at:
        //   ImplBlock = "impl" [ Trait "for" ] Type ImplBody
        //                        ^^^^^         ^^^^
        //                           ^ ambiguity ^
        // The ambiguity is fairly simple to see if we look at the syntax definitions for the two:
        //   Trait = Path .
        //           ^^^^
        //   Type  = Path [ Refinements ]
        //           ^^^^
        //         | RefType
        //         | MutType
        //         ...
        //
        // So: If we find an identifier as the first token after "impl", then we parse a path and
        // see what comes after. Otherwise, if token starts a type, we'll skip straight to that.
        // If we can't find either, then we'll produce a suitable error (there's some special cases
        // we'd like to be nice about).

        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        // We'll define our own macro for sipmlifying error returns, just so that the `expect!`
        // calls aren't so messy.
        macro_rules! return_err {
            () => {{
                return Err(ItemParseErr { consumed });
            }};
        }

        //`jump_to_type` is our way of simulating goto's
        let mut jump_to_type = false;
        let path_start_idx = consumed;

        // Note that we DON'T increment `consumed` here - this is just for peeking to determine
        // control flow
        expect!((
            Ok(fst),
            TokenKind::Ident(_) => (),
            _ if Type::is_starting_token(fst) => jump_to_type = true,
            @err TokenKind::Punctuation(Punc::Lt) => Error::GenericParamsOnImplBlock { src: Source::token(file, fst) },
            @else { return_err!() } => ExpectedKind::ImplTraitOrType,
        ));

        let mut trait_impl = None;
        let mut impl_ty = None;

        // If we aren't jumping to the type, we're parsing a path as our trait, then interpreting
        // it based on what comes next.
        if !jump_to_type {
            let path = Path::consume(file, &tokens[consumed..], ends_early, containing_token, errors)
                .map_err(ItemParseErr::add(consumed))?;
            consumed += path.consumed();

            // And with that path parsed, we'll look ahead one token to see whether this should be
            // interpreted as a trait or as the implementing type.
            expect!((
                Ok(_),
                // A trailing "|" after a path will indicate refinements, which means that the path
                // was part of a type.
                TokenKind::Punctuation(Punc::Or) => {
                    let refinements = Refinements::try_consume(
                        file,
                        &tokens[consumed..],
                        Restrictions::default(),
                        ends_early,
                        containing_token,
                        errors,
                    )
                    .map_err(ItemParseErr::add(consumed))?;

                    consumed += refinements.consumed();

                    impl_ty = Some(Type::Named(NamedType {
                        src: Source::slice_span(file, &tokens[path_start_idx..consumed]),
                        path,
                        refinements,
                    }));

                    consumed += impl_ty.consumed();
                },
                // Trailing curly braces or semicolon indiciate the `ipml` body; the original path
                // was the implementing type.
                TokenKind::Tree { delim: Delim::Curlies, .. }
                | TokenKind::Punctuation(Punc::Semi) => {
                    impl_ty = Some(Type::Named(NamedType {
                        src: Source::slice_span(file, &tokens[path_start_idx..consumed]),
                        path,
                        refinements: None,
                    }));

                    consumed += impl_ty.consumed();
                },
                // The keyword `for` means we have `"impl" Trait "for" Type`, so the original path
                // was the trait being implemented
                TokenKind::Keyword(Kwd::For) => {
                    trait_impl = Some(path);
                    // We've already "consumed" `path`, but we still need to mark the keyword "for"
                    // as consumed:
                    consumed += 1;
                },
                @else { return_err!() } => ExpectedKind::ImplAfterPath,
            ));
        }

        // We might have already specified the implementing type in attempting to disambiguate
        // between a leading trait or type. If we haven't, we'll parse the type now.
        if impl_ty.is_none() {
            let ty = Type::consume(
                file,
                &tokens[consumed..],
                TypeContext::ImplBlockType {
                    prev_tokens: Source::slice_span(file, &tokens[..consumed]),
                },
                Restrictions::default(),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(ItemParseErr::add(consumed))?;
            impl_ty = Some(ty);

            consumed += impl_ty.consumed();
        }

        // And finally, we'll parse the body of the `impl` block
        let mut body = None;
        expect!((
            Ok(body_token),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            TokenKind::Tree { delim: Delim::Curlies, inner, .. } => {
                consumed += 1;
                let ends_early = false;

                let (items, poisoned) =
                    Item::parse_all(file, inner, ends_early, Some(body_token), errors);

                body = Some(ImplBody {
                    src: body_token.span(file),
                    items,
                    poisoned,
                });
            },
            @else { return_err!() } => ExpectedKind::ImplBody,
        ));

        Ok(ImplBlock {
            src: Source::slice_span(file, &tokens[..consumed]),
            trait_impl,
            // We're safe to unwrap here becaues the value is always set by the time we get to this
            // point.
            impl_ty: impl_ty.unwrap(),
            body,
        })
    }
}
