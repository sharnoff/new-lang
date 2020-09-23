use super::*;
use crate::files::{FileInfo, Span};

/// A trait definition
///
/// While these are syntactically allowed within trait definitions, they are not semantically valid
/// in those positions - this is a feature that may be added in the future, but it is not currently
/// planned.
///
/// The BNF for trait definitions is:
/// ```text
/// TraitDef = ProofStmts [ Vis ] "trait" Ident [ GenericsParams ] [ "::" TypeBound ] ( ImplBody | ";" ) .
/// ```
/// Some of the syntax elements here warrant an explanation; we'll go through those in order.
/// Firstly, while trait definitions may be preceeded by proof statements, there aren't currently
/// any ways in which proof could apply to the contents of a trait definition - in any case, this
/// validation is left for later.
///
/// Beyond the first few elements, traits are defined by their name and whatever generic parameters
/// they take as input. They may also list "super traits" - additional restrictions given by a
/// [`TypeBound`] that all implementors of this trait must also satisfy.
///
/// In the event that the trait has no items in its body, a single semicolon may be used in place
/// of an empty curly-brace block.
///
/// [`TypeBound`]: struct.TypeBound.html
#[derive(Debug, Clone, Consumed)]
pub struct TraitDef {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    pub proof_stmts: Option<ProofStmts>,
    pub vis: Option<Vis>,
    #[consumed(name.consumed() + 1)] // +1 for "trait" keyword
    pub name: Ident,
    pub generics_params: Option<GenericsParams>,
    // +1 for leading "::"
    #[consumed(super_traits.as_ref().map(|t| t.consumed() + 1).unwrap_or(0))]
    pub super_traits: Option<TypeBound>,
    #[consumed(1)]
    pub body: Option<ImplBody>,
}

impl TraitDef {
    /// Consumes a trait definition as a prefix of the given tokens
    ///
    /// The semantics for this function are identical to what's described in the documentation for
    /// [`FnDecl::consume`]. For more information on the meaning of these arguments, please refer
    /// to that function.
    ///
    /// [`FnDecl::consume`]: ../fndecl/struct.FnDecl.html#method.consume
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
        proof_stmts: Option<ProofStmts>,
        vis: Option<Vis>,
    ) -> Result<TraitDef, ItemParseErr> {
        // We'll do a little bit of setup here.

        let mut consumed = ident_idx;

        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);
        macro_rules! err {
            () => {{
                return Err(ItemParseErr { consumed });
            }};
        }

        let kwd_idx = ident_idx - 1;
        let kwd_token = assert_token!(
            tokens.get(kwd_idx) => "keyword `trait`",
            Ok(t) && TokenKind::Keyword(Kwd::Trait) => Source::token(file, t),
        );

        // We're expecting a name at `ident_idx`
        let name = expect!((
            Ok(t),
            TokenKind::Ident(name) => Ident { src: t.span(file), name: (*name).into() },
            @else { err!() } => ExpectedKind::Ident(IdentContext::TraitDef { kwd_token }),
        ));

        consumed += 1;

        let generics_params = GenericsParams::try_consume(
            file,
            &tokens[consumed..],
            GenericsParamsContext::TraitDef(Source::slice_span(file, &tokens[kwd_idx..consumed])),
            |_| true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;

        consumed += generics_params.consumed();

        // If we find a double-colon ("::") after the trait name with generic parameters, we'll be
        // expecting a type bound.
        let super_traits = expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::DoubleColon) => {
                consumed += 1;

                let bound = TypeBound::consume(
                    file,
                    &tokens[consumed..],
                    ends_early,
                    containing_token,
                    errors,
                ).map_err(ItemParseErr::add(consumed))?;

                consumed += bound.consumed();

                Some(bound)
            },
            _ => None,
            @else { err!() } => ExpectedKind::TraitDefTypeBoundOrImplBody,
        ));

        // For the body of the trait definition, we're either expecting a semicolon or a
        // curly-brace enclosed block.
        let mut body = None;
        expect!((
            Ok(token),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            TokenKind::Tree { delim: Delim::Curlies, inner, .. } => {
                consumed += 1;
                let ends_early = false;

                let (items, poisoned) =
                    Item::parse_all(file, inner, ends_early, Some(token), errors);

                body = Some(ImplBody {
                    src: token.span(file),
                    items,
                    poisoned,
                });
            },
            @else { err!() } => ExpectedKind::TraitDefBody,
        ));

        Ok(TraitDef {
            src: Source::slice_span(file, &tokens[..consumed]),
            proof_stmts,
            vis,
            name,
            generics_params,
            super_traits,
            body,
        })
    }
}
