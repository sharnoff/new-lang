use super::*;
use crate::files::{FileInfo, Span};

/// A type declaration, independent of where it might occur
///
/// Note that this also includes types declarations that might be part of a trait definition, where
/// there may be bounds on the type (and where they might lack a definition). The checks for
/// whether a type declaration is valid are left for later, as part of a separate pass.
///
/// Nevertheless, we'll briefly touch on some of the context-specific semantic validity of type
/// declarations (and what each component signifies).
///
/// The BNF definition for type declarations is:
/// ```text
/// TypeDecl = ProofStmts [ Vis ] "type" Ident [ GenericsParams ]
///            [ "::" TypeBound ] [ [ "=" ] Type ] ";" .
/// ```
/// In turn, type declarations may have proof statements, visibility qualifiers, and generics
/// parameters - these all function as expected. The final few elements are more complex, and
/// typically occupy the majority of the visual space used.
///
/// Within trait definitions, [`TypeBound`]s are allowed for associated types, alongside the
/// `"=" Type` to give a default value. Outside trait definitions, the equals is optional, and
/// indicates type aliasing. It should also be noted that the trailing semicolon may be omitted in
/// cases where the type is given and it is defined using curly braces - i.e. for `enum`s and
/// structs.
///
/// As a final note: the last few pieces are only semantically valid in certain contexts. This is
/// not included in the BNF definition here.
///
/// [`TypeBound`]: ../struct.TypeBound.html
#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub(in crate::ast) src: Span,
    pub proof_stmts: Option<ProofStmts>,
    pub vis: Option<Vis>,
    pub name: Ident,
    pub generics_params: Option<GenericsParams>,
    pub bound: Option<TypeBound>,
    pub is_alias: bool,
    pub ty: Option<Type>,

    consumed: usize,
}

impl Consumed for TypeDecl {
    fn consumed(&self) -> usize {
        self.consumed
    }
}

impl TypeDecl {
    /// Consumes a type declaration as a prefix of the given tokens
    ///
    /// This function operates under the same semantics as [`FnDecl::consume`]; accurate
    /// descriptions of the purpose of each argument can be found there.
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
    ) -> Result<TypeDecl, ItemParseErr> {
        let mut consumed = ident_idx;

        // Because we're starting at `ident_idx`, we only actually need to parse the following BNF
        // equivalent:
        //   Ident [ GenericsParams ] [ "::" TypeBound [ "=" Type ] | [ "=" ] Type ] ";"

        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);
        macro_rules! err {
            () => {{
                return Err(ItemParseErr { consumed });
            }};
        }

        let kwd_tokens = Source::slice_span(file, &tokens[proof_stmts.consumed()..consumed]);

        let name = expect!((
            Ok(t),
            TokenKind::Ident(name) => Ident { src: t.span(file), name: (*name).into() },
            @else { err!() } => ExpectedKind::Ident(IdentContext::FnDeclName(kwd_tokens)),
        ));
        consumed += 1;

        let generics_params = GenericsParams::try_consume(
            file,
            &tokens[consumed..],
            GenericsParamsContext::TypeDecl,
            |_| true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;
        consumed += generics_params.consumed();

        // Next, `[ "::" TypeBound ]`
        let mut bound = None;
        expect!((
            Ok(t),
            TokenKind::Punctuation(Punc::DoubleColon) => {
                consumed += 1;

                let b = TypeBound::consume(
                    file,
                    &tokens[consumed..],
                    ends_early,
                    containing_token,
                    errors,
                ).map_err(ItemParseErr::add(consumed))?;

                consumed += b.consumed();
                bound = Some(b);
            },

            // We'll pass through the allowed next tokens:
            _ if Type::is_starting_token(t) => (),
            TokenKind::Punctuation(Punc::Semi)
            | TokenKind::Punctuation(Punc::Eq) => (),

            // Someone might have left a single colon accidentally - we'll produce a distinct error
            // for this
            @err TokenKind::Punctuation(Punc::Colon) => {
                Error::TypeDeclSingleColonBound { colon: Source::token(file, t) }
            },

            // But if it isn't, we'll produce the appropriate error immediately instead of waiting
            // until later.
            @else { err!() } => ExpectedKind::TypeDeclBoundOrAfter,
        ));

        // After this, we can have an equals:
        let is_alias = match kind!(tokens)(consumed) {
            Some(TokenKind::Punctuation(Punc::Eq)) => true,
            _ => false,
        };

        // And then the type:
        let mut ty = None;
        expect!((
            Ok(t),
            _ if Type::is_starting_token(t) => {
                let t = Type::consume(
                    file,
                    &tokens[consumed..],
                    TypeContext::TypeDecl,
                    Restrictions::default(),
                    ends_early,
                    containing_token,
                    errors,
                ).map_err(ItemParseErr::add(consumed))?;

                consumed += t.consumed();
                ty = Some(t);
            },
            _ if !is_alias => (),
            TokenKind::Punctuation(Punc::Semi) => (),
            @else { err!() } => ExpectedKind::TypeDeclType,
        ));

        let requires_semi = ty
            .as_ref()
            .map(Type::requires_trailing_delim)
            .unwrap_or(true);
        if requires_semi {
            expect!((
                Ok(_),
                TokenKind::Punctuation(Punc::Semi) => consumed += 1,
                @else { err!() } => ExpectedKind::TypeDeclTrailingSemi,
            ));
        } else if let Some(TokenKind::Punctuation(Punc::Semi)) = kind!(tokens)(consumed) {
            // If we didn't require it, but found a trailing semicolon anyways, that's fine.
            consumed += 1;
        }

        Ok(TypeDecl {
            src: Source::slice_span(file, &tokens[..consumed]),
            proof_stmts,
            vis,
            name,
            generics_params,
            bound,
            is_alias,
            ty,
            consumed,
        })
    }
}
