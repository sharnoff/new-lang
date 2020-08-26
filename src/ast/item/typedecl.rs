use super::*;

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
///            [ "::" TypeBound ] ( ";" | [ "=" ] Type [ ";" ] ) .
/// ```
/// In turn, type declarations may have proof statements, visibility qualifiers, and generic
/// parameters - these all function as expected. The final few elements, however are more complex
/// and typically occupy the most visual space. When inside a trait definition, the [`TypeBound`] is
/// allowed as a method of constraining the set of associated types that are valid - the
/// right-hand-side type is additionally not necessary; providing one instead serves as a default
/// value. When *outside* a trait definition, type bounds are disallowed and the definition must be
/// present.
///
/// Note that visibility qualifiers are not allowed within trait definitions; each item takes the
/// visibility of the parent trait.
///
/// [`TypeBound`]: struct.TypeBound.html
#[derive(Debug, Clone)]
pub struct TypeDecl<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub generic_params: Option<GenericsParams<'a>>,
    pub bound: Option<TypeBound<'a>>,
    pub is_alias: bool,
    pub def: Option<Type<'a>>,
}

impl<'a> TypeDecl<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<TypeDecl<'a>, Option<usize>> {
        todo!()
    }
}
