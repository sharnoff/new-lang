use super::*;

/// A trait definition
///
/// While these are syntactically allowed within trait definitions, they are not semantically valid
/// in those positions - this is a feature that may be added in the future, but it is not currently
/// planned.
///
/// The BNF for trait definitions is:
/// ```text
/// TraitDef = ProofStmts [ Vis ] "trait" Ident [ GenericParams ] [ "::" TypeBound ] ( ImplBody | ";" ) .
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
#[derive(Debug, Clone)]
pub struct TraitDef<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub proof_stmts: Option<ProofStmts<'a>>,
    pub vis: Option<Vis<'a>>,
    pub name: Ident<'a>,
    pub generic_params: Option<GenericParams<'a>>,
    pub super_traits: Option<TypeBound<'a>>,
    pub body: Option<ImplBody<'a>>,
}

impl<'a> TraitDef<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<TraitDef<'a>, Option<usize>> {
        todo!()
    }
}
