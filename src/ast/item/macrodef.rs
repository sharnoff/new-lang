use super::*;

/// A macro definition
///
/// This feature is a work-in-progress, and so this type has not yet been defined.
#[derive(Debug, Clone)]
pub struct MacroDef<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    placeholder: (),
}

impl<'a> MacroDef<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<MacroDef<'a>, Option<usize>> {
        todo!()
    }
}
