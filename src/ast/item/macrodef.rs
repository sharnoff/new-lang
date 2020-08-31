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
        _ends_early: bool,
        _containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        _proof_stmts: Option<ProofStmts<'a>>,
        _vis: Option<Vis<'a>>,
    ) -> Result<MacroDef<'a>, ItemParseErr> {
        let macro_idx = ident_idx - 1;

        errors.push(Error::MacrosUnimplemented {
            macro_kwd: tokens[macro_idx].as_ref().unwrap(),
        });

        Err(ItemParseErr {
            consumed: ident_idx,
        })
    }
}
