use super::*;
use crate::files::{FileInfo, Span};

/// A macro definition
///
/// This feature is a work-in-progress, and so this type has not yet been defined.
#[derive(Debug, Clone, Consumed)]
pub struct MacroDef {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    #[consumed(0)]
    placeholder: (),
}

impl MacroDef {
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ident_idx: usize,
        _ends_early: bool,
        _containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
        _proof_stmts: Option<ProofStmts>,
        _vis: Option<Vis>,
    ) -> Result<MacroDef, ItemParseErr> {
        let macro_idx = ident_idx - 1;

        errors.push(Error::MacrosUnimplemented {
            macro_kwd: Source::from(file, &tokens[macro_idx]),
        });

        Err(ItemParseErr {
            consumed: ident_idx,
        })
    }
}
