use super::*;

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
#[derive(Debug, Clone)]
pub struct ImplBlock<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub trait_impl: Option<Path<'a>>,
    pub impl_ty: Type<'a>,
    pub body: Option<ImplBody<'a>>,
}

#[derive(Debug, Clone)]
pub struct ImplBody<'a> {
    pub(in crate::ast) src: &'a Token<'a>,
    pub items: Vec<Item<'a>>,
}

impl<'a> ImplBlock<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ImplBlock<'a>, Option<usize>> {
        todo!()
    }
}
