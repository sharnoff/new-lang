//! Types for statement parsing
//!
//! The actual parsing of statments is handled in [`BlockExpr::parse`], because it's only there
//! that the distinction can be made between additional statements and a tail expression inside the
//! block.
//!
//! [`BlockExpr::parse`]: ../expr/struct.BlockExpr.html#method.parse

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Statements                                                                                     //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Stmt<'a> {
    BigExpr(Expr<'a>),
    LittleExpr(LittleExprStmt<'a>),
    Assign(AssignStmt<'a>),
    Item(Item<'a>),
}

#[derive(Debug)]
pub struct LittleExprStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Expr<'a>,
}

#[derive(Debug)]
pub struct AssignStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    assignee: Assignee<'a>,
    op: AssignOp,
    expr: Expr<'a>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Assignee                                                                                     //
// * AssignOp                                                                                     //
////////////////////////////////////////////////////////////////////////////////////////////////////

// AKA lvalue - "Assignee" is more intuitive to people who aren't in the know
#[derive(Debug)]
pub enum Assignee<'a> {
    Deref(PrefixOpExpr<'a>),
    Path(Path<'a>),
}

#[derive(Debug)]
pub enum AssignOp {
    /// `+=`
    Add,
    /// `-=`
    Sub,
    /// `*=`
    Mul,
    /// `/=`
    Div,
    /// `%=`
    Mod,
    /// `&=`
    BitAnd,
    /// `|=`
    BitOr,
    /// `<<=`
    Shl,
    /// `>>=`
    Shr,
    /// `=`
    Eq,
}

impl<'a> Assignee<'a> {
    pub fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Assignee<'a>, Option<usize>> {
        todo!()
    }
}
