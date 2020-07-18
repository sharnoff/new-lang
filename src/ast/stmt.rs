//! Statment parsing

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