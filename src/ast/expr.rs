//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Expr<'a> {
    Access(AccessExpr<'a>),
    TypeBinding(Box<TypeBindExpr<'a>>),
    PrefixOp(PrefixOpExpr<'a>),
    BinOp(Box<BinOpExpr<'a>>),
    PostfixOp(PostfixOpExpr<'a>),
    Let(Box<LetExpr<'a>>),
    FnCall(FnCallExpr<'a>),
    Struct(StructExpr<'a>),
    Array(ArrayLitExpr<'a>),
    Tuple(TupleExpr<'a>),
    Block(BlockExpr<'a>),
    For(ForExpr<'a>),
    While(WhileExpr<'a>),
    DoWhile(DoWhileExpr<'a>),
    Loop(LoopExpr<'a>),
    If(IfExpr<'a>),
    Match(MatchExpr<'a>),
}

#[derive(Debug)]
pub struct AccessExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    host: Box<Expr<'a>>,
    field: Ident<'a>,
}

#[derive(Debug)]
pub struct TypeBindExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Expr<'a>,
    bind_to: Type<'a>,
}

#[derive(Debug)]
pub struct PrefixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    op: PrefixOp<'a>,
    expr: Box<Expr<'a>>,
}

#[derive(Debug)]
pub struct BinOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    lhs: Expr<'a>,
    op: BinOp<'a>,
    rhs: Expr<'a>,
}

#[derive(Debug)]
pub struct PostfixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Box<Expr<'a>>,
    op: PostfixOp<'a>,
}

#[derive(Debug)]
pub struct LetExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Pattern<'a>,
    ty: Option<Type<'a>>,
    expr: Option<Expr<'a>>,
}

#[derive(Debug)]
pub struct FnCallExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    func: Box<Expr<'a>>,
    generic_args: Option<GenericArgs<'a>>,
    args: StructFieldsExpr<'a>,
}

#[derive(Debug)]
pub struct StructExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    ty_name: Option<Path<'a>>,
    generic_args: Option<GenericArgs<'a>>,
    fields: Option<StructFieldsExpr<'a>>,
}

#[derive(Debug)]
pub struct ArrayLitExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    values: Vec<Expr<'a>>,
}

#[derive(Debug)]
pub struct TupleExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    values: Vec<Expr<'a>>,
}

#[derive(Debug)]
pub struct BlockExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    items: Vec<Stmt<'a>>,
    tail: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct ForExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Pattern<'a>,
    iter: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct WhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pred: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct DoWhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    body: BlockExpr<'a>,
    pred: Box<Expr<'a>>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct LoopExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    body: BlockExpr<'a>,
}

#[derive(Debug)]
pub struct IfExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    condition: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct MatchExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Box<Expr<'a>>,
    arms: Vec<(Pattern<'a>, Expr<'a>)>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Ident                                                                                        //
// * StringLiteral                                                                                //
// * Path                                                                                         //
//   * PathComponent                                                                              //
// * PrefixOp                                                                                     //
//   * PrefixOpKind                                                                               //
// * BinOp                                                                                        //
//   * BinOpKind                                                                                  //
// * PostfixOp                                                                                    //
//   * PostfixOpKind                                                                              //
// * StructFieldsExpr                                                                             //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Copy, Clone)]
pub struct Ident<'a> {
    pub(super) src: &'a Token<'a>,
    pub name: &'a str,
}

#[derive(Debug, Copy, Clone)]
pub struct StringLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    // NOTE: currently, string literals cannot give this; a minor change to `crate::tokens` is
    // required
    pub value: &'a str,
}

#[derive(Debug)]
pub struct Path<'a> {
    pub(super) src: TokenSlice<'a>,
    components: Vec<PathComponent<'a>>,
    tail: Ident<'a>,
}

#[derive(Debug)]
pub struct PathComponent<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    generic_args: Option<GenericArgs<'a>>,
}

#[derive(Debug)]
pub struct PrefixOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: PrefixOpKind,
}

#[derive(Debug)]
pub enum PrefixOpKind {
    /// `"!"`
    Not,
    /// `"-"`
    Minus,
    /// `"&" [ "mut" ]`
    Ref { is_mut: bool },
    /// `"*"`
    Deref,
}

#[derive(Debug)]
pub struct BinOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: BinOpKind,
}

#[derive(Debug)]
pub enum BinOpKind {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Mod,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `^`
    BitXor,
    /// `<<`
    Shl,
    /// `>>`
    Shr,
    /// `&&`
    And,
    /// `||`
    Or,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Le,
    /// `>=`
    Ge,
    /// `==`
    Eq,
    /// `!=`
    Ne,
}

#[derive(Debug)]
pub struct PostfixOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: PostfixOpKind,
}

#[derive(Debug)]
pub enum PostfixOpKind {
    /// `?`
    Try,
}

#[derive(Debug)]
pub struct StructFieldsExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    fields: Vec<(Ident<'a>, Option<Expr<'a>>)>,
}
