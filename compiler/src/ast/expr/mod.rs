//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;
use crate::files::{FileInfo, Span};
use crate::tokens::LiteralKind;

mod stack;
use stack::Stack;
mod restrictions;
pub use restrictions::Restrictions;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Consumed)]
pub enum Expr {
    Literal(Literal),
    Named(PathComponent),
    PrefixOp(Box<PrefixOpExpr>),
    BinOp(Box<BinOpExpr>),
    PostfixOp(PostfixOpExpr),
    Struct(StructExpr),
    Array(ArrayExpr),
    Tuple(TupleExpr),
    Block(BlockExpr),
    AmbiguousBlock(AmbiguousBlockExpr),
    For(ForExpr),
    While(WhileExpr),
    DoWhile(DoWhileExpr),
    Loop(LoopExpr),
    If(IfExpr),
    Match(MatchExpr),
    Continue(ContinueExpr),
}

/// The types of delimeters that may occur around expression parsing
///
/// The outer delimiter context is useful in a couple cases: firstly for
/// [`Expr::consume_delimited`] in optionally pairing with names, but secondly for producing better
/// error messages with the ambiguity around generics arguments.
///
/// For example, when parsing as part of some struct fields, we might find that the user has
/// erroneously written:
/// ```text
/// { foo: Bar<T, size + 2> }
/// ```
/// It's likely that the user meant to instead write:
/// ```text
/// { foo: Bar<(T, size + 2)> }
/// ```
/// so that `size + 2` is a generics argument. We can deduce this because `size +` cannot start a
/// struct field, but *can* start a generics argument.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ExprDelim {
    /// Expressions that occur within tuple or array literals
    Comma,
    /// Expressions that occur within struct instantiation
    StructFields,
    /// Expressions that occur as part of function arguments
    FnArgs,
    Nothing,
}

/// A helper type for consuming certain arrangements of expressions with
/// [`Expr::consume_delimited`]
///
/// A single `Delimited` serves to represent an expression that may or may not be named. The
/// primary usag of this type is by implementing `From<Delimited>` which allows the desired type to
/// be returned in a list from that function.
///
/// This type always upholds that at least one of the two non-source fields will have a value. In
/// the event of a conflict (e.g. finding `.., foo, ..` as part of a list), the variant of
/// [`ExprDelim`] passed in will be used to disambiguate.
///
/// [`Expr::consume_delimited`]: enum.Expr.html#method.consume_delimited
/// [`ExprDelim`]: enum.ExprDelim.html
#[derive(Consumed)]
pub struct Delimited {
    // The middle ":"
    #[consumed(if name.is_some() && value.is_some() { 1 } else { 0 })]
    pub(super) src: Span,
    name: Option<Ident>,
    value: Option<Expr>,
}

/// A prefix-operator expression, given by the operator and the right-hand-side expression
///
/// The operator is given by a [`PrefixOp`] and its source. The relevant BNFs definitions are:
/// ```text
/// PrefixOpExpr = PrefixOp Expr .
/// PrefixOp     = "!" | "-" | "&" [ "mut" ] | "*" | LetPrefix | "break" | "return".
/// LetPrefix    = "let" Pattern [ ":" Type ] "="
/// ```
///
/// There are no publicly-exposed functions to produce prefix-operator expressions - this is
/// because expression parsing is a complex beast that is managed through a key selection of
/// methods on [`Expr`].
///
/// [`PrefixOp`]: enum.PrefixOp.html
/// [`Expr`]: enum.Expr.html
#[derive(Debug, Clone, Consumed)]
pub struct PrefixOpExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub op_src: Span,
    pub op: PrefixOp,
    pub expr: Box<Expr>,
}

/// The different prefix operators available for expressions
///
/// This is defined by the following BNF:
/// ```text
/// PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" .
/// ```
///
/// For more information, see [`PrefixOpExpr`](struct.PrefixOpExpr.html).
#[derive(Debug, Clone, Consumed)]
pub enum PrefixOp {
    /// `"!"`
    #[consumed(1)]
    Not,
    /// `"-"`
    #[consumed(1)]
    Minus,
    /// `"&" [ "mut" ]`
    #[consumed(if *is_mut { 2 } else { 1 })]
    Ref { is_mut: bool },
    /// `"*"`
    #[consumed(1)]
    Deref,
    /// "let" Pattern [ ":" Type ] "="
    #[consumed(1 + _0.consumed() + _1.as_ref().map(|t| t.consumed() + 1).unwrap_or(0) + 1)]
    Let(Pattern, Option<Type>),
    /// `"break"`
    #[consumed(1)]
    Break,
    /// `"return"`
    #[consumed(1)]
    Return,
}

/// A binary-operator expression, given by the operator and the expressions on either side
///
/// The operator is given by a [`BinOp`] and its source. The relevant BNF definitions are:
/// ```text
/// BinOpExpr = Expr BinOp Expr .
/// BinOp = "+" | "-" | "*" | "/" | "%"
///       | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
///       | "<" | ">" | "<=" | ">=" | "==" | "!="
///       | "+=" | "-=" | "*=" | "/=" | "%="
///       | "&=" | "|=" | "<<=" | ">>=" | "=" .
/// ```
///
/// Operator precedence is given by the [`BindingPower`] enum, represented by the internal comments
/// within it.
///
/// There are no publicly-exposed functions to produce binary-operator experssions - this is
/// because expression parsing is a complex beast that is managed through a key selection of
/// methods on [`Expr`].
///
/// [`BinOp`]: enum.BinOp.html
/// [`BindingPower`]: enum.BindingPower.html
/// [`Expr`]: enum.Expr.html
#[derive(Debug, Clone, Consumed)]
pub struct BinOpExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub lhs: Expr,
    #[consumed(@ignore)]
    pub op_src: Span,
    pub op: BinOp,
    pub rhs: Expr,
}

/// The different binary operators available for expressions
///
/// These are defined by the following BNF:
/// ```text
/// BinOp = "+" | "-" | "*" | "/" | "%"
///       | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
///       | "<" | ">" | "<=" | ">=" | "==" | "!=" .
/// ```
#[derive(Debug, Copy, Clone)]
pub enum BinOp {
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
    LogicalAnd,
    /// `||`
    LogicalOr,
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
    /// `+=`
    AddAssign,
    /// `-=`
    SubAssign,
    /// `*=`
    MulAssign,
    /// `/=`
    DivAssign,
    /// `%=`
    ModAssign,
    /// `&=`
    BitAndAssign,
    /// `|=`
    BitOrAssign,
    /// `<<=`
    ShlAssign,
    /// `>>=`
    ShrAssign,
    /// `=`
    Assign,
}

/// A postfix-operator expression, given by the operator and the expression to its left.
///
/// Note that *many* types of expressions are included by this that would not typically be
/// considered "postfix" operators. For example, function calls are listed here. The related BNF
/// definitions help to shed some light on this:
/// ```text
/// PostfixOpExpr = Expr PostfixOp .
/// PostfixOp = "[" Expr "]"                # Indexing
///           | "." Ident [ GenericsArgs ]   # Field access / method calls
///           | "." IntLiteral              # Tuple indexing
///           | FnArgs                      # Function calls
///           | "{" StructFieldsExpr "}"    # Named structs
///           | "~" Type                    # Type binding
///           | "is" Pattern                # Pattern equivalence
///           | "?"                         # "try" operator
/// ```
/// The operator is given by a [`PostfixOp`], and its source stored separately.
///
/// There are no publicly-exposed functions to produce postfix-operator expressions - this is
/// because expression parsing is a complex beast that is managed through a key selection of
/// methods on [`Expr`].
///
/// [`PostfixOp`]: enum.PostfixOp.html
/// [`Expr`]: enum.Expr.html
#[derive(Debug, Clone, Consumed)]
pub struct PostfixOpExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub expr: Box<Expr>,
    pub op: PostfixOp,
    #[consumed(@ignore)]
    pub op_src: Span,
}

/// The different types of postfix operators available
///
/// There's complex behavior that's allowed here, which is mostly detailed in the documentation for
/// [`PostfixOpExpr`].
///
/// [`PostfixOpExpr`]: struct.PostfixOpExpr.html
#[derive(Debug, Clone, Consumed)]
pub enum PostfixOp {
    /// `"[" Expr "]"`
    ///
    /// The boolean indicates whether the expression may have been poisoned
    #[consumed(1)]
    Index(Box<Expr>, bool),
    /// `"." Ident [ GenericsArgs ]`
    #[consumed(_0.consumed() + 1)]
    Access(PathComponent),
    /// `"." IntLiteral`
    #[consumed(_0.consumed() + 1)]
    TupleIndex(IntLiteral),
    /// `"(" [ FnArg { "," FnArg } [ "," ] ] ")"`
    ///
    /// The boolean indicates whether the values have been poisoned
    #[consumed(1)]
    FnCall(Vec<FnArg>, bool),
    /// `StructExpr`
    #[consumed(1)]
    NamedStruct(StructExpr),
    /// `"~" Type`
    #[consumed(_0.consumed() + 1)]
    TypeBinding(Box<Type>),
    /// `"is" Pattern`
    #[consumed(_0.consumed() + 1)]
    IsPattern(Pattern),
    /// `"?"`
    #[consumed(1)]
    Try,
}

/// A single function argument; a helper type for [`PostfixOp::FnCall`]
///
/// Individual function arguments are defined by the following BNF:
/// ```text
/// FnArg = [ Ident ":" ] Expr .
/// ```
/// There are semantics regarding the types of expressions allowed here and under which
/// circumstances (e.g. writing `f(y, x)` for `fn f(x: _, y: _)` is illegal), but those are too
/// complex to be described here.
///
/// [`PostfixOp::FnCall`]: enum.PostfixOp.html#variant.FnCall
#[derive(Debug, Clone, Consumed)]
pub struct FnArg {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(name.as_ref().map(|i| i.consumed() + 1).unwrap_or(0))] // +1 for trailing ":"
    pub name: Option<Ident>,
    pub value: Expr,
}

/// An anonymous struct expression, given on its own as an atom or available as a postfix operator
///
/// The fields are individually given by [`StructFieldExpr`]s. The relevant BNF definitions are:
/// ```text
/// StructExpr = "{" [ StructFieldExpr { "," StructFieldExpr } [ "," ] ] "}" .
/// StructFieldExpr = Ident [ ":" Expr* ] .
/// ```
/// Like Rust, the expresion used in assignment for the struct definition may be omitted; this is
/// syntax sugar for assigning to a field the value of a local variable with the same name.
///
/// Struct expressions are used in two ways - both as an atomic expression to represent anonymous
/// struct initialization and as a postfix operator to have named struct initialization. The
/// postfix representation is selectively disallowed in certain places (e.g. `if` conditions) due
/// to the ambiguity it causes.
///
/// One final piece to note about the expressions assigned to the field is that they do not allow
/// assignment operators (e.g. `=`, `+=`, etc.). This is to reduce ambiguity in cases where a
/// construct may already be either a struct type or expression.
///
/// [`StructFieldExpr`]: struct.StructFieldExpr.html
#[derive(Debug, Clone, Consumed)]
pub struct StructExpr {
    #[consumed(1)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub fields: Vec<StructFieldExpr>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A single field of a struct expression
///
/// The BNF definition for this is:
/// ```text
/// StructFieldExpr = Ident [ ":" Expr ] .
/// ```
///
/// For more information, see [`StructExpr`](#struct.StructExpr.html).
#[derive(Debug, Clone, Consumed)]
pub struct StructFieldExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub name: Ident,
    #[consumed(value.as_ref().map(|i| i.consumed() + 1).unwrap_or(0))] // +1 for leading ":"
    pub value: Option<Expr>,
}

/// An array literal, given by a comma-separated list of the elements
///
/// The BNF definition for these is:
/// ```text
/// ArrayExpr = "[" [ Expr { "," Expr } [ "," ] ] "]" .
/// ```
///
/// Like tuple literals, possible syntax ambiguities here mean that we might not know exactly how
/// many elements are represented here before type checking.
#[derive(Debug, Clone, Consumed)]
pub struct ArrayExpr {
    #[consumed(1)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub values: Vec<Expr>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A tuple literal, given by a comma-separated list of the elements
///
/// The BNF definition for tuple literals is nearly identical to [array literals]
/// ```text
/// TupleExpr = "(" [ Expr { "," Expr } [ "," ] ] ")" .
/// ```
///
/// Like array literals, possible syntax ambiguities here mean that we might not know exactly how
/// many elements are represented here before type checking.
///
/// [array literals]: struct.ArrayExpr.html
#[derive(Debug, Clone, Consumed)]
pub struct TupleExpr {
    #[consumed(1)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub values: Vec<Expr>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A curly-brace enclosed block, containing a list of statments with an optional tail expression
///
/// Block expressions are fairly simple by themselves (they are composed of complex constructs),
/// and are defined by the following BNF:
/// ```text
/// BlockExpr = "{" { Stmt } [ Expr ] "}" .
/// ```
#[derive(Debug, Clone, Consumed)]
pub struct BlockExpr {
    #[consumed(1)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub stmts: Vec<Stmt>,
    #[consumed(@ignore)]
    pub tail: Option<Box<Expr>>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A single statement available within block expressions
///
/// This is defined by the following BNF:
/// ```text
/// Stmt = BigExpr
///      | Expr ";"
///      | Item
/// ```
#[derive(Debug, Clone, Consumed)]
pub enum Stmt {
    BigExpr(Expr),
    Little(LittleExpr),
    Item(Item),
    #[consumed(1)]
    UnnecessarySemi(Span),
}

/// This is a thin wrapper type around a semicolon-terminated expression used as a statement so
/// that we can include the semicolon in the source as well
///
/// Please note that in certain conditions, the semicolon may *not* be included - this may occur
/// with missing semicolons where we still want to produce the expression that we parsed.
#[derive(Debug, Clone, Consumed)]
pub struct LittleExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub expr: Expr,
    /// A marker to indicate whether the expression may have been poisoned by lacking a trailing
    /// semicolon where one was expected
    #[consumed(if *poisoned { 0 } else { 1 })]
    pub poisoned: bool,
}

/// A block expression or single-field anonymous struct initialization
///
/// This is of a few forms of ambiguity that cannot be resolved at parse-time, and always has the
/// form of `"{" [ Ident ] "}"`. This could either be a anonymous struct initialization with the field
/// name abbreviation OR a block expression where the tail expression is the single identifier.
///
/// It is represented by the containing token.
#[derive(Debug, Clone, Consumed)]
pub struct AmbiguousBlockExpr {
    #[consumed(1)]
    pub(super) src: Span,
    #[consumed(@ignore)]
    pub name: Option<Ident>,
}

/// A single `for` expression for loops with iterators
///
/// These are standard, and function as would normally be expected. The BNF definition is:
/// ```text
/// ForExpr = "for" Pattern "in" Expr BlockExpr [ "else" BigExpr ] .
/// ```
/// `for` loops may be followed by an `else` branch, which is executed only if the iterator is
/// exhausted. The `Pattern` given by the iterator must be infallible.
///
/// Note that `for` expressions are part of the `BigExpr` group, which allows expressions in
/// certain places - e.g. inside an `else` branch or as a statement (without a trailing `;`).
#[derive(Debug, Clone, Consumed)]
pub struct ForExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(1 + pat.consumed() + 1)] // "for" pat "in"
    pub pat: Pattern,
    pub iter: Box<Expr>,
    pub body: BlockExpr,
    pub else_branch: Option<Box<ElseBranch>>,
}

/// Conditional loops
///
/// These are standard, and function as would normally be expected in any similar language. The BNF
/// definition is:
/// ```text
/// WhileExpr = "while" Expr BlockExpr [ "else" BigExpr ] .
/// ```
/// `while` loops may be followed by an `else` branch, which is executed only if the condition at
/// the head of the loop evalutes to false. If the loop is terminated through other means (e.g. by
/// breaking out of it), then the `else` branch will not be executed.
///
/// Note that `while` expressions are part of the `BigExpr` group.
#[derive(Debug, Clone, Consumed)]
pub struct WhileExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(1 + condition.consumed())] // +1 for leading "while" keyword
    pub condition: Box<Expr>,
    pub body: BlockExpr,
    pub else_branch: Option<Box<ElseBranch>>,
}

/// "Do-while" loops
///
/// These are similar to C-style "do-while" loops, with the notable exceptions that (1) the
/// trailing condition may use variables defined inside the loop body and (2) like other loops
/// here, it may be followed by an [else branch]. The BNF for these is defined as:
/// ```text
/// DoWhileExpr = "do" BlockExpr "while" Expr [ "else" BigExpr ] .
/// ```
///
/// [else branch]: struct.ElseBranch.html
#[derive(Debug, Clone, Consumed)]
pub struct DoWhileExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(1 + body.consumed() + 1)] // "do" body "while"
    pub body: BlockExpr,
    pub pred: Box<Expr>,
    pub else_branch: Option<Box<ElseBranch>>,
}

/// Infinite loops
///
/// These may only be escaped by breaking out of the loop or returning from the containing function.
/// Loop expressions are defined by the following BNF definition:
/// ```text
/// LoopExpr = "loop" BlockExpr .
/// ```
///
/// Because there cannot be a condition for these loops, there is also no corresponding else branch
/// permitted.
#[derive(Debug, Clone, Consumed)]
pub struct LoopExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(body.consumed() + 1)]
    pub body: BlockExpr,
}

/// Conditional `if` expressions
///
/// `if` expressions provide the body after the condition only if that condition evaluates to true
/// - because of this, using the value of an `if` expression requires either that the condition is
/// infallible or that it has a trailing [else branch]. `if` expressions are given by the following
/// BNF definition:
/// ```text
/// IfExpr = "if" Expr* BlockExpr [ "else" BigExpr ] .
/// ```
#[derive(Debug, Clone, Consumed)]
pub struct IfExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(1 + condition.consumed())] // +1 for leading "if" keyword
    pub condition: Box<Expr>,
    pub body: BlockExpr,
    pub else_branch: Option<Box<ElseBranch>>,
}

/// `match` expressions
///
/// `match` expressions provide a way to execute branches conditional on successful destructuring
/// of a certain determinant expression with a pattern. These expressions are defined by the
/// following relevant BNFs:
/// ```text
/// MatchExpr = "match" Expr "{" { MatchArm } "}" .
/// MatchArm  = Pattern [ "if" Expr ] "=>" ( Expr "," | BigExpr ) .
/// ```
#[derive(Debug, Clone, Consumed)]
pub struct MatchExpr {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(1 + expr.consumed())] // +1 for leading "match" keyword
    pub expr: Box<Expr>,
    #[consumed(1)]
    pub arms: Vec<MatchArm>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A single `match` arm; a helper type for [`MatchExpr`](#struct.MatchExpr.html)
#[derive(Debug, Clone, Consumed)]
pub struct MatchArm {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(pat.consumed() + 1)] // +1 for trailing "=>"
    pub pat: Pattern,
    #[consumed(cond.as_ref().map(|e| 1 + e.consumed()).unwrap_or(0))] // +1 for "if"
    pub cond: Option<Expr>,
    pub eval: Expr,
}

/// A `continue` expression, to go to the next iteration of a loop
///
/// This is essentially a wrapper type for the single-token source (the keyword `continue`), as a
/// placeholder for more complex syntax that may be added later.
#[derive(Debug, Clone, Consumed)]
pub struct ContinueExpr {
    #[consumed(1)]
    pub(super) src: Span,
}

binding_power! {
    /// All of the available operators, with an implementation of `Ord` to specify their relative
    /// binding power.
    ///
    /// Please note that variants with equivalent binding power are treated as equal by the
    /// implementations of `Ord` and `Eq`.
    ///
    /// The implementation of `Ord` is defined by the macro generating this type - for more
    /// information on relative precedence between the variants here, please refer to the internal
    /// comments on the source for this type. If you wish to do so, the `src` link unfortunately
    /// does not link to the macro usage, but to the definition - the actual source can be found by
    /// searching for "enum BindingPower" inside 'src/ast/expr.rs'.
    //
    // Internal documentation! The best kind ~
    //
    // The macro is defined so that we give each level of binding power in decreasing order, with
    // variants delimited by commas *within* the levels, and the levels delimited by semicolons.
    // There's commentary on each of the sections below, with reference to other languages.
    #[derive(Debug, Copy, Clone)]
    pub enum BindingPower {
        // // A reserved binding power primarily for internal use as a way of signifying the highest
        // // binding power, plus one.
        // ReservedHighest;

        // (Almost) All of the postfix operators have the highest binding power, because (almost)
        // all of them should apply before any prefix operators. The only one we leave is type
        // binding, because it is typically written with spaces around it, unlike the others.
        Index, Access, TupleIndex, FnCall, NamedStruct, Try;

        // After them, we have the the prefix operators, all of which are present here.
        Not, Minus, Ref, Deref;

        // And then we add back in the remaining postfix operators - type binding and pattern
        // equivalence, for the reason given above.
        TypeBinding, IsPattern;

        // After the operators that are nearly all in a row, we have the multiplication operators
        Mul, Div, Mod;
        // Followed by addition/subtraction
        Add, Sub;
        // And then with bitshifts taking the rear.
        //
        // The decision for what precedence to give the bitshift operators is not simple. Indeed,
        // there is no standard answer across languages. For example, Rust and Python, and
        // JavaScript both put the precedence in exactly this place (which is part of the reason for
        // this choice), but Go places it with the multiplication operators (along with bitwise
        // AND), and Swift even places it above them!
        //
        // Even with all that, the bitshift operators were placed here simply because they occupy a
        // large amount of space, so a user might visually intuit them to be lower precedence than
        // smaller operators, e.g. addition/subtraction.
        Shl, Shr;

        // After bitshifts, we have the other bit operators. Python, Rust, and JavaScript all have
        // this distinction (albeit with JS placing these after comparison operators).
        BitAnd;
        BitXor;
        BitOr;
        // ^ A note for future changes: A large chunk of the disambiguation used in
        // `Expr::consume_path_component` relies on `BitOr` having higher binding power than the
        // comparison operators.

        // We then only have the comparison operators left. Some langauges (Python, Rust, Go, Swift,
        // etc.) place all of these on the same level. JavaScript, however, does something neat
        // that we'd like to copy here - the relational comparison operators ('<', '<=', '>=', '>')
        // are given higher precedence than the equality operators ('==', '!='). This *would* make a
        // lot of sense here, if we didn't provide the relational comparison operators for
        // booleans. Because/if we do, we don't want to have any gotchas for users, so we'll do
        // what everyone else does and lump them all in together.
        Eq, Ne, Lt, Le, Ge, Gt;

        // "Let" expressions have precedence higher than logical AND or OR, so we give them their
        // own binding power, just so they know they're special :)
        Let;

        // Logical OR and AND are given particularly low binding power so that `let` can bind more
        // tightly than them. AND binds more tightly than OR (per precedent set by other
        // languages), and so we give them unique levels:
        LogicalAnd;
        LogicalOr;

        // Below the rest of the binary operators, we have assignment!
        AddAssign, SubAssign, MulAssign, DivAssign, ModAssign, BitAndAssign, BitOrAssign, ShlAssign,
        ShrAssign, Assign;

        // We finish up the list with `break` and `return` as prefix operators
        Break, Return;

        // A reserved binding power primarily for internal use as a way of signifying the lowest
        // binding power, minus one.
        ReservedLowest;
    }
}

/// The direction in which operators are associative
///
/// This is defined so that a select few operators may be right-associative, namely assignment
/// operators.
enum Fixity {
    /// A marker for left-associative operators. This implies that for some operator `*`,
    /// `x * y * z` is equivalent to `(x * y) * z`.
    ///
    /// Most operators are left-associative
    Left,

    /// A marker for right-associative operators. This implies that for some operator `*`,
    /// `x * y * z` is equivalent to `x * (y * z)`.
    ///
    /// The only operators that are right-associative are assignment operators
    Right,
}

impl Expr {
    /// Consumes a single expression, within the given delimited context for the expression
    ///
    /// The additional boolean flag `allow_angle_bracket` is for disallowing comparison (and
    /// bitshifts) in single-expression generics arguments.
    pub fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Expr, Option<usize>> {
        Expr::consume_until(
            file,
            tokens,
            |_| false,
            delim,
            restrictions,
            ends_early,
            containing_token,
            errors,
        )
    }

    /// A helper function to allow ending parsing early if a certain condition is satisfied
    ///
    /// Note that this does not affect the behavior on ending parsing due to
    fn consume_until(
        file: &FileInfo,
        tokens: TokenSlice,
        is_done: impl Fn(&Stack) -> bool,
        delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Expr, Option<usize>> {
        let is_done = |stack: &Stack| {
            if is_done(stack) {
                return true;
            } else if let Some(ex) = stack.last_expr.as_ref() {
                return match ex {
                    Expr::DoWhile(_) => true,
                    _ => false,
                };
            }

            false
        };

        let mut stack = Stack::new();
        let mut consumed = 0;

        loop {
            if !stack.is_empty() && is_done(&stack) {
                break;
            }

            let src = &tokens[consumed..];

            let res = match stack.expecting() {
                stack::Expecting::AtomOrPrefix => Expr::try_consume_atom_or_prefix(
                    &mut stack,
                    file,
                    src,
                    consumed,
                    delim,
                    restrictions,
                    ends_early,
                    containing_token,
                    errors,
                ),
                stack::Expecting::BinOpOrPostfix => {
                    debug_assert!(!stack.is_empty());
                    Expr::try_consume_binop_or_postfix(
                        &mut stack,
                        file,
                        src,
                        consumed,
                        delim,
                        restrictions,
                        ends_early,
                        containing_token,
                        errors,
                    )
                }
            };

            match res {
                Ok(Some(c)) => consumed += c,
                Ok(None) if stack.requires_more() => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::ExprLhs,
                        found: match tokens.get(consumed) {
                            Some(res) => Source::from(file, res),
                            None => end_source!(file, containing_token),
                        },
                    });

                    return Err(None);
                }
                Ok(None) => break,
                Err(None) => return Err(None),
                Err(Some(c)) => return Err(Some(c + consumed)),
            }
        }

        Ok(stack.finish())
    }

    /// Attempts to consume an atomic expression or a prefix operator, returning `None` if the
    /// first token does not constitute either of these
    ///
    /// On success, the number of tokens consumed will be returned.
    ///
    /// `already_consumed` indicates the place in the original consumed expression `tokens` starts,
    /// in order for us to pass it along to the stack values.
    ///
    /// Like most parsing functions, a return value of `Err(Some)` indicates the number of tokens
    /// that were consumed in the event of an error; a return of `Err(None)` indicates that parsing
    /// within the current token tree should immediately stop.
    fn try_consume_atom_or_prefix(
        stack: &mut Stack,
        file: &FileInfo,
        tokens: TokenSlice,
        already_consumed: usize,
        delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<usize>, Option<usize>> {
        match tokens.first() {
            Some(Err(_)) | None => Ok(None),
            Some(Ok(_)) => {
                // First, we'll see if we can parse a prefix operator here
                let res = PrefixOp::try_consume(file, tokens, ends_early, containing_token, errors);
                match res {
                    Ok(None) => (),
                    Ok(Some((op, op_src))) => {
                        let consumed = op.consumed();
                        stack.push_prefix(op, op_src);
                        return Ok(Some(consumed));
                    }
                    Err(e) => return Err(e),
                }

                // If we can't, we'll try to parse an "atomic" expression - these can be loosely
                // defined as all of the expression types that don't involve operators.
                let res = Expr::try_consume_atom(
                    file,
                    tokens,
                    restrictions.with_do_while(DoWhileExpr::is_allowed(stack)),
                    delim,
                    ends_early,
                    containing_token,
                    errors,
                );
                match res {
                    Ok(None) => (),
                    Ok(Some(atom)) => {
                        let consumed = atom.consumed();
                        stack.push_atom(atom);
                        return Ok(Some(consumed));
                    }
                    Err(e) => return Err(e),
                }

                // If we couldn't parse a prefix expression or an atom, we'll indicate that we
                // couldn't find anything
                Ok(None)
            }
        }
    }

    /// Attempts to consume an atomic expression, returning the number of tokens consumed on
    /// success
    ///
    /// `already_consumed` indicates the place in the original consumed expression `tokens` starts,
    /// in order for us to pass it along to the stack values.
    fn try_consume_atom(
        file: &FileInfo,
        tokens: TokenSlice,
        restrictions: Restrictions,
        delim: ExprDelim,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<Expr>, Option<usize>> {
        // Atomic expressions are defined as any of:
        //   AtomicExpr = Literal | PathComponent | StructExpr | ArrayExpr | TupleExpr | BlockExpr
        //              | ForExpr | WhileExpr | LoopExpr | IfExpr | MatchExpr | DoWhileExpr
        //              | ContinueExpr .
        // We'll examine the first token to determine what type of expression we're looking at. If
        // we can't find anything that matches, we'll return `Ok(None)`.
        //
        // There's a little bit of handling further down the expression list: `do..while`
        // expressions are only allowed in certain contexts, and sometimes expressions with else
        // branches (i.e. "if", "while", "for", and "do..while") aren't allowed.

        use Delim::{Curlies, Parens, Squares};

        // A helper macro for some of the repetetive cases near the bottom of the match expression
        macro_rules! consume {
            ($ty:ident, $var:ident) => {{
                $ty::consume(file, tokens, ends_early, containing_token, errors)
                    .map(|e| Some(Expr::$var(e)))
            }};
        }

        match tokens.first() {
            Some(Err(_)) | None => Ok(None),
            // We'll go through each starting token that we listed above, in turn
            Some(Ok(fst_token)) => match &fst_token.kind {
                // Literal
                TokenKind::Literal(_, _) => {
                    Literal::consume(file, tokens).map(|e| Some(Expr::Literal(e)))
                }

                // Named
                TokenKind::Ident(_) => Expr::consume_path_component(
                    file,
                    tokens,
                    delim,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(|e| Some(Expr::Named(e))),

                // StructExpr or BlockExpr
                TokenKind::Tree {
                    delim: Curlies,
                    inner,
                    ..
                } => Expr::parse_curly_block(file, fst_token, inner, errors, tokens)
                    .map(Some)
                    .map_err(|()| Some(1)),

                // ArrayExpr
                TokenKind::Tree {
                    delim: Squares,
                    inner,
                    ..
                } => ArrayExpr::parse(file, fst_token, inner, errors)
                    .map(|e| Some(Expr::Array(e)))
                    .map_err(|()| Some(1)),

                // TupleExpr
                TokenKind::Tree {
                    delim: Parens,
                    inner,
                    ..
                } => TupleExpr::parse(file, fst_token, inner, errors)
                    .map(|e| Some(Expr::Tuple(e)))
                    .map_err(|()| Some(1)),

                // If we find an expression that may have a trailing "else" branch where we aren't
                // allowing it, we'll produce an error
                TokenKind::Keyword(kwd @ Kwd::For)
                | TokenKind::Keyword(kwd @ Kwd::While)
                | TokenKind::Keyword(kwd @ Kwd::If)
                | TokenKind::Keyword(kwd @ Kwd::Do)
                    if !restrictions.allows_else_branch() =>
                {
                    errors.push(Error::PotentialElseDisallowed {
                        src: Source::token(file, fst_token),
                        kwd: *kwd,
                    });

                    Err(None)
                }

                TokenKind::Keyword(Kwd::For) => consume!(ForExpr, For),
                TokenKind::Keyword(Kwd::While) => consume!(WhileExpr, While),
                TokenKind::Keyword(Kwd::Loop) => consume!(LoopExpr, Loop),
                TokenKind::Keyword(Kwd::If) => consume!(IfExpr, If),
                TokenKind::Keyword(Kwd::Match) => consume!(MatchExpr, Match),
                TokenKind::Keyword(Kwd::Continue) => consume!(ContinueExpr, Continue),

                TokenKind::Keyword(Kwd::Do) if !restrictions.allow_do_while => {
                    errors.push(Error::DoWhileDisallowed {
                        do_token: Source::token(file, fst_token),
                    });

                    Err(None)
                }

                TokenKind::Keyword(Kwd::Do) => consume!(DoWhileExpr, DoWhile),

                _ => Ok(None),
            },
        }
    }

    /// Parses a curly-brace enclosed block as an atomic expression
    ///
    /// This function handles dispatching between `BlockExpr::parse` and `StructFieldsExpr::parse`
    /// depending on the content of the block. In ambiguous cases (e.g. when we have the input
    /// `{ x }`), `Expr::AmbiguousBlock` is returned instead.
    fn parse_curly_block(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
        outer_src: TokenSlice,
    ) -> Result<Expr, ()> {
        let kinds = inner
            .iter()
            .take_while(|res| res.is_ok())
            .map(|t| &t.as_ref().unwrap().kind)
            .take(2)
            .collect::<Vec<_>>();

        use TokenKind::Punctuation;

        match &kinds as &[_] {
            // There's two fully ambiguous cases. The first is when there's nothing inside of the
            // block...
            [] => Ok(Expr::AmbiguousBlock(AmbiguousBlockExpr {
                src: src.span(file),
                name: None,
            })),
            // ... and the second is when there's just a single identifier inside
            [&TokenKind::Ident(name)] => {
                let name = Some(Ident {
                    src: Source::from(file, &inner[0]).span,
                    name: (*name).into(),
                });

                Ok(Expr::AmbiguousBlock(AmbiguousBlockExpr {
                    src: src.span(file),
                    name,
                }))
            }

            // If the second token is either a colon or a comma, it must be a struct instantiation
            // that we're parsing. We'll use `StructFieldsExpr::parse` to do so.
            [TokenKind::Ident(_), Punctuation(Punc::Colon)]
            | [TokenKind::Ident(_), Punctuation(Punc::Comma)] => {
                StructExpr::parse(file, src, inner, errors).map(Expr::Struct)
            }

            // Otherwise, this is *most likely* a block expression (if not, it's invalid).
            // We'll give EOF as the source because it's only used in cases where the token source
            // is None, which we can clearly see is not the case here.
            _ => BlockExpr::parse(file, outer_src.first(), false, Source::eof(file), errors)
                .map(Expr::Block),
        }
    }

    /// Consumes a single path component that may be part of an expression
    ///
    /// This function expects that the first token provided is an identifier, and will panic if
    /// this is not the case.
    ///
    /// The delimited context here is provided so that better error messages can be given on
    /// failure. (NOTE: Currently unimplemented)
    pub(super) fn consume_path_component(
        file: &FileInfo,
        tokens: TokenSlice,
        _delim: ExprDelim,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<PathComponent, Option<usize>> {
        let name = assert_token!(
            tokens.first() => "identifier",
            Ok(t) && TokenKind::Ident(name) => Ident { src: t.span(file), name: (*name).into() },
        );

        // We'll only attempt to consume generics arguments if we have an angle bracket after the
        // initial name.
        //
        // To help us out here, we'll define a helper macro to return the path component that only
        // includes the identifier.
        macro_rules! return_name {
            () => {{
                return Ok(PathComponent {
                    src: Source::slice_span(file, &tokens[..1]),
                    name,
                    generics_args: None,
                });
            }};
        }

        // Now, we'll check that we have a "<" token following the name. Because we *also* require
        // that the tokens after it be able to start an expression (or type), we need to ensure
        // that they won't have been part of a binary operator *other than "<"*.
        //
        // Essentially: We'll only continue (and try to parse generics args) if we find the
        // less-than binary operator. Other operators, like "<=" or "<<" cannot be used because the
        // trailing "<" or "=" can't start an expression.
        match BinOp::try_consume(file, &tokens[1..], Restrictions::default()) {
            Some((BinOp::Lt, _)) => (),
            _ => return_name!(),
        }

        // `generics_start` includes the leading angle-bracket
        let generics_start = 1;
        let mut consumed = 2;
        let mut local_errors = Vec::new();

        // All expressions can constitute a valid prefix of generics arguments if necessary, so
        // we'll just use the parsing function provided by 'ast/types' to handle this.
        //
        // If we eventually determine that the angle bracket we found earlier wasn't for generics,
        // we don't want any errors generated by `GenericsArgs::consume_inner` to actually be given
        // to the user; we aren't actually expecting generics arguments.
        //
        // To do this, we'll create `local_errors` so that we only add errors to the main list if
        // we use the output of `GenericsArgs::consume_inner`.
        let generics_args_res = GenericsArgs::consume_inner(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            &mut local_errors,
        );
        let (args, poisoned) = match generics_args_res {
            Ok((args, poisoned, c)) => {
                consumed += c;
                (args, poisoned)
            }
            Err(None) => {
                errors.extend(local_errors);
                return Err(None);
            }
            Err(Some(c)) => {
                consumed += c;
                (Vec::new(), true)
            }
        };

        // If the token immediately following the generics argument is a closing angle-bracket, we
        // know that we *were* parsing generics arguments.
        //
        // There are a couple things still to note here. If the original set of tokens we were
        // given looks something like:
        //   foo < x>>y
        // if we're not careful, we might parse this as:
        //   foo<x> > y
        // So - like before - we'll check the sort of binary operator we can find here. If we find
        // a binary operator that *starts* with a closing angle-bracket but isn't exactly ">", the
        // syntax is ambiguous.

        match BinOp::try_consume(file, &tokens[consumed..], Restrictions::default()) {
            // ">>"
            Some((BinOp::Shr, op_src))
            // ">="
            | Some((BinOp::Ge, op_src))
            // ">>="
            | Some((BinOp::ShrAssign, op_src)) if !GenericsArgs::can_be_expr(&args) => {
                // As mentioned above, these cases are generally ambiguous. We'll produce an error
                // from them to indicate that the user must provide more information.
                //
                // Because this *is* ambiguous and this function is always called within the
                // context of parsing a (possibly) larger expression, we'll mark the region from
                // generics arguments as consumed when we return.
                errors.extend(local_errors);
                errors.push(Error::AmbiguousCloseGenerics {
                    path: Source::slice_span(file, &tokens[..consumed]),
                    op_src,
                });

                // We add 1 so that we mark the first closing angle-bracket as consumed.
                return Err(Some(consumed + 1));
            }
            // If we only find ">", then we did have generics arguments, so we'll exit.
            Some((BinOp::Gt, _))
            | Some((BinOp::Shr, _))
            // ">="
            | Some((BinOp::Ge, _))
            // ">>="
            | Some((BinOp::ShrAssign, _)) => {
                consumed += 1;

                return Ok(PathComponent {
                    src: Source::slice_span(file, &tokens[..consumed]),
                    name,
                    generics_args: Some(GenericsArgs {
                        src: Source::slice_span(file, &tokens[generics_start..consumed]),
                        args,
                        poisoned,
                        consumed: consumed - generics_start,
                    }),
                });
            }
            _ => (),
        }

        // If we didn't have a closing angle bracket, there's a few cases we still want to handle
        // so that we can produce better error messages.
        //
        // We *could* just return the name, with the logic that "oH tHeRe WaSn'T a cLoSiNg aNgLe
        // BrAcKeT", but that might give bad error messages later on.
        //
        // One possible mistake a user might make could be attempting to use the following as an
        // expression:
        //   x + foo<T,S>(y)
        // Obviously, our syntax forbids this; it should instead be written as:
        //   x + foo<(T,S)>(y)
        // but a user coming from other languages (e.g. C++) might forget this - it's a common
        // mistake. To accomodate for this, we'll produce an error if we see a comma in a context
        // that we aren't expecting it.
        //
        // Of course, this only occurs if we find a comma as the next token. If we don't, we'll
        // just return the name by itself.
        let next_kind = tokens
            .get(consumed)
            .and_then(|res| Some(&res.as_ref().ok()?.kind));
        if let Some(TokenKind::Punctuation(Punc::Comma)) = next_kind {
            errors.extend(local_errors);
            errors.push(Error::UnexpectedGenericsArgsComma {
                ident: name.src,
                args: args.iter().map(|a| a.span()).collect(),
            });

            Err(None)
        } else {
            return_name!()
        }
    }

    /// Attempts to consume a binary or postifx operator, returning `None` if the first token does
    /// not constitute either of these
    ///
    /// On success, the number of tokens consumed will be returned.
    ///
    /// `already_consumed` indicates the place in the original consumed expression `tokens` starts,
    /// in order for us to pass it along to the stack values.
    ///
    /// Like most parsing functions, a return value of `Err(Some)` indicates the number of tokens
    /// that were consumed in the event of an error; a return of `Err(None)` indicates that parsing
    /// within the current token tree should immediately stop.
    fn try_consume_binop_or_postfix(
        stack: &mut Stack,
        file: &FileInfo,
        tokens: TokenSlice,
        already_consumed: usize,
        delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<usize>, Option<usize>> {
        // This function only serves to dispatch between the two different functions for binary and
        // postfix operators
        //
        // We just call them in sequence, starting with binary operators
        if let Some((op, src)) = BinOp::try_consume(file, tokens, restrictions) {
            stack.push_binop(op, src);
            return Ok(Some(op.consumed()));
        }

        // If we didn't have a binary operator here, we'll attempt to consume a postfix operator
        // instead
        let res = PostfixOp::try_consume(
            file,
            tokens,
            delim,
            restrictions,
            ends_early,
            containing_token,
            errors,
        );
        match res {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((op, src))) => {
                let consumed = op.consumed();
                stack.push_postfix(op, src);
                Ok(Some(consumed))
            }
        }
    }

    /// Returns whether the expression is "big"
    ///
    /// This is essentially defined by the following BNF:
    /// ```text
    /// BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr .
    /// ```
    /// Note that -- in addition to the above, `do .. while .. else` expressions are included here,
    /// but only in the case that they do contain an else clause. As such, parsing with
    /// [`Expr::consume_big`] does not permit `do .. while` expressions, to be conservative.
    ///
    /// [`Expr::consume_big`]: #method.consume_big
    fn is_big(&self) -> bool {
        use Expr::*;

        match self {
            If(_) | Match(_) | For(_) | While(_) | Loop(_) | Block(_) | AmbiguousBlock(_) => true,
            DoWhile(ex) if ex.else_branch.is_some() || ex.pred.is_big() => true,
            Literal(_) | Named(_) | PrefixOp(_) | BinOp(_) | PostfixOp(_) | Struct(_)
            | Array(_) | Tuple(_) | DoWhile(_) | Continue(_) => false,
        }
    }

    /// Consumes a "big" expression
    ///
    /// Essentially, this only consumes an expression satisfying [`Expr::is_big`], with one notable
    /// exception - while `is_big` returns true for certain types of `do .. while` expressions,
    /// they are not allowed here.
    ///
    /// [`Expr::is_big`]: #method.is_big
    fn consume_big(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: BigExprContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Expr, Option<usize>> {
        // We'll define a helper macro here for passing along the information needed for consuming
        // the actual expression we find.
        macro_rules! pass {
            ($ty:ident, $variant:ident) => {
                $ty::consume(file, tokens, ends_early, containing_token, errors).map(Expr::$variant)
            };
        }

        match tokens.first() {
            // We *are* expecting a big expression; if we don't find one, that's usually an error
            None if ends_early => Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::BigExpr(ctx),
                    found: end_source!(file, containing_token),
                });

                Err(None)
            }

            // We do the standard error-handling here, producing a secondary error only somtimes.
            // Because some "big" expressions are given by curly braces,
            Some(Err(token_tree::Error::UnclosedDelim(Delim::Curlies, _, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::BigExpr(ctx),
                    found: Source::err(file, e),
                });

                Err(None)
            }

            // Otherwise, we'll hope the first token is one of the ones that indicates the start of
            // a "big" expression
            //
            // These are given by the following BNF:
            //   BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr .
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::If) => pass!(IfExpr, If),
                TokenKind::Keyword(Kwd::Match) => pass!(MatchExpr, Match),
                TokenKind::Keyword(Kwd::For) => pass!(ForExpr, For),
                TokenKind::Keyword(Kwd::While) => pass!(WhileExpr, While),
                TokenKind::Keyword(Kwd::Loop) => pass!(LoopExpr, Loop),
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => {
                    // We're expecting a block expression here - *not* a struct expression. If we
                    // find that the user mistakenly gave a struct expression, we'll produce a
                    // separate error for that.
                    if is_definitely_struct(inner) {
                        errors.push(Error::StructAsBigExpr {
                            outer: t.span(file),
                            ctx,
                        });
                        return Err(Some(1));
                    }

                    let ends_early = false;
                    BlockExpr::parse(
                        file,
                        tokens.first(),
                        ends_early,
                        end_source!(file, containing_token),
                        errors,
                    )
                    .map_err(|()| Some(1))
                    .map(Expr::Block)
                }

                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::BigExpr(ctx),
                        found: Source::token(file, t),
                    });

                    Err(None)
                } // StructAsBigExpr { ctx },
            },
        }
    }

    /// Consumes a list of expressions within a given delimited context
    ///
    /// This is essentially a helper function for extracting the common parts of a few of the
    /// parsing methods for the tokens inside token trees - e.g. `TupleExpr` and `StructExpr`.
    fn consume_all_delimited<T: From<Delimited>>(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        restrictions: Restrictions,
        delim: ExprDelim,
        check_post_expr: Option<fn(&FileInfo, TokenSlice) -> Result<(), Error>>,
        delim_err: fn(Source) -> ExpectedKind,
        errors: &mut Vec<Error>,
    ) -> Result<(Vec<T>, bool), ()> {
        let mut consumed = 0;
        let ends_early = false;
        let mut poisoned = false;
        let mut fields = Vec::new();

        make_expect!(file, inner, consumed, ends_early, Some(src), errors);

        while consumed < inner.len() {
            let res = Expr::consume_delimited(
                file,
                &inner[consumed..],
                restrictions,
                delim,
                ends_early,
                src,
                errors,
            );
            match res {
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
                Ok(field) => {
                    consumed += field.consumed();
                    fields.push(field.into());
                }
            }

            if let Some(check) = check_post_expr.as_ref() {
                if let Err(e) = check(file, &inner[consumed..]) {
                    errors.push(e);
                    poisoned = true;
                    break;
                }
            }

            // Between elements, we'll expect trailing commas
            if consumed < inner.len() {
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ if poisoned => break,
                    @else { poisoned = true; break } => delim_err(Source::token(file, src)),
                ));
            }
        }

        poisoned |= ends_early;

        Ok((fields, poisoned))
    }

    /// Consumes a single (possibly named) expression within a given delimiter context
    ///
    /// This function always expects that there are at least *some* input tokens, and will panic if
    /// this is not the case.
    fn consume_delimited(
        file: &FileInfo,
        tokens: TokenSlice,
        restrictions: Restrictions,
        delim: ExprDelim,
        ends_early: bool,
        containing_token: &Token,
        errors: &mut Vec<Error>,
    ) -> Result<Delimited, Option<usize>> {
        // This function has a fair amount of complexity to manage.

        // There's a little bit of validation that we wat to do on the delimiter passed in, just
        // for forwards compatability.
        debug_assert!(delim.requires_name() || delim.requires_expr());
        if delim.requires_name() {
            debug_assert!(delim.allows_name());
        }

        // We can assert that there *is* a first token because it's provided by the informal
        // contract for calling this function.
        assert!(!tokens.is_empty());
        let fst_token = match tokens[0].as_ref() {
            Ok(t) => t,
            Err(_) => return Err(None),
        };

        // A helper macro for returning with only a single identifier
        macro_rules! only_name {
            ($name:expr) => {{
                let ident = Ident {
                    src: fst_token.span(file),
                    name: $name,
                };

                let src = Source::slice_span(file, &tokens[..1]);

                if delim.requires_name() {
                    return Ok(Delimited {
                        src,
                        name: Some(ident),
                        value: None,
                    });
                } else {
                    let value = Some(Expr::Named(PathComponent {
                        src,
                        name: ident,
                        generics_args: None,
                    }));

                    return Ok(Delimited {
                        src,
                        name: None,
                        value,
                    });
                }
            }};
        }

        // And now we get to the meat of the function. There's a few cases here that we want to
        // look at. I'll describe them here in a condensed form so that the explanation mixed
        // within the implementation isn't *too* difficult to understand.
        //
        // For any delimiter context that *allows* named expressions, we hae a special case we want
        // to go through. If we find that the first token is an identifier, we get the following
        // table of cases for initial tokens.
        //
        //    Ident <Err> => return Err(None),
        //
        //    Ident <End> => only_name!(),
        //    Ident ","   => only_name!(),
        //    Ident ":"   => set name if allowed. Else error
        //
        //    otherwise => if requires name, error
        //                 else, interpret as an expression
        //
        //  where only_name!() expands (roughly) to:
        //    if delim.requires_name() {
        //        Delimited { name, value: None },
        //    } else {
        //        Delimited { name: None, value: name },
        //    }

        let mut name = None;
        let mut consumed = 0;

        if let TokenKind::Ident(n) = &fst_token.kind {
            match tokens.get(1) {
                Some(Err(_)) => return Err(None),

                None => only_name!((*n).into()),
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => only_name!((*n).into()),
                    TokenKind::Punctuation(Punc::Colon) => {
                        if delim.allows_name() {
                            name = Some(Ident {
                                src: fst_token.span(file),
                                name: (*n).into(),
                            });
                            consumed += 2;
                        } else {
                            errors.push(Error::UnexpectedExprColon {
                                delim,
                                src: Source::slice_span(file, &tokens[..2]),
                            });

                            return Err(None);
                        }
                    }
                    // otherwise: if requires name, error
                    _ if delim.requires_name() => {
                        assert!(delim == ExprDelim::StructFields);
                        errors.push(Error::Expected {
                            kind: ExpectedKind::StructFieldExprColonOrComma {
                                name: Source::token(file, fst_token),
                                containing_token: containing_token.span(file),
                            },
                            found: Source::token(file, t),
                        });

                        return Err(None);
                    }
                    // otherwise: probably an expression
                    _ => (),
                },
            }
        } else if delim.requires_name() {
            assert!(delim == ExprDelim::StructFields);
            errors.push(Error::Expected {
                kind: ExpectedKind::StructFieldExprName,
                found: match tokens.first() {
                    Some(res) => Source::from(file, res),
                    None => end_source!(file, Some(containing_token)),
                },
            });

            return Err(None);
        }

        // After (possibly) consuming the name, we'll get the expression
        let value_res = Expr::consume(
            file,
            &tokens[consumed..],
            delim,
            restrictions,
            ends_early,
            Some(containing_token),
            errors,
        );

        match value_res {
            Err(Some(c)) => Err(Some(consumed + c)),
            Err(None) => Err(None),
            Ok(value) => Ok(Delimited {
                src: Source::slice_span(file, &tokens[..consumed + value.consumed()]),
                name,
                value: Some(value),
            }),
        }
    }

    /// Returns whether the token can start an expression
    pub(super) fn is_starting_token(token: &Token) -> bool {
        use TokenKind::*;

        match &token.kind {
            // "simple" atomic expressions
            Literal(_,_)
            | Ident(_)

            // Prefix operators
            | Punctuation(Punc::Not)
            | Punctuation(Punc::Minus)
            | Punctuation(Punc::Plus)
            | Punctuation(Punc::Star)
            | Keyword(Kwd::Let)
            | Keyword(Kwd::Break)
            | Keyword(Kwd::Return)

            // In order: block expr / structs / tuples / array literals
            | Tree { delim: Delim::Curlies, .. }
            | Tree { delim: Delim::Parens, .. }
            | Tree { delim: Delim::Squares, .. }

            // And then the various atomic keyword expressions
            | Keyword(Kwd::While)
            | Keyword(Kwd::Do)
            | Keyword(Kwd::Loop)
            | Keyword(Kwd::If)
            | Keyword(Kwd::Match)
            | Keyword(Kwd::Continue) => true,
            _ => false,
        }
    }

    /// Returns whether the tokens can continue an already-complete expression, subject to the given
    /// set of restrictions
    ///
    /// This essentially returns whether the tokens start with a permitted binary or postfix
    /// operator.
    pub(super) fn can_continue_with(
        file: &FileInfo,
        tokens: TokenSlice,
        restrictions: Restrictions,
    ) -> bool {
        // A helper function to indicate whether a token can start a postfix operator
        let starts_postfix = |kind: &TokenKind| -> bool {
            match kind {
                // We explicitly match all delimiters for forwards-compatability
                TokenKind::Tree { delim, .. } => match delim {
                    // named struct instantiation
                    Delim::Curlies => restrictions.allows_structs(),
                    // function calls, indexing
                    Delim::Parens | Delim::Squares => true,
                }
                TokenKind::Punctuation(Punc::Dot)        // field/tuple access
                | TokenKind::Punctuation(Punc::Tilde)    // type binding
                | TokenKind::Punctuation(Punc::Question) // "try"
                | TokenKind::Keyword(Kwd::Is)            // Pattern equivalence
                => true,

                // Everything else isn't a postfix operator
                _ => false,
            }
        };

        let is_postfix = kind!(tokens)(0).map(starts_postfix).unwrap_or(false);
        is_postfix || BinOp::try_consume(file, tokens, restrictions).is_some()
    }

    /// Returns whether the given set of tokens may continue an expression after an identifier
    /// (notably including generics arguments)
    pub(super) fn can_follow_ident(file: &FileInfo, tokens: TokenSlice) -> bool {
        // Because generics arguments would instead be recognized as the less-than (`<`) operator
        // by `Expr::can_continue_with`, we actually don't need to separately account for them.
        // This function becomes rather simple:
        Expr::can_continue_with(file, tokens, Restrictions::default())
    }

    /// Returns the `Span` corresponding to the source of the expr
    pub(super) fn span(&self) -> Span {
        macro_rules! spans {
            ( $($pat:pat => $arm:expr),+; $($variant:ident),* ) => {
                match self {
                    $($pat => $arm,)+
                    $( Expr::$variant(v) => v.src, )*
                }
            }
        }

        spans!(
            Expr::Literal(lit) => lit.span();
            Named, PrefixOp, BinOp, PostfixOp, Struct, Array, Tuple, Block, AmbiguousBlock, For, While, DoWhile, If, Match, Continue, Loop
        )
    }
}

/// A helper function that returns whether the tokens *definitely* represent the inside of a struct
/// instantiation - as opposed to a block expression
fn is_definitely_struct(tokens: TokenSlice) -> bool {
    // From an implementation stand point, this is fairly simple. It's definitely a struct if it
    // starts with the tokens: `Ident ":"` or `Ident ","`. Anything else is either *definitely* a
    // block expression or is ambiguous (see: AmbiguousBlockExpr).

    match (kind!(tokens)(0), kind!(tokens)(1)) {
        (Some(TokenKind::Ident(_)), Some(TokenKind::Punctuation(Punc::Colon)))
        | (Some(TokenKind::Ident(_)), Some(TokenKind::Punctuation(Punc::Comma))) => true,
        _ => false,
    }
}

impl ExprDelim {
    /// A convenience method to return whether the expression delimeter context requires the first
    /// two tokens to be `Ident ":"` as a field name
    ///
    /// This returns true precisely if the `ExprDelim` is the `StructFields` variant.
    pub fn requires_name(&self) -> bool {
        match self {
            ExprDelim::StructFields => true,
            ExprDelim::Comma | ExprDelim::FnArgs | ExprDelim::Nothing => false,
        }
    }

    /// A convenience method to return whether the expression delimiter context allows the first
    /// two tokens to be `Ident ":"` as a field name
    ///
    /// This returns true precisely if the `ExprDelim` is either the `StructFields` or `FnArgs`
    /// variants.
    pub fn allows_name(&self) -> bool {
        match self {
            ExprDelim::StructFields | ExprDelim::FnArgs => true,
            ExprDelim::Comma | ExprDelim::Nothing => false,
        }
    }

    /// A convenience method to return whether the expression delimiter requires that there be a
    /// full expression (with or without a name)
    ///
    /// This returns true for every value but `StructFields`, where the delimiter may be omitted.
    pub fn requires_expr(&self) -> bool {
        match self {
            ExprDelim::Comma | ExprDelim::FnArgs | ExprDelim::Nothing => true,
            ExprDelim::StructFields => false,
        }
    }

    /// Returns whether the `ExprDelim` is the `Nothing` variant
    pub fn is_nothing(&self) -> bool {
        match self {
            ExprDelim::Nothing => true,
            _ => false,
        }
    }

    /// Returns whether the `ExprDelim` includes commas; defined as `!ExprDelim::is_nothing`.
    pub fn has_comma(&self) -> bool {
        !self.is_nothing()
    }
}

impl PrefixOp {
    /// Returns the binding power of the prefix operator
    pub(super) fn bp(&self) -> BindingPower {
        use BindingPower::*;

        match self {
            PrefixOp::Not => Not,
            PrefixOp::Minus => Minus,
            PrefixOp::Ref { .. } => Ref,
            PrefixOp::Deref => Deref,
            PrefixOp::Let(_, _) => Let,
            PrefixOp::Break => Break,
            PrefixOp::Return => Return,
        }
    }

    /// Attempts to consume a prefix operator, returning the operator and its source on success
    ///
    /// If it is clear that the tokens do not start with a prefix operator, this function will
    /// return `Ok(None)`. Otherwise, errors will result in a return value of `Err(Some)` for
    /// recoverable errors and `Err(None)` when parsing within the current token tree should
    /// immediately stop.
    fn try_consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<(PrefixOp, Span)>, Option<usize>> {
        // Because the set of prefix operators is so limited, we'll just go through all of the
        // cases here.
        //
        // Before we do, however, we'll define a little helper macro to make our returns a little
        // cleaner.
        macro_rules! op {
            ($kind:ident) => {{
                Ok(Some((
                    PrefixOp::$kind,
                    Source::slice_span(file, &tokens[..1]),
                )))
            }};
        }

        match tokens.first() {
            // If we can't get the first token, we'll just indicate that there isn't a prefix
            // operator
            Some(Err(_)) | None => Ok(None),
            // Otherwise, we'll actually go through the cases now
            Some(Ok(fst_token)) => match &fst_token.kind {
                // The first few are simple; they're each a single token
                TokenKind::Punctuation(Punc::Not) => op!(Not),
                TokenKind::Punctuation(Punc::Minus) => op!(Minus),
                TokenKind::Punctuation(Punc::Star) => op!(Deref),
                TokenKind::Keyword(Kwd::Break) => op!(Break),
                TokenKind::Keyword(Kwd::Return) => op!(Return),

                // We follow this up with references: `"&" [ "mut" ]`
                // Because they can consume up to two tokens, we need to give them a special case
                TokenKind::Punctuation(Punc::And) => {
                    let is_mut = match tokens.get(1) {
                        Some(Ok(t)) => match &t.kind {
                            TokenKind::Keyword(Kwd::Mut) => true,
                            _ => false,
                        },
                        _ => false,
                    };

                    Ok(Some((
                        PrefixOp::Ref { is_mut },
                        Source::slice_span(file, &tokens[..1]),
                    )))
                }

                // There's a dedicated function for let expressions, so we'll use that:
                TokenKind::Keyword(Kwd::Let) => {
                    PrefixOp::consume_let(file, tokens, ends_early, containing_token, errors)
                        .map(Some)
                }

                // Anything else isn't a prefix operator
                _ => Ok(None),
            },
        }
    }

    /// Consumes a `let` expression as a prefix operator
    ///
    /// This function assumes that the first token is the keyword `let`, and will panic if it is
    /// not.
    fn consume_let(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<(PrefixOp, Span), Option<usize>> {
        // Let prefixes aren't *too* bad to parse - the BNF is simply:
        //   "let" Pattern [ ":" Type ] "="
        //
        // We're given that the first token is the keyword `let`, so we'll panic if we find that's
        // not the case.
        let let_kwd = assert_token!(
            tokens.first() => "keyword `let`",
            Ok(t) && TokenKind::Keyword(Kwd::Let) => Source::token(file, t),
        );

        let mut consumed = 1;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let pat_ctx = PatternContext::Let(let_kwd);
        let pat = Pattern::consume(
            file,
            &tokens[consumed..],
            pat_ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;

        consumed += pat.consumed();
        let pat_src = Source::slice_span(file, &tokens[1..consumed]);

        // If we have a ":" token following the pattern, we'll expect a type
        let ty = expect!((
            Ok(_),
            // If we find a "=", that's fine because it's what we'll expect next anyways.
            TokenKind::Punctuation(Punc::Eq) => None,
            TokenKind::Punctuation(Punc::Colon) => {
                consumed += 1;
                let ty_res = Type::consume(
                    file,
                    &tokens[consumed..],
                    TypeContext::LetHint(LetContext {
                        let_kwd,
                        pat: pat_src,
                    }),
                    Restrictions::default(),
                    ends_early,
                    containing_token,
                    errors,
                );

                match ty_res {
                    Err(Some(c)) => return Err(Some(c + consumed)),
                    Err(None) => return Err(None),
                    Ok(ty) => {
                        consumed += ty.consumed();
                        Some(ty)
                    }
                }
            },
            @else(return None) => ExpectedKind::LetColonOrEq(LetContext {
                let_kwd,
                pat: Source::slice_span(file, &tokens[1..consumed]),
            })
        ));

        // Now, we'll expect an equals for assigning the value as the last token in this prefix
        // operator
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Eq) => consumed += 1,
            @else(return Some) => ExpectedKind::LetEq(LetContext {
                let_kwd,
                pat: pat_src,
            })
        ));

        // And with that all done, we'll return the prefix operator
        Ok((
            PrefixOp::Let(pat, ty),
            Source::slice_span(file, &tokens[..consumed]),
        ))
    }
}

impl BinOp {
    /// Returns the binding power of the binary operator
    #[rustfmt::skip]
    pub(super) fn bp(&self) -> BindingPower {
        macro_rules! bps {
            ($($variant:ident,)*) => {
                match self {
                    $(BinOp::$variant => BindingPower::$variant,)*
                }
            }
        }

        bps!(
            Add, Sub, Mul, Div, Mod, BitAnd, BitOr, BitXor, Shl, Shr, LogicalAnd, LogicalOr, Lt, Gt,
            Le, Ge, Eq, Ne, AddAssign, SubAssign, MulAssign, DivAssign, ModAssign, BitAndAssign,
            BitOrAssign, ShlAssign, ShrAssign, Assign,
        )
    }

    /// Returns the fixity of the operator
    fn fixity(&self) -> Fixity {
        use BinOp::*;

        match self {
            Add | Sub | Mul | Div | Mod | BitAnd | BitOr | BitXor | Shl | Shr | LogicalAnd
            | LogicalOr | Lt | Gt | Le | Ge | Eq | Ne => Fixity::Left,
            AddAssign | SubAssign | MulAssign | DivAssign | ModAssign | BitAndAssign
            | BitOrAssign | ShlAssign | ShrAssign | Assign => Fixity::Right,
        }
    }

    /// Attempts to consume a binary operator as a prefix of the given tokens
    fn try_consume(
        file: &FileInfo,
        tokens: TokenSlice,
        restrictions: Restrictions,
    ) -> Option<(BinOp, Span)> {
        // Broadly, this function matches on the `kind` field of the first two tokens, assuming
        // they are both successful. We use the folowing pair of macros to make this easier.
        //
        // The first macro here produces a pattern to match on
        macro_rules! punc {
            ($($kind:ident),+) => {
                [$(Some(&TokenKind::Punctuation(Punc::$kind)),)+ ..]
            };
        }

        // And the second produces the value we return
        macro_rules! op {
            // Most operators will only occupy a single token
            ($kind:ident) => {{
                op!($kind, 1)
            }};

            // But some use more, so we provide the second variant here to allow that
            ($kind:ident, $len:expr) => {{
                Some((BinOp::$kind, Source::slice_span(file, &tokens[..$len])))
            }};
        }

        let kind = kind!(tokens);
        let no_trail = |idx: usize| match tokens
            .get(idx)?
            .as_ref()
            .ok()?
            .trailing_whitespace
            .is_empty()
        {
            true => Some(()),
            false => None,
        };

        // We'll match on the first tokens that are all "glued" together - i.e. there's no
        // whitespace between them
        let ts = [
            kind(0),
            no_trail(0).and_then(|()| kind(1)),
            no_trail(1).and_then(|()| kind(2)),
        ];

        match &ts {
            // All of the assignment operators are composed of multiple tokens, so we do those
            // first. They all require assignment to be available
            punc!(Plus, Eq) if restrictions.allows_assignment() => op!(AddAssign, 2),
            punc!(Minus, Eq) if restrictions.allows_assignment() => op!(SubAssign, 2),
            punc!(Star, Eq) if restrictions.allows_assignment() => op!(MulAssign, 2),
            punc!(Slash, Eq) if restrictions.allows_assignment() => op!(DivAssign, 2),
            punc!(Percent, Eq) if restrictions.allows_assignment() => op!(ModAssign, 2),
            punc!(And, Eq) if restrictions.allows_assignment() => op!(BitAndAssign, 2),
            punc!(Or, Eq) if restrictions.allows_assignment() => op!(BitOrAssign, 2),
            punc!(Lt, Lt, Eq) if restrictions.allows_assignment() => op!(ShlAssign, 3),
            punc!(Gt, Gt, Eq) if restrictions.allows_assignment() => op!(ShrAssign, 3),
            punc!(Eq) if restrictions.allows_assignment() => op!(Assign),

            punc!(Plus) => op!(Add),
            punc!(Minus) => op!(Sub),
            punc!(Star) => op!(Mul),
            punc!(Slash) => op!(Div),
            punc!(Percent) => op!(Mod),
            punc!(OrOr) => op!(LogicalOr),
            // We do logical AND before bitwise AND because it's composed of the same tokens
            // Instead of treating AndAnd as a prefix operator (for double reference), we combine
            // two Ands into a single binary operator.
            punc!(And, And) => op!(LogicalAnd, 2),
            punc!(And) => op!(BitAnd),
            punc!(Or) if restrictions.allows_pipe() => op!(BitOr),
            punc!(Caret) => op!(BitXor),
            // The same goes for bitshifts
            punc!(Lt, Lt) if restrictions.allows_angle_bracket() => op!(Shl, 2),
            punc!(Gt, Gt) if restrictions.allows_angle_bracket() => op!(Shr, 2),
            punc!(Lt) if restrictions.allows_angle_bracket() => op!(Lt),
            punc!(Gt) if restrictions.allows_angle_bracket() => op!(Gt),
            punc!(Le) => op!(Le),
            punc!(Ge) => op!(Ge),
            punc!(EqEq) => op!(Eq),
            punc!(NotEq) => op!(Ne),

            _ => None,
        }
    }

    /// Returns whether the binary operator is an assignment operator
    fn is_assign_op(&self) -> bool {
        use BinOp::*;

        match self {
            AddAssign | SubAssign | MulAssign | DivAssign | ModAssign | BitAndAssign
            | BitOrAssign | ShlAssign | ShrAssign | Assign => true,
            _ => false,
        }
    }
}

impl Consumed for BinOp {
    fn consumed(&self) -> usize {
        use BinOp::*;

        match self {
            AddAssign | SubAssign | MulAssign | DivAssign | ModAssign | BitAndAssign
            | BitOrAssign | Shl | Shr | LogicalAnd => 2,
            ShrAssign | ShlAssign => 3,
            Add | Sub | Mul | Div | Mod | LogicalOr | BitAnd | BitOr | Lt | Gt | Le | Ge | Eq
            | Ne | BitXor | Assign => 1,
        }
    }
}

impl PostfixOp {
    /// Returns the binding power of the postfix operator
    pub(super) fn bp(&self) -> BindingPower {
        use BindingPower::*;

        match self {
            PostfixOp::Index(_, _) => Index,
            PostfixOp::Access(_) => Access,
            PostfixOp::TupleIndex(_) => TupleIndex,
            PostfixOp::FnCall(_, _) => FnCall,
            PostfixOp::NamedStruct(_) => NamedStruct,
            PostfixOp::TypeBinding(_) => TypeBinding,
            PostfixOp::IsPattern(_) => IsPattern,
            PostfixOp::Try => Try,
        }
    }

    /// Attempts to consume a postfix operator of the given tokens
    ///
    /// This will return `Err(_)` if we encounter a previous tokenizer error *or* if we encounter a
    /// type binding and the restrictions prevent it (with `Restrictions::allows_pipe`).
    ///
    /// This function additionally handles the ambiguity that may be present with less-than (`<`)
    /// following identifiers - hence why it takes `stacks`. Note that if a *truly* ambiguous case
    /// occurs, we'll additionally handle the pieces of the expression resulting from that
    /// ambiguity.
    fn try_consume(
        file: &FileInfo,
        tokens: TokenSlice,
        delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<(PostfixOp, Span)>, Option<usize>> {
        // The large majority of this function is spent producing the various operators that we
        // might use.

        match tokens.first() {
            // Because some tokenizer error tokens *could* represent syntax that's valid at that
            // immediate point, we need to explicitly filter out the errors here so we don't emit a
            // double error for them.
            //
            // All delimiters can represent a postfix operator, so we explicitly account for
            // unclosed delimiters here.
            Some(Err(token_tree::Error::UnclosedDelim(_, _, _))) => Err(None),

            // For everything else, we just indicate that we couldn't find a postfix operator
            Some(Err(_)) | None => Ok(None),

            // The postfix operators are given by the following BNF definition:
            //   PostfixOp = "[" Expr "]"                # Indexing
            //             | "." Ident [ GenericsArgs ]   # Field / method access
            //             | "." IntLiteral              # Tuple indexing
            //             | FnArgs                      # Function calls
            //             | StructExpr                  # Named structs
            //             | "~" Type                    # Type binding
            //             | "is" Pattern                # Pattern equivalence
            //             | "?"                         # "try" operator
            // We won't do these in *precisely* the same order, but we will go through all of them.
            Some(Ok(fst_token)) => match &fst_token.kind {
                // The easiest set to go through are all of the token trees:
                TokenKind::Tree { delim, inner, .. } => {
                    let res = match delim {
                        Delim::Curlies => {
                            if let Some(ctx) = restrictions.no_struct_postfix {
                                if is_definitely_struct(inner) {
                                    errors.push(Error::CurliesDisallowed {
                                        ctx,
                                        src: Source::token(file, fst_token),
                                    });

                                    return Err(None);
                                } else {
                                    return Ok(None);
                                }
                            }

                            StructExpr::parse(file, fst_token, inner, errors)
                                .map(PostfixOp::NamedStruct)
                        }
                        Delim::Parens => PostfixOp::parse_fn_args(file, fst_token, inner, errors),
                        Delim::Squares => PostfixOp::parse_index(file, fst_token, inner, errors),
                    };

                    res.map_err(|()| Some(1))
                        .map(|op| Some((op, Source::slice_span(file, &tokens[..1]))))
                }

                // We'll follow with the only two other "simple" cases
                //
                // The "try" operator is *really* simple:
                TokenKind::Punctuation(Punc::Question) => Ok(Some((
                    PostfixOp::Try,
                    Source::slice_span(file, &tokens[..1]),
                ))),

                // "is" patterns are also relatively simple, so we don't both with a separate
                // function here either.
                TokenKind::Keyword(Kwd::Is) => {
                    let res = Pattern::consume(
                        file,
                        &tokens[1..],
                        PatternContext::Is(Source::token(file, fst_token)),
                        ends_early,
                        containing_token,
                        errors,
                    );

                    match res {
                        Err(Some(c)) => Err(Some(c + 1)),
                        Err(None) => Err(None),
                        Ok(pat) => {
                            let src = Source::slice_span(file, &tokens[..1 + pat.consumed()]);
                            Ok(Some((PostfixOp::IsPattern(pat), src)))
                        }
                    }
                }

                TokenKind::Punctuation(Punc::Tilde) if !restrictions.allows_pipe() => {
                    errors.push(Error::TypeHintDisallowed {
                        tilde_token: Source::token(file, fst_token),
                    });
                    return Err(None);
                }
                TokenKind::Punctuation(Punc::Tilde) => {
                    let res = Type::consume(
                        file,
                        &tokens[1..],
                        TypeContext::TypeBinding {
                            tilde: Source::token(file, fst_token),
                        },
                        restrictions,
                        ends_early,
                        containing_token,
                        errors,
                    );

                    match res {
                        Err(Some(c)) => Err(Some(c + 1)),
                        Err(None) => Err(None),
                        Ok(ty) => {
                            let src = Source::slice_span(file, &tokens[..1 + ty.consumed()]);
                            Ok(Some((PostfixOp::TypeBinding(Box::new(ty)), src)))
                        }
                    }
                }

                // The only other postfix operators both start with a dot, so we'll use a separate
                // function to handle those.
                TokenKind::Punctuation(Punc::Dot) => PostfixOp::consume_dot(
                    file,
                    tokens,
                    delim,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Some),

                // If the set of tokens clearly doesn't start with a postfix operator, we'll
                // indicate as such
                _ => return Ok(None),
            },
        }
    }

    /// Parses the contents of a parenthetically-delimited token tree as a list of function
    /// arguments
    fn parse_fn_args(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> Result<PostfixOp, ()> {
        let (values, poisoned) = Expr::consume_all_delimited(
            file,
            src,
            inner,
            Restrictions::default(),
            ExprDelim::FnArgs,
            None,
            ExpectedKind::FnArgDelim,
            errors,
        )?;

        Ok(PostfixOp::FnCall(values, poisoned))
    }

    /// Parses the contents of a square-bracket-delimited token tree as a single expression for
    /// indexing
    fn parse_index(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> Result<PostfixOp, ()> {
        Expr::consume(
            file,
            inner,
            ExprDelim::Nothing,
            Restrictions::default(),
            false,
            Some(src),
            errors,
        )
        .map_err(|_| ())
        .map(|expr| {
            let mut poisoned = false;
            if expr.consumed() != inner.len() {
                errors.push(Error::Expected {
                    kind: ExpectedKind::EndOfIndexPostfix,
                    found: Source::from(file, &inner[expr.consumed()]),
                });

                poisoned = true;
            }

            PostfixOp::Index(Box::new(expr), poisoned)
        })
    }

    /// Consumes a postfix given by a dot (`.`) - either for tuple-field access or the more generic
    /// field/method access with an identifier and optional generics arguments.
    ///
    /// This function will assume that the first token in the supplied list is a dot (`.`) token,
    /// and will panic if that is not the case.
    fn consume_dot(
        file: &FileInfo,
        tokens: TokenSlice,
        delim: ExprDelim,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<(PostfixOp, Span), Option<usize>> {
        // We'll assert that the first token is a dot ('.'), just to verify that we've been given
        // what we were promised
        let dot_token = assert_token!(
            tokens.first() => "dot (`.`)",
            Ok(t) && TokenKind::Punctuation(Punc::Dot) => Source::token(file, t),
        );

        make_expect!(file, tokens, 1, ends_early, containing_token, errors);

        expect!((
            Ok(_),
            TokenKind::Literal(value, LiteralKind::Int) => {
                let op_src = Source::slice_span(file, &tokens[..2]);
                let op = PostfixOp::TupleIndex(IntLiteral {
                    src: Source::slice_span(file, &tokens[1..2]),
                    content: (*value).into(),
                    suffix: None,
                });

                Ok((op, op_src))
            },
            TokenKind::Ident(_) => {
                let path_res = Expr::consume_path_component(
                    file,
                    &tokens[1..],
                    delim,
                    ends_early,
                    containing_token,
                    errors,
                );

                match path_res {
                    Ok(path) => {
                        let src = Source::slice_span(file, &tokens[..path.consumed() + 1]);
                        Ok((PostfixOp::Access(path), src))
                    }
                    Err(None) => Err(None),
                    Err(Some(c)) => Err(Some(c + 1)),
                }
            },
            @else(return None) => ExpectedKind::DotAccess(dot_token),
        ))
    }
}

impl From<Delimited> for FnArg {
    fn from(delim: Delimited) -> Self {
        FnArg {
            src: delim.src,
            name: delim.name,
            value: delim.value.unwrap(),
        }
    }
}

impl StructExpr {
    /// Parses a `StructExpr` from the entire set of input tokens
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> Result<StructExpr, ()> {
        fn starts_assignment(file: &FileInfo, tokens: TokenSlice) -> Result<(), Error> {
            let (op, op_src) = match BinOp::try_consume(file, tokens, Restrictions::default()) {
                None => return Ok(()),
                Some((op, src)) => (op, src),
            };

            match op.is_assign_op() {
                false => Ok(()),
                true => Err(Error::AssignOpDisallowedInStructExpr { op_src }),
            }
        }

        let (fields, poisoned) = Expr::consume_all_delimited(
            file,
            src,
            inner,
            Restrictions::default().no_assignment(),
            ExprDelim::StructFields,
            Some(starts_assignment),
            ExpectedKind::StructFieldExprDelim,
            errors,
        )?;

        Ok(StructExpr {
            src: src.span(file),
            fields,
            poisoned,
        })
    }
}

impl From<Delimited> for StructFieldExpr {
    fn from(delim: Delimited) -> Self {
        assert!(delim.name.is_some());

        StructFieldExpr {
            src: delim.src,
            name: delim.name.unwrap(),
            value: delim.value,
        }
    }
}

impl ArrayExpr {
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> Result<ArrayExpr, ()> {
        let (values, poisoned) = Expr::consume_all_delimited(
            file,
            src,
            inner,
            Restrictions::default(),
            ExprDelim::Comma,
            None,
            ExpectedKind::ArrayDelim,
            errors,
        )?;

        Ok(ArrayExpr {
            src: src.span(file),
            values,
            poisoned,
        })
    }
}

impl TupleExpr {
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> Result<TupleExpr, ()> {
        let (values, poisoned) = Expr::consume_all_delimited(
            file,
            src,
            inner,
            Restrictions::default(),
            ExprDelim::Comma,
            None,
            ExpectedKind::TupleDelim,
            errors,
        )?;

        Ok(TupleExpr {
            src: src.span(file),
            values,
            poisoned,
        })
    }
}

impl From<Delimited> for Expr {
    fn from(delim: Delimited) -> Expr {
        assert!(delim.name.is_none());

        delim.value.unwrap()
    }
}

impl BlockExpr {
    /// Parses a block expression from the given token
    ///
    /// Because block expressions are always given by the curly braces they're enclosed by, the
    /// single token is expected to be a curly-brace-enclosed block.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub fn parse(
        file: &FileInfo,
        token: Option<&TokenResult>,
        ends_early: bool,
        none_source: Source,
        errors: &mut Vec<Error>,
    ) -> Result<BlockExpr, ()> {
        // Parsing a block expression is fairly simple. Essentially, we repeatedly consume input,
        // using `Item::consume` for anything that looks like an item, and doing a kind of dynamic
        // expression parsing for everything else. We'll get more into that later.

        let mut consumed = 0;
        let mut stmts = Vec::new();
        let mut poisoned = false;

        // A temporary macro for reducing the size of the match block for extracting the curly
        // braces.
        macro_rules! err {
            ($source:expr) => {{
                errors.push(Error::Expected {
                    kind: ExpectedKind::BlockExpr,
                    found: $source,
                });

                Err(())
            }};
        }

        let (src, inner, ends_early) = match token {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => (t, inner, false),
                _ => return err!(Source::token(file, t)),
            },
            Some(Err(_)) => return Err(()),
            None if ends_early => return Err(()),
            None => return err!(none_source),
        };

        // A helper macro for handling results
        macro_rules! handle {
            ($res:expr => { Ok($p:pat) => $arm:expr $(,)? }) => {{
                match $res {
                    Err(Some(c)) => {
                        consumed += c;
                        poisoned = true;
                        continue;
                    }
                    Err(None) => {
                        poisoned = true;
                        break None;
                    }
                    Ok($p) => $arm,
                }
            }};
        }

        let tail_expr = loop {
            let next_token = match inner.get(consumed) {
                None => break None,
                // If there was a tokenizer error, we'll just break out of the loop
                Some(Err(_)) => {
                    poisoned = true;
                    break None;
                }
                Some(Ok(t)) => t,
            };

            if let TokenKind::Punctuation(Punc::Semi) = next_token.kind {
                stmts.push(Stmt::UnnecessarySemi(next_token.span(file)));
                consumed += 1;
                continue;
            }

            if Item::is_starting_token(next_token) {
                let item_res =
                    Item::consume(file, &inner[consumed..], ends_early, Some(src), errors);
                match item_res {
                    Ok(item) => {
                        consumed += item.consumed();
                        stmts.push(Stmt::Item(item));
                    }
                    Err(ItemParseErr { consumed: c }) => {
                        poisoned = true;
                        consumed += c;
                        match Item::seek_next_start(&inner[consumed..]) {
                            Some(idx) => consumed += idx,
                            None => break None,
                        }
                    }
                }

                continue;
            }

            // If we didn't find an item, we'll parse an expression, which may have a trailing
            // semicolon if it isn't the final expression in the block.
            let expr_res = Expr::consume_until(
                file,
                &inner[consumed..],
                BlockExpr::expr_stack_done,
                ExprDelim::Nothing,
                Restrictions::default().with_do_while(true),
                ends_early,
                Some(src),
                errors,
            );

            let (expr_start, expr) = handle!(expr_res => {
                Ok(expr) => {
                    let expr_start = consumed;
                    consumed += expr.consumed();

                    if !BlockExpr::requires_trailing_semi(&expr) {
                        stmts.push(Stmt::BigExpr(expr));
                        continue;
                    }

                    (expr_start, expr)
                },
            });

            let expr_src = Source::slice_span(file, &inner[expr_start..consumed]);

            // At this point, we're either expecting a semicolon or the end of the input tokens
            match inner.get(consumed) {
                // Running out of tokens is expected
                None => {
                    poisoned |= ends_early;
                    break Some(expr);
                }
                // Tokenizer errors are not:
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::TrailingSemi { expr_src },
                        found: Source::err(file, e),
                    });

                    stmts.push(Stmt::Little(LittleExpr {
                        src: expr_src,
                        expr,
                        poisoned: true,
                    }));
                    poisoned = true;

                    break None;
                }

                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Semi) => {
                        consumed += 1;
                        stmts.push(Stmt::Little(LittleExpr {
                            src: Source::slice_span(file, &inner[expr_start..consumed]),
                            expr,
                            poisoned: false,
                        }));
                    }
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::TrailingSemi { expr_src },
                            found: Source::token(file, t),
                        });

                        stmts.push(Stmt::Little(LittleExpr {
                            src: expr_src,
                            expr,
                            poisoned: true,
                        }));
                        poisoned = true;

                        continue;
                    }
                },
            }
        };

        Ok(BlockExpr {
            src: src.span(file),
            stmts,
            tail: tail_expr.map(Box::new),
            poisoned,
        })
    }

    /// Returns whether an expression requires a trailing semicolon as part of a block
    fn requires_trailing_semi(expr: &Expr) -> bool {
        match expr {
            Expr::PrefixOp(expr) => {
                let op = &expr.op;
                let rhs = &expr.expr;

                match op {
                    PrefixOp::Let(_, _) if rhs.is_big() => false,
                    _ => true,
                }
            }
            Expr::BinOp(expr) => !(expr.op.is_assign_op() && expr.rhs.is_big()),
            _ => !expr.is_big(),
        }
    }

    /// Returns whether an expression stack can be treated - in its current state - as a "big"
    /// expression
    fn expr_stack_done(stack: &Stack) -> bool {
        let expr = match stack.last_expr.as_ref() {
            None => return false,
            Some(ex) => ex,
        };

        match &stack.elems[..] {
            [] => !BlockExpr::requires_trailing_semi(expr),
            [stack::Element::PrefixOp {
                op: PrefixOp::Let(_, _),
                ..
            }] => !BlockExpr::requires_trailing_semi(expr),
            [stack::Element::BinOp { op, .. }] if op.is_assign_op() => {
                !BlockExpr::requires_trailing_semi(expr)
            }
            _ => false,
        }
    }
}

impl ForExpr {
    /// Consumes a "for" loop expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "for", and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<ForExpr, Option<usize>> {
        // For loops are fairly simple - the BNF is exactly:
        //   "for" Pattern "in" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs
        //
        // Our primary task here is just to glue together the other parsers.
        //
        // The first thing we're going to do is just to check that the input we were given *did*
        // start with the `for` keyword.
        let for_kwd = assert_token!(
            tokens.first() => "keyword `for`",
            Ok(t) && TokenKind::Keyword(Kwd::For) => Source::token(file, t),
        );

        let mut consumed = 1;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let pat_ctx = PatternContext::For(for_kwd);
        let pat = Pattern::consume(
            file,
            &tokens[consumed..],
            pat_ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;
        consumed += pat.consumed();

        // After the pattern, we expect the keyword "in"
        expect!((
            Ok(_),
            TokenKind::Keyword(Kwd::In) => consumed += 1,
            @else(return None) => ExpectedKind::ForLoopInKwd(Source::slice_span(file, &tokens[..consumed]))
        ));

        // And then we expect an expression. This expression can't include curly braces (in certain
        // places) because they would be ambiguous with the following block.
        let iter = Expr::consume(
            file,
            &tokens[consumed..],
            ExprDelim::Nothing,
            Restrictions::default().no_struct_postfix(NoCurlyContext::ForIter),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;
        consumed += iter.consumed();

        // And this is followed by a block expression
        let body = BlockExpr::parse(
            file,
            tokens.get(consumed),
            ends_early,
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        // For loops may be optionally followed by an 'else' branch
        let else_branch = ElseBranch::try_consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?
        .map(Box::new);
        consumed += else_branch.consumed();

        Ok(ForExpr {
            src: Source::slice_span(file, &tokens[..consumed]),
            pat,
            iter: Box::new(iter),
            body,
            else_branch,
        })
    }
}

impl WhileExpr {
    /// Consumes a `while` loop expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "while", and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<WhileExpr, Option<usize>> {
        // More simple than `for` loops, while loops have the following BNF:
        //   "while" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs
        assert_token!(
            tokens.first() => "keyword `while`",
            Ok(t) && TokenKind::Keyword(Kwd::While) => (),
        );

        let mut consumed = 1;
        let condition = Expr::consume(
            file,
            &tokens[..consumed],
            ExprDelim::Nothing,
            Restrictions::default().no_struct_postfix(NoCurlyContext::WhileCondition),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;
        consumed += condition.consumed();

        let body = BlockExpr::parse(
            file,
            tokens.get(consumed),
            ends_early,
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        // While loops may be optionally followed by an 'else' branch:
        let else_branch = ElseBranch::try_consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?
        .map(Box::new);
        consumed += else_branch.consumed();

        Ok(WhileExpr {
            src: Source::slice_span(file, &tokens[..consumed]),
            condition: Box::new(condition),
            body,
            else_branch,
        })
    }
}

impl DoWhileExpr {
    /// Consumes a `do..while` expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "do', and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<DoWhileExpr, Option<usize>> {
        // Do..while expressions are moderately complex; the BNF is defined as:
        //   "do" BlockExpr "while" Expr [ "else" BigExpr ] .
        // With the addition that we cannot allow expressions that might have else branches inside
        // of the condition - i.e. the following is illegal:
        //     do {
        //         foo()
        //     while if x { y };
        // This is not allowed because a trailing `else` branch from the `if` expression would be
        // ambiguous with a trailing `else` branch from the do-while loop itself.
        //
        // We're given that the first token in the set we're given is "do", so we'll just
        // double-check that.
        assert_token!(
            tokens.first() => "keyword `do`",
            Ok(t) && TokenKind::Keyword(Kwd::Do) => (),
        );

        // After the initial "do", we're expecting a block expression
        let body = BlockExpr::parse(
            file,
            tokens.get(1),
            ends_early,
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| Some(1))?;

        let mut consumed = 2;

        // And then "while"
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);
        expect!((
            Ok(_),
            TokenKind::Keyword(Kwd::While) => (),
            @else(return Some) => ExpectedKind::DoWhileWhileToken,
        ));

        consumed += 1;

        let pred = Expr::consume(
            file,
            &tokens[consumed..],
            ExprDelim::Nothing,
            Restrictions::default().no_else_branch(),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;

        consumed += pred.consumed();

        let else_branch = ElseBranch::try_consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?
        .map(Box::new);

        consumed += else_branch.consumed();

        Ok(DoWhileExpr {
            src: Source::slice_span(file, &tokens[..consumed]),
            body,
            pred: Box::new(pred),
            else_branch,
        })
    }

    /// Returns whether the expression stack can be allowed to parse a block expression next
    ///
    /// This function expects to be called only when the stack's `last_expr` field is `None` - i.e.
    /// not when the stack is expecting a binary or postfix operator.
    fn is_allowed(stack: &Stack) -> bool {
        use self::PrefixOp::Let;
        use stack::Element::{BinOp, PrefixOp};

        assert!(stack.last_expr.is_none());

        match &stack.elems[..] {
            [] => true,
            [PrefixOp { op: Let(_, _), .. }] => true,
            [BinOp { op, .. }] if op.is_assign_op() => true,
            _ => false,
        }
    }
}

impl LoopExpr {
    /// Consumes a `loop` expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "loop", and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<LoopExpr, Option<usize>> {
        // Loop expressions are very simple; the BNF is just:
        //   "loop" BlockExpr
        assert_token!(
            tokens.first() => "keyword `loop`",
            Ok(t) && TokenKind::Keyword(Kwd::Loop) => (),
        );

        // If we won't be able to parse a block expression, due to the token list ending early,
        // we'll just return an error - we don't want to pass it down to `BlockExpr::parse`
        if tokens.len() < 2 && ends_early {
            return Err(None);
        }

        BlockExpr::parse(
            file,
            tokens.get(1),
            ends_early,
            end_source!(file, containing_token),
            errors,
        )
        .map(|body| LoopExpr {
            src: Source::slice_span(file, &tokens[..2]),
            body,
        })
        .map_err(|()| None)
    }
}

impl IfExpr {
    /// Consumes an "if" conditional expression
    ///
    /// This function assumes that the starting token is the keyword `if`, and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<IfExpr, Option<usize>> {
        // If conditions are fairly simple - they are defined with the following BNF:
        //   "if" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs
        assert_token!(
            tokens.first() => "keyword `if`",
            Ok(t) && TokenKind::Keyword(Kwd::If) => (),
        );

        let mut consumed = 1;
        let condition = Expr::consume(
            file,
            &tokens[consumed..],
            ExprDelim::Nothing,
            Restrictions::default().no_struct_postfix(NoCurlyContext::IfCondition),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;
        consumed += condition.consumed();

        let body = BlockExpr::parse(
            file,
            tokens.get(consumed),
            ends_early,
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        let else_branch = ElseBranch::try_consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?
        .map(Box::new);
        consumed += else_branch.consumed();

        Ok(IfExpr {
            src: Source::slice_span(file, &tokens[consumed..]),
            condition: Box::new(condition),
            body,
            else_branch,
        })
    }
}

impl MatchExpr {
    /// Consumes a "match" expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword `match`, and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<MatchExpr, Option<usize>> {
        // Match expressions are defined by the following BNF:
        //   "match" Expr* "{" { MatchArm } "}"
        // * excluding structs
        let match_kwd = assert_token!(
            tokens.first() => "keyword `match`",
            Ok(t) && TokenKind::Keyword(Kwd::Match) => Source::token(file, t),
        );

        let mut consumed = 1;
        let expr = Expr::consume(
            file,
            &tokens[consumed..],
            ExprDelim::Nothing,
            Restrictions::default().no_struct_postfix(NoCurlyContext::MatchExpr),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;
        consumed += expr.consumed();

        let (arms, poisoned) = match tokens.get(consumed) {
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::MatchBody(match_kwd),
                    found: end_source!(file, containing_token),
                });

                return Err(None);
            }
            Some(Err(token_tree::Error::UnclosedDelim(Delim::Curlies, _, _))) => return Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::MatchBody(match_kwd),
                    found: Source::err(file, e),
                });

                return Err(Some(consumed));
            }
            Some(Ok(t)) => match &t.kind {
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => {
                    consumed += 1;
                    MatchArm::parse_all(file, match_kwd, t, inner, errors)
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::MatchBody(match_kwd),
                        found: Source::token(file, t),
                    });

                    return Err(Some(consumed));
                }
            },
        };

        Ok(MatchExpr {
            src: Source::slice_span(file, &tokens[..consumed]),
            expr: Box::new(expr),
            arms,
            poisoned,
        })
    }
}

impl MatchArm {
    /// A helper function for [`MatchExpr::consume`](struct.MatchExpr.html#method.consume)
    ///
    /// This function parses the entire contents of a curly-brace enclosed block as the body of a
    /// match expression, returning the match arms and whether that list is poisoned.
    fn parse_all(
        file: &FileInfo,
        match_kwd: Source,
        curly_src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> (Vec<MatchArm>, bool) {
        let mut consumed = 0;
        let mut poisoned = false;
        let mut arms = Vec::new();
        let ends_early = false;

        make_expect!(file, inner, consumed, ends_early, Some(curly_src), errors);

        let pat_ctx = PatternContext::Match(match_kwd);
        while consumed < inner.len() {
            // breakpoint

            let arm_res = MatchArm::consume(
                file,
                &inner[consumed..],
                pat_ctx,
                ends_early,
                Some(curly_src),
                errors,
            );

            let arm_src;
            let requires_delim;

            match arm_res {
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    arm_src = Source::slice_span(file, &inner[consumed..consumed + c]);
                    consumed += c;
                    poisoned = true;
                    requires_delim = false;
                }
                Ok(arm) => {
                    arm_src = Source::slice_span(file, &inner[consumed..consumed + arm.consumed()]);
                    consumed += arm.consumed();
                    requires_delim = arm.requires_delim();
                    arms.push(arm);
                }
            }

            if consumed < inner.len() {
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ if !requires_delim => continue,
                    _ if poisoned => break,
                    @else { poisoned = true; break } => ExpectedKind::MatchArmDelim(arm_src),
                ))
            }
        }

        (arms, poisoned)
    }

    /// Consumes a single match arm as a prefix of the given tokens
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        pat_ctx: PatternContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<MatchArm, Option<usize>> {
        // Match arms are essentially defined by the following BNF:
        //   Pattern [ "if" Expr ] "=>" Expr

        let pat = Pattern::consume(file, tokens, pat_ctx, ends_early, containing_token, errors)?;
        let mut consumed = pat.consumed();

        let mut cond: Option<Expr> = None;

        // After the pattern, we optionally allow `"if" Expr`:
        let kind = tokens
            .get(consumed)
            .and_then(|res| Some(&res.as_ref().ok()?.kind));
        if let Some(TokenKind::Keyword(Kwd::If)) = kind {
            consumed += 1;

            // If we found "if", we'll expect an expression
            cond = Expr::consume(
                file,
                &tokens[consumed..],
                ExprDelim::Nothing,
                Restrictions::default(),
                ends_early,
                containing_token,
                errors,
            )
            .map(Some)
            .map_err(p!(Some(c) => Some(consumed + c)))?;

            consumed += cond.consumed();
        }

        // And then we'll expect the `"=>" Expr`:
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::ThickArrow) => consumed += 1,
            @else(return None) => ExpectedKind::MatchArmArrow,
        ));

        let eval = Expr::consume(
            file,
            &tokens[consumed..],
            // Strictly speaking, we aren't consuming a bunch of expressions delimited by commas.
            // But this expression *is* followed by a comma, so there are certain types of errors
            // that wouldn't be appropriate to generate here.
            ExprDelim::Comma,
            Restrictions::default(),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(consumed + c)))?;

        consumed += eval.consumed();

        Ok(MatchArm {
            src: Source::slice_span(file, &tokens[..consumed]),
            pat,
            cond,
            eval,
        })
    }

    /// A helper function to determine whether a match arm requires a trailing comma. Only
    /// `BigExpr` expressions are allowed to omit the trailing comma.
    fn requires_delim(&self) -> bool {
        !self.eval.is_big()
    }
}

impl ContinueExpr {
    /// Consumes a `continue` expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword `continue`, and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        _ends_early: bool,
        _containing_token: Option<&Token>,
        _errors: &mut Vec<Error>,
    ) -> Result<ContinueExpr, Option<usize>> {
        // Currently, this function is simple; we don't have labels, so continue expressions are
        // only the keyword.
        //
        // Because we're allowed to assume that the starting token is the keyword `continue`, we
        // essentially don't need to do any parsing. Even though we could just return the first
        // token, we'll double-check that it *is* `continue`.
        let src = assert_token!(
            tokens.first() => "keyword `continue`",
            Ok(t) && TokenKind::Keyword(Kwd::Continue) => t,
        );

        Ok(ContinueExpr {
            src: src.span(file),
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Path                                                                                         //
//   * PathComponent                                                                              //
// * ElseBranch                                                                                   //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A path to an item in scope
///
/// The standard image of a path contains no generic arguments: it is simply a chain of identifiers
/// linked together by dots (`"."`). Note, however, that they *can* have generics arguments at any
/// component. For example, `foo<i64>.Bar<String>` is a valid path.
///
/// Because of their usage of generics arguments, certain ambiguities arise within expression
/// parsing - this is not managed by the primary parser provided by this type.
///
/// For reference, the BNF is defined as:
/// ```text
/// Path = Ident [ GenericsArgs ] { "." Ident [ GenericsArgs ] } .
/// ```
///
/// The helper type [`PathComponent`] is defined as well to manage the token sources for individual
/// elements, where its BNF is:
/// ```text
/// PathComponent = Ident [ GenericsArgs ] .
/// ```
///
/// [`PathComponent`]: struct.PathComponent.html
#[derive(Debug, Clone, Consumed)]
pub struct Path {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(components.consumed() + components.len() - 1)]
    pub components: Vec<PathComponent>,
}

/// A single component of a type
///
/// For more information, refer to the documentation of [`Path`](struct.Path.html).
#[derive(Debug, Clone, Consumed)]
pub struct PathComponent {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub name: Ident,
    pub generics_args: Option<GenericsArgs>,
}

/// An `else` branch, for use after `if` conditions and various loops
///
/// Unlike many languages, which only allow `else` to be used after `if` conditions, we
/// additionally allow "`else` branches" to be added after any conditional loop (i.e. `for`,
/// `while` and `do..while`). On top of this, we allow more than just block expressions as `else`
/// branches; anything in the `BigExpr` class is allowed here.
///
/// The relevant BNF definitions for these are:
/// ```text
/// ElseBranch = "else" BigExpr .
/// BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr | StructExpr .
/// ```
#[derive(Debug, Clone, Consumed)]
pub struct ElseBranch {
    #[consumed(@ignore)]
    pub(super) src: Span,
    #[consumed(expr.consumed() + 1)] // +1 for "else" keyword
    pub expr: Expr,
}

impl Path {
    /// Consumes a `Path` as a prefix of the given tokens
    ///
    /// Note that this function should not be used where there may be ambiguity with generics
    /// arguments (primarily within expression parsing). Additionally, this function should not be
    /// used if a dot (`"."`) is allowed after a path at the desired position; it will be parsed as
    /// a path separator and will expect a following path component.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Path, Option<usize>> {
        // We always require a first element in the path
        let fst = PathComponent::consume(file, tokens, None, ends_early, containing_token, errors)
            .map_err(|_| None)?;
        let mut consumed = fst.consumed();

        let mut components = vec![fst];

        loop {
            // If we find a path separator token ("."), we'll look for another path component
            match tokens.get(consumed) {
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Dot) => consumed += 1,
                    _ => break,
                },
                _ => break,
            };

            let next = PathComponent::consume(
                file,
                &tokens[consumed..],
                Some(&tokens[..consumed]),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(|_| None)?;
            consumed += next.consumed();
            components.push(next);
        }

        Ok(Path {
            src: Source::slice_span(file, &tokens[..consumed]),
            components,
        })
    }
}

impl PathComponent {
    /// Consumes a single `PathComponent` as a prefix of the given tokens
    ///
    /// This exists solely as a helper function for [`Path::consume`].
    ///
    /// [`Path::consume`]: struct.Path.html#method.consume
    pub fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        prev_tokens: Option<TokenSlice>,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<PathComponent, Option<usize>> {
        // Path components are composed of - at most - two pieces: an identifier and optional
        // generic arguments.
        let ctx = PathComponentContext {
            prev_tokens: prev_tokens.map(|ts| Source::slice_span(file, ts)),
        };

        let name = Ident::parse(
            file,
            tokens.first(),
            IdentContext::PathComponent(ctx),
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|_| None)?;

        let mut consumed = name.consumed();

        let generics_args = GenericsArgs::try_consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|_| None)?;

        consumed += generics_args.consumed();

        Ok(PathComponent {
            src: Source::slice_span(file, &tokens[..consumed]),
            name,
            generics_args,
        })
    }
}

impl ElseBranch {
    /// Attempts to consume an "else branch" as a prefix of the given tokens, returning `Ok(None)`
    /// only if they do not start with the keyword `else`
    fn try_consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Option<ElseBranch>, Option<usize>> {
        let else_token = match tokens.first() {
            Some(Err(_)) | None => return Ok(None),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Else) => Source::token(file, t),
                _ => return Ok(None),
            },
        };

        let ctx = BigExprContext::Else(else_token);
        Expr::consume_big(
            file,
            &tokens[1..],
            ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + 1)))
        .map(|expr| {
            let consumed = expr.consumed() + 1;
            Some(ElseBranch {
                src: Source::slice_span(file, &tokens[consumed..]),
                expr,
            })
        })
    }
}
