//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Named(PathComponent<'a>),
    PrefixOp(Box<PrefixOpExpr<'a>>),
    BinOp(Box<BinOpExpr<'a>>),
    PostfixOp(PostfixOpExpr<'a>),
    Struct(StructExpr<'a>),
    Array(ArrayExpr<'a>),
    Tuple(TupleExpr<'a>),
    Block(BlockExpr<'a>),
    AmbiguousBlock(AmbiguousBlockExpr<'a>),
    For(Box<ForExpr<'a>>),
    While(WhileExpr<'a>),
    DoWhile(DoWhileExpr<'a>),
    Loop(LoopExpr<'a>),
    If(IfExpr<'a>),
    Match(MatchExpr<'a>),
    Continue(ContinueExpr<'a>),
}

/// The types of delimeters that may occur around expression parsing
///
/// The outer delimeter context is necessary for expression parsing because certain assumptions can
/// only be made given the outer context. For example, take the following expression:
/// ```text
/// Foo<T, S> { x: bar() }
///      ^ disambiguation point
/// ```
/// If we're able to deduce that the comma cannot be interpreted as a delimeter between
/// *expressions*, then we can immediately parse the first half of the expression as an identifier
/// with generic arguments. On the other hand, if this isn't known - e.g. if the expression occurs
/// in a context such as the following - we must wait longer to disambiguate.
/// ```text
/// (1, Foo<T,S> { x: bar() }
///                 ^ disambiguation point
/// ```
///
/// In addition to "temporary" ambiguity like the case above, it is sometimes impossible to know
/// during parsing how the input tokens should be interpreted. Take the following for example:
/// ```text
/// (foo<T, S>(bar + 1))
/// ```
/// This could either constitute a single function-call expression (i.e. with generic function
/// `foo`) or as two comparison expressions (the first being between `foo` and `T`, and the second
/// between `S` and `(bar + 1)`). There are a few different ways that this ambiguity can appear
/// inside comma-delimited lists, and a separate class of ambiguities that can appear where colons
/// are allowed (e.g. struct instantiation). Some of these are listed below:
///
/// | Context     | Expression                           |
/// |-------------|--------------------------------------|
/// | Tuple/Array | `foo<T, S> ( x + y, z )`             |
/// | Tuple/Array | `foo<U, T, S> { x: y, z }`*          |
/// | Tuple/Array | `foo<T, Bar<S, U>> ( x + y, z )`     |
/// | Struct      | `foo: bar<T, x: Baz, y: T> (z)`      |
/// \* Not semantically valid (no implementation of `Ord` for anonymous structs)
#[derive(Copy, Clone, Debug)]
pub enum ExprDelim {
    /// Expressions that occur within tuple or array literals
    Comma,
    /// Expressions that occur within struct instantiation
    StructFields,
    /// Expressions that occur as part of function arguments
    FnArgs,
    Nothing,
}

/// A helper type for use by [`Expr::consume_delimited`]
///
/// This provides a uniform representation of the various bits of information that may be used to
/// construct a single field or element under different expression contexts. This type is then used
/// by the restriction that the ambiguous fields produced by `Expr::consume_delimited` implement
/// `From<Delimited<'a>>`, with the additional assumption that each instance of `Delimited` given
/// to them satisfies the intended requirements (e.g. tuple elements are not named, struct fields
/// require a name, etc).
///
/// [`Expr::consume_delimited`]: enum.Expr.html#method.consume_delimited
#[derive(Debug)]
struct Delimited<'a> {
    src: TokenSlice<'a>,
    name: Option<Ident<'a>>,
    expr: Option<Expr<'a>>,
}

/// A helper type for managing the various ambiguities in parsing
///
/// All syntax ambiguities unable to be resolved at parse-time can be determined later, with the
/// addition of type information. This is exposed here, with the two variants for allowing
/// ambiguities to be mixed in with concrete values.
///
/// ## Examples
/// ### Bastion of the turbofish
///
/// We'll go through a couple examples here to explain (and justify) the usage of this type. The
/// first is the "simple" ambiguous case presented in Rust's iconic ["bastion of the turbofish"]:
/// ```
/// let (oh, woe, is, me) = ("the", "Turbofish", "remains", "undefeated");
/// let _ = (oh<woe, is>(me));
/// ```
/// If we were to ignore the first line, we'd see two different possibilities the internals of the
/// tuple literal on the second line: either `oh` as taking generic arguments `woe` and `is`, with
/// a single argument `me` **OR** with all of the above as values, producing two comparison
/// expressions. We can determine from the type information which one of these it should be, but we
/// don't have access to that information at parse-time. As such, we'd produce tuple contents that
/// look something like this:
/// ```
/// use Ambiguous::Known;
///
/// let contents = [
///     Ambiguous::Conditional {
///         all_generic: "oh<woe, is>(me)",
///         generics: [ ("oh", ["oh<woe", "is>(me)"]) ],
///     },
/// ];
/// ```
/// We're using strings here as a simpler medium for demonstrating this - note that these are not
/// *actually* represented using strings, but the full AST types.
///
/// Once we have this structure, it's a simple matter to refine the AST later, with more type
/// information available.
///
/// ["bastion of the turbofish"]: https://github.com/rust-lang/rust/blob/2155adbc3aeb4b38466a7127a7f4e92a8f8fc4e5/src/test/ui/bastion-of-the-turbofish.rs
///
/// ### A more complex example
///
/// There are other, more complex ways that ambiguity can occur (taking into account both temporary
/// and permenant ambiguity). Let's take the following expression as an example:
/// ```
/// (foo<T,S>(y) + bar<T,S>(z))
/// ```
/// This ambiguous expression could represent any of the following *three* lists:
/// ```text
/// ["foo<T,S>(y) + bar<T,S>(z)"]
/// ["foo<T", "S>(y) + bar<T,S>(z)"]
/// ["foo<T,S>(y) + bar<T",S>(z)"]
/// ```
///
/// This is an important detail to note: that there's only three possibilities here is a result of
/// the general formula for the number of differnet possible interpretations for a single ambiguous
/// expression. If we have `n` ambiguous sub-expressions that may involve generics arguments, we
/// can have at most `n + 1` possible valid interpretations.
///
/// To see why this is the case, we'll look at the excluded example from above:
/// ```text
/// ["foo<T", "S>(y) + bar<T", "S>(z)"]
/// ```
/// Here, because we've interpreted both `foo` and `bar` as not having generics arguments, we end
/// up with chained comparison (of the form `x > y < z`) between them. This happens for any number
/// of chained sub-expressions with a similar form to `foo` or `bar`, and so we get our upper bound
/// of `n + 1`.
///
/// We represent this with the `Conditional` variant here - `n` sets of expressions with the
/// `generics` field, and the `+1` from `all_generic`.
#[derive(Debug, Clone)]
pub enum Ambiguous<'a, T> {
    Known(T),
    Conditional {
        /// The singlular expression if all values are generic
        all_generic: T,

        /// The set of expressions that we might interpret the set of tokens as, given that a
        /// determiner expression is *not* generic. These are strictly sorted by when the
        /// determiner expression appears, so that error messages that are seemingly magic can be
        /// given.
        generics: Vec<ConditionalSet<'a, T>>,
    },
}

impl<T: Consumed> Consumed for Ambiguous<'_, T> {
    fn consumed(&self) -> usize {
        match self {
            Ambiguous::Known(t) => t.consumed(),
            Ambiguous::Conditional { all_generic, .. } => all_generic.consumed(),
        }
    }
}

/// A helper type for [`Ambiguous`](#enum.Ambiguous.html)
#[derive(Debug, Clone)]
pub struct ConditionalSet<'a, T> {
    /// The expression that must *not* be generic for the tokens to be interpreted as this set
    determiner: Expr<'a>,
    /// The set of expressions that are must be generic for the tokens to be interpreted as this
    /// set
    implied: Vec<Expr<'a>>,
    set: Vec<T>,
}

struct ExprStacks<'a> {
    base_name: Option<Ident<'a>>,
    base_stack: ExprStack<'a>,
    stacks: Vec<(Option<Ident<'a>>, ExprStack<'a>)>,
}

struct ExprStack<'a> {
    previous_exprs: Vec<(Option<Ident<'a>>, Option<Expr<'a>>)>,
    name: Option<Ident<'a>>,
    total_src: TokenSlice<'a>,
    elems: Vec<ExprStackElement<'a>>,
    last_expr: Option<Expr<'a>>,
}

enum ExprStackElement<'a> {
    BinOp {
        src_offset: usize,
        lhs: Expr<'a>,
        op: BinOp,
        op_src: TokenSlice<'a>,
    },
    PrefixOp {
        src_offset: usize,
        op: PrefixOp<'a>,
        op_src: TokenSlice<'a>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum StackExpecting {
    AtomOrPrefix,
    BinOpOrPostfix,
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
#[derive(Debug, Clone)]
pub struct PrefixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub op_src: TokenSlice<'a>,
    pub op: PrefixOp<'a>,
    pub expr: Box<Expr<'a>>,
}

/// The different prefix operators available for expressions
///
/// This is defined by the following BNF:
/// ```text
/// PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" .
/// ```
///
/// For more information, see [`PrefixOpExpr`](struct.PrefixOpExpr.html).
#[derive(Debug, Clone)]
pub enum PrefixOp<'a> {
    /// `"!"`
    Not,
    /// `"-"`
    Minus,
    /// `"&" [ "mut" ]`
    Ref { is_mut: bool },
    /// `"*"`
    Deref,
    /// "let" Pattern [ ":" Type ] "="
    Let(Pattern<'a>, Option<Type<'a>>),
    /// `"break"`
    Break,
    /// `"return"`
    Return,
}

/// A binary-operator expression, given by the operator and the expressions on either side
///
/// The operator is given by a [`BinOp`] and its source. The relevant BNF definitions are:
/// ```text
/// BinOpExpr = Expr BinOp Expr .
/// BinOp = "+" | "-" | "*" | "/" | "%"
///       | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
///       | "<" | ">" | "<=" | ">=" | "==" | "!=" .
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
#[derive(Debug, Clone)]
pub struct BinOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    lhs: Expr<'a>,
    op_src: TokenSlice<'a>,
    op: BinOp,
    rhs: Expr<'a>,
}

/// The different binary operators available for expressions
///
/// These are defined by the following BNF:
/// ```text
/// BinOp = "+" | "-" | "*" | "/" | "%"
///       | "&" | "|" | "^" | "<<" | ">>" | "&&" | "||"
///       | "<" | ">" | "<=" | ">=" | "==" | "!=" .
/// ```
#[derive(Debug, Clone)]
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
}

/// A postfix-operator expression, given by the operator and the expression to its left.
///
/// Note that *many* types of expressions are included by this that would not typically be
/// considered "postfix" operators. For example, function calls are listed here. The related BNF
/// definitions help to shed some light on this:
/// ```text
/// PostfixOpExpr = Expr PostfixOp .
/// PostfixOp = "[" Expr "]"                # Indexing
///           | "." Ident [ GenericArgs ]   # Field access / method calls
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
#[derive(Debug, Clone)]
pub struct PostfixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Box<Expr<'a>>,
    op: PostfixOp<'a>,
    op_src: TokenSlice<'a>,
}

/// The different types of postfix operators available
///
/// There's complex behavior that's allowed here, which is mostly detailed in the documentation for
/// [`PostfixOpExpr`].
///
/// [`PostfixOpExpr`]: struct.PostfixOpExpr.html
#[derive(Debug, Clone)]
pub enum PostfixOp<'a> {
    /// `"[" Expr "]"`
    Index(Box<Expr<'a>>),
    /// `"." Ident [ GenericArgs ]`
    Access(PathComponent<'a>),
    /// `"." IntLiteral`
    TupleIndex(IntLiteral<'a>),
    /// `"(" [ FnArg { "," FnArg } [ "," ] ] ")"`
    FnCall(Vec<Ambiguous<'a, FnArg<'a>>>),
    /// `StructExpr`
    NamedStruct(StructExpr<'a>),
    /// `"~" Type`
    TypeBinding(Box<Type<'a>>),
    /// `"is" Pattern`
    IsPattern(Pattern<'a>),
    /// `"?"`
    Try,
}

/// An anonymous struct expression, given on its own as an atom or available as a postfix operator
///
/// The fields are individually given by [`StructFieldExpr`]s. The relevant BNF definitions are:
/// ```text
/// StructExpr = "{" [ StructFieldExpr { "," StructFieldExpr } [ "," ] ] "}" .
/// StructFieldExpr = Ident [ ":" Expr ] .
/// ```
/// Like Rust, the expresion used in assignment for the struct definition may be omitted; this is
/// syntax sugar for assigning to a field the value of a local variable with the same name.
///
/// Struct expressions are used in two ways - both as an atomic expression to represent anonymous
/// struct initialization and as a postfix operator to have named struct initialization. The
/// postfix representation is selectively disallowed in certain places (e.g. `if` conditions) due
/// to the ambiguity it causes.
///
/// [`StructFieldExpr`]: struct.StructFieldExpr.html
#[derive(Debug, Clone)]
pub struct StructExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<Ambiguous<'a, StructFieldExpr<'a>>>,
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
#[derive(Debug, Clone)]
pub struct StructFieldExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub value: Option<Expr<'a>>,
}

/// An array literal, given by a comma-separated list of the elements
///
/// The BNF definition for these is:
/// ```text
/// ArrayExpr = "[" [ Expr { "," Expr } [ "," ] ] "]
/// ```
///
/// Like tuple literals, possible syntax ambiguities here mean that we might not know exactly how
/// many elements are represented here before type checking.
#[derive(Debug, Clone)]
pub struct ArrayExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub values: Vec<Ambiguous<'a, Expr<'a>>>,
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
#[derive(Debug, Clone)]
pub struct TupleExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub values: Vec<Ambiguous<'a, Expr<'a>>>,
    pub poisoned: bool,
}

/// A curly-brace enclosed block, containing a list of statments with an optional tail expression
///
/// Block expressions are fairly simple by themselves (they are composed of complex constructs),
/// and are defined by the following BNF:
/// ```text
/// BlockExpr = "{" { Stmt } [ Expr ] "}" .
/// ```
#[derive(Debug, Clone)]
pub struct BlockExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub stmts: Vec<Stmt<'a>>,
    pub tail: Option<Box<Expr<'a>>>,
}

/// A block expression or single-field anonymous struct initialization
///
/// This is of a few forms of ambiguity that cannot be resolved at parse-time, and always has the
/// form `"{" Ident "}"`. This could either be a anonymous struct initialization with the field
/// name abbreviation OR a block expression where the tail expression is the single identifier.
///
/// It is represented by the containing token.
#[derive(Debug, Clone)]
pub struct AmbiguousBlockExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub name: Ident<'a>,
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
#[derive(Debug, Clone)]
pub struct ForExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub pat: Pattern<'a>,
    pub iter: Expr<'a>,
    pub body: BlockExpr<'a>,
    pub else_branch: Option<Box<ElseBranch<'a>>>,
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
#[derive(Debug, Clone)]
pub struct WhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub condition: Box<Expr<'a>>,
    pub body: BlockExpr<'a>,
    pub else_branch: Option<Box<ElseBranch<'a>>>,
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
#[derive(Debug, Clone)]
pub struct DoWhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub body: BlockExpr<'a>,
    pub pred: Box<Expr<'a>>,
    pub else_branch: Option<Box<ElseBranch<'a>>>,
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
#[derive(Debug, Clone)]
pub struct LoopExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub body: BlockExpr<'a>,
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
#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub condition: Box<Expr<'a>>,
    pub body: BlockExpr<'a>,
    pub else_branch: Option<Box<ElseBranch<'a>>>,
}

/// `match` expressions
///
/// `match` expressions provide a way to execute branches conditional on successful destructuring
/// of a certain determinant expression with a pattern. These expressions are defined by the
/// following relevant BNFs:
/// ```text
/// MatchExpr = "match" Expr "{" { MatchArm } "}" .
/// MatchArm  = Pattern [ "if" Expr ] "=>" ( Expr "," | BigExpr "\n" ) .
/// ```
#[derive(Debug, Clone)]
pub struct MatchExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Box<Expr<'a>>,
    pub arms: Vec<MatchArm<'a>>,
    pub poisoned: bool,
}

/// A single `match` arm; a helper type for [`MatchExpr`](#struct.MatchExpr.html)
#[derive(Debug, Clone)]
pub struct MatchArm<'a> {
    pub(super) src: TokenSlice<'a>,
    pub pat: Pattern<'a>,
    pub cond: Option<Expr<'a>>,
    pub eval: Expr<'a>,
}

/// A `continue` expression, to go to the next iteration of a loop
///
/// This is essentially a wrapper type for the single-token source (the keyword `continue`), as a
/// placeholder for more complex syntax that may be added later.
#[derive(Debug, Clone)]
pub struct ContinueExpr<'a> {
    pub(super) src: &'a Token<'a>,
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
        // A reserved binding power primarily for internal use as a way of signifying the highest
        // binding power, plus one.
        ReservedHighest;

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
        // `Expr::consume_path_segment` relies on `BitOr` having higher binding power than the
        // comparison operaors.

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

        // We finish up the list with `break` and `return` as prefix operators
        Break, Return;

        // A reserved binding power primarily for internal use as a way of signifying the lowest
        // binding power, minus one.
        ReservedLowest;
    }
}

impl<'a> Expr<'a> {
    /// Consumes a single expression
    pub fn consume_no_delim(
        tokens: TokenSlice<'a>,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Expr<'a>, Option<usize>> {
        let ambiguous = Expr::consume_delimited(
            tokens,
            ExprDelim::Nothing,
            ExpectedKind::ExprLhs,
            no_structs,
            allow_comparison,
            ends_early,
            containing_token,
            errors,
        )?;

        use Ambiguous::{Conditional, Known};

        match ambiguous {
            Known(ex) => Ok(ex),
            Conditional { .. } => panic!("Expected unambiguous expression, found {:?}", ambiguous),
        }
    }

    /// Parses a curly-brace enclosed block as an expression
    ///
    /// This function handles dispatching between `BlockExpr::parse` and `StructFieldsExpr::parse`
    /// depending on the content of the block. In ambiguous cases (e.g. when we have the input
    /// `{ x }`), `Expr::AmbiguousBlock` is returned instead.
    fn parse_curly_block(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
        outer_src: TokenSlice<'a>,
    ) -> Result<Expr<'a>, ()> {
        let kinds = inner
            .iter()
            .take_while(|res| res.is_ok())
            .map(|t| &t.as_ref().unwrap().kind)
            .take(2)
            .collect::<Vec<_>>();

        use TokenKind::Punctuation;

        match &kinds as &[_] {
            // The fully ambiguous case is when there's a single identifier within a
            // curly-brace-enclosed block. That's what we have here.
            [&TokenKind::Ident(name)] => {
                let name = Ident {
                    src: inner[0].as_ref().unwrap(),
                    name,
                };

                Ok(Expr::AmbiguousBlock(AmbiguousBlockExpr { src, name }))
            }

            // If the second token is either a colon or a comma, it must be a struct instantiation
            // that we're parsing. We'll use `StructFieldsExpr::parse` to do so.
            [TokenKind::Ident(_), Punctuation(Punc::Colon)]
            | [TokenKind::Ident(_), Punctuation(Punc::Comma)] => {
                StructExpr::parse(src, inner, errors).map(Expr::Struct)
            }

            // Otherwise, this is *most likely* a block expression (if not, it's invalid).
            // We'll give EOF as the source because it's only used in cases where the token source
            // is None, which we can clearly see is not the case here.
            _ => BlockExpr::parse(outer_src.first(), false, Source::EOF, errors).map(Expr::Block),
        }
    }

    /// Consumes a list of delimited expressions, determined by the given delimiter
    fn consume_all_delimited<T: From<Delimited<'a>> + Consumed>(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        delim: ExprDelim,
        no_elem_err: ExpectedKind<'a>,
        delim_err: fn(&'a Token<'a>) -> ExpectedKind<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(Vec<Ambiguous<'a, T>>, bool), ()> {
        let mut consumed = 0;
        let ends_early = false;
        let mut poisoned = false;
        let mut exprs = Vec::new();
        let allow_comparison = true;
        let no_structs = None;

        loop {
            match inner.get(consumed) {
                // Running out of tokens is fine - it's the end of the list. We'll break out of the
                // loop to do a normal return.
                None => {
                    if ends_early {
                        poisoned = true;
                    }
                    break;
                }

                Some(_) => {
                    let res = Expr::consume_delimited(
                        &inner[consumed..],
                        delim,
                        no_elem_err,
                        no_structs,
                        allow_comparison,
                        ends_early,
                        Some(src),
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
                        Ok(ambiguous) => {
                            consumed += ambiguous.consumed();
                            exprs.push(ambiguous);
                        }
                    }
                }
            }

            // Between elements, we'll expect trailing commas
            match inner.get(consumed) {
                // If we ran out of tokens, it's because there's no more elements/fields to
                // consume. That's fine, so we'll exit the loop to return normally.
                None => {
                    if ends_early {
                        poisoned = true;
                    }

                    break;
                }

                // If there was a tokenizer error, we'll exit without producing further errors
                // here.
                Some(Err(_)) => {
                    poisoned = true;
                    break;
                }

                // Otherwise, we'll check that we *do* have a trailing comma
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    // If we didn't have one, we'll produce an error
                    _ => {
                        errors.push(Error::Expected {
                            kind: delim_err(src),
                            found: Source::TokenResult(Ok(t)),
                        });

                        poisoned = true;
                        break;
                    }
                },
            }
        }

        Ok((exprs, poisoned))
    }

    /// Consumes a single (possibly ambiguous) expression within a given delimeter context
    fn consume_delimited<T: From<Delimited<'a>>>(
        tokens: TokenSlice<'a>,
        delim: ExprDelim,
        no_elem_err: ExpectedKind<'a>,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Ambiguous<'a, T>, Option<usize>> {
        // This function is a complex beast. Before we get into that, however, we'll perform a
        // small amount of validation to ensure that some of the external invariants we expect to
        // hold *are* indeed true.
        //
        // Essentially, we want to guarantee (for forwards-compatability / resilience) that all
        // options for `delim` either require a name or an expression - and that all values of
        // `delim` that require a name do - in fact - allow names.
        //
        // Only a debug assert because any regression should be caught during testing
        debug_assert!(delim.requires_name() || delim.requires_expr());

        if delim.requires_name() {
            debug_assert!(delim.allows_name());
        }

        // With those brief preliminaries out of the way, let's get into the meat of the function.
        //
        // The primary goal of this function is to return a single, possibly ambiguous,
        // expression/function argument/struct field. This is given by the `Ambiguous<T>` that we
        // return, which *may* itself represent multiple fields.
        //
        // Because of the ambiguity that we need to handle, this parsing must be done with a
        // stack-based model. In order to do this, we clone stacks whenever necessary
        // we create multiple stacks as needed (whenever we encounter something ambiguous)

        let mut stacks = ExprStacks::new(tokens);
        let mut consumed = 0;

        // The first thing we'll do is to optionally consume a leading name, if the delimiter
        // context allows it:
        if delim.allows_name() {
            match tokens.first() {
                // If we ran out of tokens, we'll produce an error here, where we have the
                // additional context that we're expecting a name, in addition to an expression
                None => {
                    if !ends_early {
                        errors.push(Error::Expected {
                            kind: no_elem_err,
                            found: end_source!(containing_token),
                        });
                    }

                    return Err(None);
                }
                Some(Err(_)) => return Err(None),
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Ident(name) => {
                        // If we find a name here, it isn't *necessarily* required. We'll only
                        // register this identifier as a name for the expression if it's followed
                        // by a colon. Whether the colon is strictly required is given by
                        // `delim.requires_name`. If it isn't, we know that we can't produce
                        // something like `Ident ","` using the name because of the invariant that
                        // we checked above:
                        //   delim.requires_name() || delim.requires_expr()
                        //                         <=>
                        //   !delim.requires_name() ==> delim.requires_expr()
                        match tokens.get(2) {
                            Some(Err(_)) | None if !delim.requires_name() => (),
                            Some(Err(_)) | None => {
                                if !ends_early && tokens.get(2).is_none() {
                                    errors.push(Error::Expected {
                                        kind: ExpectedKind::ColonAfterNamedExpr(t),
                                        found: end_source!(containing_token),
                                    });
                                } else if let Some(Err(e)) = tokens.get(2) {
                                    errors.push(Error::Expected {
                                        kind: ExpectedKind::ColonAfterNamedExpr(t),
                                        found: Source::TokenResult(Err(*e)),
                                    });
                                }

                                return Err(None);
                            }
                            Some(Ok(snd)) => match &snd.kind {
                                TokenKind::Punctuation(Punc::Colon) => {
                                    stacks.set_name(Ident { src: t, name });
                                    consumed = 2;
                                }
                                _ if !delim.requires_name() => (),
                                _ => {
                                    errors.push(Error::Expected {
                                        kind: ExpectedKind::ColonAfterNamedExpr(t),
                                        found: Source::TokenResult(Ok(t)),
                                    });

                                    return Err(Some(1));
                                }
                            },
                        }
                    }
                    _ if !delim.requires_name() => (),
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::Ident(IdentContext::NamedExpr(delim)),
                            found: Source::TokenResult(Ok(t)),
                        });

                        return Err(Some(1));
                    }
                },
            }
        }

        loop {
            let src = &tokens[consumed..];

            let res = match stacks.expecting() {
                StackExpecting::AtomOrPrefix => Expr::try_consume_atom_or_prefix(
                    &mut stacks,
                    src,
                    consumed,
                    delim,
                    allow_comparison,
                    ends_early,
                    containing_token,
                    errors,
                ),
                StackExpecting::BinOpOrPostfix => {
                    debug_assert!(!stacks.is_empty());
                    Expr::try_consume_binop_or_postfix(
                        &mut stacks,
                        src,
                        consumed,
                        delim,
                        no_structs,
                        allow_comparison,
                        ends_early,
                        containing_token,
                        errors,
                    )
                }
            };

            match res {
                Ok(Some(c)) => consumed += c,
                Ok(None) if delim.requires_expr() && stacks.is_empty() => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::ExprLhs,
                        found: tokens
                            .get(consumed)
                            .map(Source::from)
                            .unwrap_or_else(|| end_source!(containing_token)),
                    });

                    return Err(None);
                }
                Ok(None) => break,
                Err(None) => return Err(None),
                Err(Some(c)) => return Err(Some(c + consumed)),
            }
        }

        Ok(stacks.finish())
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
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        match tokens.first() {
            Some(Err(_)) | None => Ok(None),
            Some(Ok(_)) => {
                // First, we'll see if we can parse a prefix operator here
                let res = PrefixOp::try_consume(tokens, ends_early, containing_token, errors);
                match res {
                    Ok(None) => (),
                    Ok(Some((op, op_src))) => {
                        let consumed = op_src.len();
                        stacks.push_prefix(already_consumed, op, op_src);
                        return Ok(Some(consumed));
                    }
                    Err(e) => return Err(e),
                }

                // If we can't, we'll try to parse an "atomic" expression - these can be loosely
                // defined as all of the expressoin types that don't involve operators.
                let res = Expr::try_consume_atom(
                    stacks,
                    tokens,
                    already_consumed,
                    delim,
                    allow_comparison,
                    ends_early,
                    containing_token,
                    errors,
                );
                match res {
                    Ok(None) => (),
                    Ok(Some(consumed)) => {
                        return Ok(Some(consumed));
                    }
                    Err(e) => return Err(e),
                }

                // If we couldn't parse a prefix expression or an atom, we'll indicate this
                Ok(None)
            }
        }
    }

    /// Attempts to consume an atomic expression, returning the number of tokens consumed on
    /// success
    ///
    /// `already_consumed` indicates the place in the original consumed expression `tokens` starts,
    /// in order for us to pass it along to the stack values.
    ///
    /// This additionally fully handles the ambiguity that may be present with angle-brackets.
    fn try_consume_atom(
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        // Atomic expressions are defined as any of:
        //   AtomicExpr = Literal | PathComponent | StructExpr | ArrayExpr | TupleExpr | BlockExpr
        //              | ForExpr | WhileExpr | LoopExpr | IfExpr | MatchExpr | ContinueExpr .
        // We'll examine the first token to determine what type of expression we're looking at. If
        // we can't find anything that matches, we'll return `Ok(None)`.

        use Delim::{Curlies, Parens, Squares};

        let expr_res = match tokens.first() {
            Some(Err(_)) | None => return Ok(None),
            // We'll go through each starting token that we listed above, in turn
            Some(Ok(fst_token)) => match &fst_token.kind {
                // Literal
                TokenKind::Literal(_, _) => Literal::consume(tokens).map(Expr::Literal),

                // PathComponent
                TokenKind::Ident(_) if !allow_comparison => {
                    PathComponent::consume(tokens, None, ends_early, containing_token, errors)
                        .map(Expr::Named)
                }
                TokenKind::Ident(_) => {
                    return Expr::consume_ambiguous_ident(
                        stacks,
                        tokens,
                        already_consumed,
                        delim,
                        ends_early,
                        containing_token,
                        errors,
                    );
                }

                // StructExpr or BlockExpr
                TokenKind::Tree {
                    delim: Curlies,
                    inner,
                    ..
                } => {
                    Expr::parse_curly_block(fst_token, inner, errors, tokens).map_err(|()| Some(1))
                }

                // ArrayExpr
                TokenKind::Tree {
                    delim: Squares,
                    inner,
                    ..
                } => ArrayExpr::parse(fst_token, inner, errors)
                    .map(Expr::Array)
                    .map_err(|()| Some(1)),

                // TupleExpr
                TokenKind::Tree {
                    delim: Parens,
                    inner,
                    ..
                } => TupleExpr::parse(fst_token, inner, errors)
                    .map(Expr::Tuple)
                    .map_err(|()| Some(1)),

                // ForExpr
                TokenKind::Keyword(Kwd::For) => {
                    ForExpr::consume(tokens, ends_early, containing_token, errors)
                        .map(|f| Expr::For(Box::new(f)))
                }

                // WhileExpr
                TokenKind::Keyword(Kwd::While) => {
                    WhileExpr::consume(tokens, ends_early, containing_token, errors)
                        .map(Expr::While)
                }

                // LoopExpr
                TokenKind::Keyword(Kwd::Loop) => {
                    LoopExpr::consume(tokens, ends_early, containing_token, errors).map(Expr::Loop)
                }

                // IfExpr
                TokenKind::Keyword(Kwd::If) => {
                    IfExpr::consume(tokens, ends_early, containing_token, errors).map(Expr::If)
                }

                // MatchExpr
                TokenKind::Keyword(Kwd::Match) => {
                    MatchExpr::consume(tokens, ends_early, containing_token, errors)
                        .map(Expr::Match)
                }

                // And finally,
                // ContinueExpr
                TokenKind::Keyword(Kwd::Continue) => {
                    ContinueExpr::consume(tokens, ends_early, containing_token, errors)
                        .map(Expr::Continue)
                }

                _ => return Ok(None),
            },
        };

        match expr_res {
            Err(e) => Err(e),
            Ok(expr) => {
                let consumed = expr.consumed();
                stacks.push_atom(already_consumed, expr);
                Ok(Some(consumed))
            }
        }
    }

    fn consume_ambiguous_ident(
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        todo!()
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
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        // This function only serves to dispatch between the two different functions for binary and
        // postfix operators

        // We'll just call these in sequence, starting with the binary operators:
        match BinOp::try_consume(tokens, allow_comparison, errors) {
            Err(()) => return Err(None),
            Ok(None) => (),
            Ok(Some((op, op_src))) => {
                let consumed = op_src.len();
                stacks.push_binop(already_consumed, op, op_src);
                return Ok(Some(consumed));
            }
        }

        PostfixOp::try_consume(
            stacks,
            tokens,
            already_consumed,
            delim,
            no_structs,
            allow_comparison,
            ends_early,
            containing_token,
            errors,
        )
    }

    /// Returns whether the expression is "big"
    ///
    /// This is essentially defined by the following BNF:
    /// ```text
    /// BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr .
    /// ```
    fn is_big_expr(&self) -> bool {
        use Expr::*;

        match self {
            If(_) | Match(_) | For(_) | While(_) | Loop(_) | Block(_) | AmbiguousBlock(_) => true,
            Literal(_) | Named(_) | PrefixOp(_) | BinOp(_) | PostfixOp(_) | Struct(_)
            | Array(_) | Tuple(_) | DoWhile(_) | Continue(_) => false,
        }
    }

    /// Returns whether the given must start an expression
    ///
    /// This returns true exactly when the start of the tokens can be either a prefix operator or
    /// an atom - and specifically cannot be a binary or postfix operator.
    fn must_be_expr_start(tokens: TokenSlice) -> bool {
        let token = match tokens.first() {
            Some(Err(_)) | None => return false,
            Some(Ok(t)) => t,
        };

        // There are many tokens that *could* start an expression, but there aren't as many that
        // *must*. Informally, the set of tokens that must start an expression is given by:
        //   MustStart = (PrefixOp ∪ Atom) / (BinOp ∪ PostfixOp)
        // As such, we get the following list:
        //   "!", "&mut", "break", "return", "let", Literal, Ident,
        //   "for", "while", "do", "loop", "if", "match", "continue"

        match &token.kind {
            TokenKind::Punctuation(Punc::Not)
            | TokenKind::Keyword(Kwd::Break)
            | TokenKind::Keyword(Kwd::Return)
            | TokenKind::Keyword(Kwd::Let)
            | TokenKind::Literal(_, _)
            | TokenKind::Ident(_)
            | TokenKind::Keyword(Kwd::For)
            | TokenKind::Keyword(Kwd::While)
            | TokenKind::Keyword(Kwd::Do)
            | TokenKind::Keyword(Kwd::Loop)
            | TokenKind::Keyword(Kwd::If)
            | TokenKind::Keyword(Kwd::Match)
            | TokenKind::Keyword(Kwd::Continue) => true,

            // We need to handle "&mut" as a separate case because there's two tokens required here
            TokenKind::Punctuation(Punc::And) => match tokens.get(1) {
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Keyword(Kwd::Mut) => true,
                    _ => false,
                },
                _ => false,
            },

            // Everything else (clearly) does not start an expression
            _ => false,
        }
    }
}

impl ExprDelim {
    /// A convenience method to return whether the expression delimeter context requires the first
    /// two tokens to be `Ident ":"` as a field name
    ///
    /// This returns true precisely if the `ExprDelim` is the `StructFields` variant.
    fn requires_name(&self) -> bool {
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
    fn allows_name(&self) -> bool {
        match self {
            ExprDelim::StructFields | ExprDelim::FnArgs => true,
            ExprDelim::Comma | ExprDelim::Nothing => false,
        }
    }

    /// A convenience method to return whether the expression delimiter requires that there be a
    /// full expression (with or without a name)
    ///
    /// This returns true for every value but `StructFields`, where the delimiter may be omitted.
    fn requires_expr(&self) -> bool {
        match self {
            ExprDelim::Comma | ExprDelim::FnArgs | ExprDelim::Nothing => true,
            ExprDelim::StructFields => false,
        }
    }

    /// Returns whether the `ExprDelim` is the `Nothing` variant
    fn is_nothing(&self) -> bool {
        match self {
            ExprDelim::Nothing => true,
            _ => false,
        }
    }
}

impl<'a> ExprStacks<'a> {
    /// Creates a new, blank `ExprStacks`
    const fn new(total_src: TokenSlice<'a>) -> ExprStacks<'a> {
        ExprStacks {
            base_name: None,
            base_stack: ExprStack::new(total_src),
            stacks: Vec::new(),
        }
    }

    /// Sets the base name of the stacks
    ///
    /// This can only be done before any changes have been made to the `ExprStacks`, and so will
    /// panic if either: (1) the name has already been set, or (2) the stack is not empty (as given
    /// by [`is_empty`]).
    ///
    /// [`is_empty`]: #method.is_empty
    fn set_name(&mut self, name: Ident<'a>) {
        assert!(self.base_name.is_none());
        assert!(self.is_empty());
        self.base_name = Some(name);
    }

    /// Returns syntax element that the stack is currently expecting
    fn expecting(&self) -> StackExpecting {
        self.base_stack.expecting()
    }

    /// Returns whether the stack is empty
    ///
    /// This will be true only before any expression pieces have been added to the stack(s).
    fn is_empty(&self) -> bool {
        self.base_stack.is_empty()
    }

    /// Finalizes the expression stack, expecting that the expression if it exists *can* be valid
    fn finish<T: From<Delimited<'a>>>(mut self) -> Ambiguous<'a, T> {
        self.collapse_bp_gt(BindingPower::ReservedLowest);
        // Because of how we produce the stacks, the base stack should never have other resolved
        // expressions within it
        assert!(self.base_stack.previous_exprs.is_empty());

        todo!()
    }

    /// Collapses the current expression stack, up to the given binding power
    ///
    /// Typical usage of this will be to produce the left-hand side of a binary or postfix
    /// operator with left binding power given by `bp`.
    fn collapse_bp_gt(&mut self, bp: BindingPower) {
        self.base_stack.collapse_bp_gt(bp);
        self.stacks
            .iter_mut()
            .for_each(|(_, s)| s.collapse_bp_gt(bp));
    }

    /// Pushes the given prefix operator onto the stack
    fn push_prefix(&mut self, src_offset: usize, op: PrefixOp<'a>, op_src: TokenSlice<'a>) {
        for (_, s) in self.stacks.iter_mut() {
            s.elems.push(ExprStackElement::PrefixOp {
                src_offset,
                op: op.clone(),
                op_src,
            });
        }
        self.base_stack.elems.push(ExprStackElement::PrefixOp {
            src_offset,
            op,
            op_src,
        });
    }

    /// Pushes the given atomic expression onto the stack
    ///
    /// This will panic if we aren't expecting one (i.e. if `self.expecting() != AtomOrPrefix`).
    fn push_atom(&mut self, src_offset: usize, expr: Expr<'a>) {
        for (_, s) in self.stacks.iter_mut() {
            assert!(s.last_expr.is_none());
            s.last_expr = Some(expr.clone());
        }
        assert!(self.base_stack.last_expr.is_none());
        self.base_stack.last_expr = Some(expr);
    }

    /// Pushes the given binary operator onto the stack
    fn push_binop(&mut self, src_offset: usize, op: BinOp, op_src: TokenSlice<'a>) {
        for (_, s) in self.stacks.iter_mut() {
            s.push_binop(src_offset, op.clone(), op_src);
        }
        self.base_stack.push_binop(src_offset, op, op_src);
    }

    fn push_postfix(&mut self, src_offset: usize, op: PostfixOp<'a>, op_src: TokenSlice<'a>) {
        for (_, s) in self.stacks.iter_mut() {
            s.push_postfix(src_offset, op.clone(), op_src);
        }
        self.base_stack.push_postfix(src_offset, op, op_src);
    }
}

impl<'a> ExprStack<'a> {
    const fn new(total_src: TokenSlice<'a>) -> Self {
        ExprStack {
            previous_exprs: Vec::new(),
            name: None,
            total_src,
            elems: Vec::new(),
            last_expr: None,
        }
    }

    fn is_empty(&self) -> bool {
        self.last_expr.is_none() && self.elems.is_empty()
    }

    fn expecting(&self) -> StackExpecting {
        match self.last_expr {
            None => StackExpecting::AtomOrPrefix,
            Some(_) => StackExpecting::BinOpOrPostfix,
        }
    }

    fn collapse_bp_gt(&mut self, bp: BindingPower) {
        assert!(self.is_empty() || self.last_expr.is_some());

        let mut rhs = match self.last_expr.take() {
            None => return,
            Some(ex) => ex,
        };

        while let Some(elem) = self.elems.pop() {
            match elem {
                ExprStackElement::BinOp {
                    src_offset,
                    lhs,
                    op,
                    op_src,
                } => {
                    // There's a little bit of explanation necessary for the choice of strictly
                    // less-than in the condition below. We'll use this example:
                    //   Given a stack and last expression that reads
                    //      [ BinOp(1, +) ]; Some(Expr(2))
                    //   and supposing we encounter the token `+`, we want to collapse the existing
                    //   stack and expression to
                    //      [ ]; Some(Expr(1 + 2))
                    //   which we then turn into:
                    //      [ BinOp(1 + 2, +) ]; None
                    //   after applying the token
                    //
                    // The collapsing process above will be done with a call to this function, so we
                    // want to collapse even if the operator's binding power is equal to the binding
                    // power we were given - i.e. only if the operator's binding power is strictly
                    // less than this `bp` will we stop collapsing the stack.
                    if op.bp() < bp {
                        self.elems.push(ExprStackElement::BinOp {
                            src_offset,
                            lhs,
                            op,
                            op_src,
                        });
                        break;
                    }

                    let size = lhs.consumed() + op_src.len() + rhs.consumed();
                    let src = &self.total_src[src_offset..src_offset + size];

                    rhs = Expr::BinOp(Box::new(BinOpExpr {
                        src,
                        lhs,
                        op,
                        op_src,
                        rhs,
                    }))
                }
                ExprStackElement::PrefixOp {
                    src_offset,
                    op,
                    op_src,
                } => {
                    // See justification for `<` here (instead of `<=`) above
                    if op.bp() < bp {
                        self.elems.push(ExprStackElement::PrefixOp {
                            src_offset,
                            op,
                            op_src,
                        });
                        break;
                    }

                    let size = op_src.len() + rhs.consumed();
                    let src = &self.total_src[src_offset..src_offset + size];
                    rhs = Expr::PrefixOp(Box::new(PrefixOpExpr {
                        src,
                        op,
                        op_src,
                        expr: Box::new(rhs),
                    }))
                }
            }
        }

        self.last_expr = Some(rhs);
    }

    fn push_binop(&mut self, src_offset: usize, op: BinOp, op_src: TokenSlice<'a>) {
        self.collapse_bp_gt(op.bp());
        let lhs = self.last_expr.take().unwrap();
        let elem = ExprStackElement::BinOp {
            src_offset: src_offset - lhs.consumed(),
            lhs,
            op,
            op_src,
        };
        self.elems.push(elem);
    }

    fn push_postfix(&mut self, src_offset: usize, op: PostfixOp<'a>, op_src: TokenSlice<'a>) {
        self.collapse_bp_gt(op.bp());
        let expr = self.last_expr.take().unwrap();

        let src = &self.total_src[src_offset - expr.consumed()..src_offset + op_src.len()];
        self.last_expr = Some(Expr::PostfixOp(PostfixOpExpr {
            src,
            expr: Box::new(expr),
            op,
            op_src,
        }));
    }
}

impl<'a> PrefixOp<'a> {
    /// Returns the binding power of the prefix operator
    fn bp(&self) -> BindingPower {
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
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<(PrefixOp<'a>, TokenSlice<'a>)>, Option<usize>> {
        // Because the set of prefix operators is so limited, we'll just go through all of the
        // cases here.
        //
        // Before we do, however, we'll define a little helper macro to make our returns a little
        // cleaner.
        macro_rules! op {
            ($kind:ident) => {{
                Ok(Some((PrefixOp::$kind, &tokens[..1])))
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

                    Ok(Some((PrefixOp::Ref { is_mut }, &tokens[..1])))
                }

                // There's a dedicated function for let expressions, so we'll use that:
                TokenKind::Keyword(Kwd::Let) => {
                    PrefixOp::consume_let(tokens, ends_early, containing_token, errors).map(Some)
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
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(PrefixOp<'a>, TokenSlice<'a>), Option<usize>> {
        // Let prefixes aren't *too* bad to parse - the BNF is simply:
        //   "let" Pattern [ ":" Type ] "="
        //
        // We're given that the first token is the keyword `let`, so we'll panic if we find that's
        // not the case.
        let let_kwd = match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Let) => t,
                k => panic!("Expected keyword 'let', found token kind {:?}", k),
            },
            _ => panic!("Expected keyword 'let', found {:?}", tokens.first()),
        };

        let mut consumed = 1;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let pat_ctx = PatternContext::Let(let_kwd);
        let pat = Pattern::consume(
            &tokens[consumed..],
            pat_ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;

        consumed += pat.consumed();
        let pat_src = &tokens[1..consumed];

        // If we have a ":" token following the pattern, we'll expect a type
        let ty = expect!((
            // If we find a "=", that's fine because it's what we'll expect next anyways.
            TokenKind::Punctuation(Punc::Eq) => None,
            TokenKind::Punctuation(Punc::Colon) => {
                consumed += 1;
                let ty_res = Type::consume(
                    &tokens[consumed..],
                    TypeContext::LetHint(LetContext {
                        let_kwd,
                        pat: pat_src,
                    }),
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
            @else ExpectedKind::LetColonOrEq(LetContext {
                let_kwd,
                pat: &tokens[1..consumed],
            })
        ));

        // Now, we'll expect an equals for assigning the value as the last token in this prefix
        // operator
        expect!((
            TokenKind::Punctuation(Punc::Eq) => consumed += 1,
            @else ExpectedKind::LetEq(LetContext {
                let_kwd,
                pat: pat_src,
            })
        ));

        // And with that all done, we'll return the prefix operator
        Ok((PrefixOp::Let(pat, ty), &tokens[..consumed]))
    }
}

impl BinOp {
    /// Returns the binding power of the binary operator
    fn bp(&self) -> BindingPower {
        use BindingPower::*;

        match self {
            BinOp::Add => Add,
            BinOp::Sub => Sub,
            BinOp::Mul => Mul,
            BinOp::Div => Div,
            BinOp::Mod => Mod,
            BinOp::BitAnd => BitAnd,
            BinOp::BitOr => BitOr,
            BinOp::BitXor => BitXor,
            BinOp::Shl => Shl,
            BinOp::Shr => Shr,
            BinOp::LogicalAnd => LogicalAnd,
            BinOp::LogicalOr => LogicalOr,
            BinOp::Lt => Lt,
            BinOp::Gt => Gt,
            BinOp::Le => Le,
            BinOp::Ge => Ge,
            BinOp::Eq => Eq,
            BinOp::Ne => Ne,
        }
    }

    /// Attempts to consume a binary operator as a prefix of the given tokens
    ///
    /// This will return `Err(())` only if we encounter a comparison operator when
    /// `allow_comparison` is `false`.
    fn try_consume<'a>(
        tokens: TokenSlice<'a>,
        allow_comparison: bool,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<(BinOp, TokenSlice<'a>)>, ()> {
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
                Ok(Some((BinOp::$kind, &tokens[..$len])))
            }};
        }

        let kind = |idx: usize| Some(&tokens.get(idx)?.as_ref().ok()?.kind);
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

        // Like we said before, we'll match on the first two tokens. More specifically, we can only
        let first_two = [kind(0), no_trail(0).and_then(|()| kind(1))];

        match &first_two {
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
            punc!(Or) => op!(BitOr),
            punc!(Caret) => op!(BitXor),
            // The same goes for bitshifts
            punc!(Lt, Lt) if allow_comparison => op!(Shl, 2),
            punc!(Gt, Gt) if allow_comparison => op!(Shr, 2),
            punc!(Lt) if allow_comparison => op!(Lt),
            punc!(Gt) if allow_comparison => op!(Gt),
            punc!(Le) => op!(Le),
            punc!(Ge) => op!(Ge),
            punc!(EqEq) => op!(Eq),
            punc!(NotEq) => op!(Ne),

            // And now we handle the comparison operator-related errors.
            // Finding "less-than" is relatively ok - we know that any ambiguity would have already
            // been handled; we're safe to emit an error here.
            punc!(Lt) if !allow_comparison => {
                errors.push(Error::ComparisonExprDisallowed {
                    source: &tokens[..1],
                });

                Err(())
            }
            // On the other hand, finding a `>` might be the end of generics arguments OR it might
            // be intended to be part of an expression! If we're certain that this `>` must be part
            // of some generics
            punc!(Gt) if !allow_comparison => {
                let start = match &first_two[1] {
                    Some(&TokenKind::Punctuation(Punc::Gt)) => 2,
                    _ => 1,
                };

                if Expr::must_be_expr_start(&tokens[start..]) {
                    errors.push(Error::ComparisonExprDisallowed {
                        source: &tokens[..start],
                    });

                    Err(())
                } else {
                    // If we aren't sure, then this `>` should be interpreted as the end of the
                    // enclosing generics arguments.
                    Ok(None)
                }
            }

            _ => Ok(None),
        }
    }
}

impl<'a> PostfixOp<'a> {
    /// Returns the binding power of the postfix operator
    fn bp(&self) -> BindingPower {
        use BindingPower::*;

        match self {
            PostfixOp::Index(_) => Index,
            PostfixOp::Access(_) => Access,
            PostfixOp::TupleIndex(_) => TupleIndex,
            PostfixOp::FnCall(_) => FnCall,
            PostfixOp::NamedStruct(_) => NamedStruct,
            PostfixOp::TypeBinding(_) => TypeBinding,
            PostfixOp::IsPattern(_) => IsPattern,
            PostfixOp::Try => Try,
        }
    }

    /// Attempts to consume a postfix operator of the given tokens, adding it to the stack on
    /// success
    ///
    /// On success, this will return the number of tokens consumed
    ///
    /// This function additionally handles the ambiguity that may be present with less-than (`<`)
    /// following identifiers - hence why it takes `stacks`. Note that if a *truly* ambiguous case
    /// occurs, we'll additionally handle the pieces of the expression resulting from that
    /// ambiguity.
    fn try_consume(
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        // The large majority of this function is spent producing the various operators that we
        // might use. Because of a *single* special case, we can't make this the return type, so we
        // let the match expression evaluate to the operator and handle it all at the bottom of the
        // function.

        let op_res = match tokens.first() {
            // Because some tokenizer error tokens *could* represent syntax that's valid at that
            // immediate point, we need to explicitly filter out the errors here so we don't emit a
            // double error for them.
            //
            // All delimiters can represent a postfix operator, so we explicitly account for
            // unclosed delimiters here.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => return Err(None),

            // For everything else, we just indicate that we couldn't find a postfix operator
            Some(Err(_)) | None => return Ok(None),

            // The postfix operators are given by the following BNF definition:
            //   PostfixOp = "[" Expr "]"                # Indexing
            //             | "." Ident [ GenericArgs ]   # Field / method access
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
                            // TODO because we need to take `no_structs` into account
                            todo!()
                            /*
                            StructExpr::parse(fst_token, inner, errors)
                            .map(PostfixOp::NamedStruct)
                            */
                        }
                        Delim::Parens => PostfixOp::parse_fn_args(fst_token, inner, errors),
                        Delim::Squares => PostfixOp::parse_index(fst_token, inner, errors),
                    };

                    res.map_err(|()| Some(1)).map(|op| (op, &tokens[..1]))
                }

                // We'll follow with the only two other "simple" cases
                //
                // The "try" operator is *really* simple:
                TokenKind::Punctuation(Punc::Question) => Ok((PostfixOp::Try, &tokens[..1])),

                // "is" patterns are also relatively simple, so we don't both with a separate
                // function here either.
                TokenKind::Keyword(Kwd::Is) => {
                    let res = Pattern::consume(
                        &tokens[1..],
                        PatternContext::Is(fst_token),
                        ends_early,
                        containing_token,
                        errors,
                    );

                    match res {
                        Err(Some(c)) => Err(Some(c + 1)),
                        Err(None) => Err(None),
                        Ok(pat) => {
                            let src = &tokens[..1 + pat.consumed()];
                            Ok((PostfixOp::IsPattern(pat), src))
                        }
                    }
                }

                // The rest of the postfix operators are fairly complicated, unfortunately - this
                // is why this function is given the stacks as input directly.
                //
                // We use separate, dedicated functions to handle these instead
                TokenKind::Punctuation(Punc::Dot) => {
                    return PostfixOp::consume_dot(
                        stacks,
                        tokens,
                        already_consumed,
                        delim,
                        no_structs,
                        allow_comparison,
                        ends_early,
                        containing_token,
                        errors,
                    );
                }
                TokenKind::Punctuation(Punc::Tilde) => PostfixOp::consume_type_binding(
                    tokens,
                    delim,
                    no_structs,
                    allow_comparison,
                    ends_early,
                    containing_token,
                    errors,
                ),

                // If the set of tokens clearly doesn't start with a postfix operator, we'll
                // indicate as such
                _ => return Ok(None),
            },
        };

        match op_res {
            Err(e) => Err(e),
            Ok((op, op_src)) => {
                let consumed = op_src.len();
                stacks.push_postfix(already_consumed, op, op_src);
                Ok(Some(consumed))
            }
        }
    }

    fn parse_fn_args(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PostfixOp<'a>, ()> {
        todo!()
    }

    /// Parses the contents of a square-bracket-delimited token tree as a single expression for
    /// indexing
    fn parse_index(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PostfixOp<'a>, ()> {
        todo!()
    }

    fn consume_dot(
        stacks: &mut ExprStacks<'a>,
        tokens: TokenSlice<'a>,
        already_consumed: usize,
        delim: ExprDelim,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<usize>, Option<usize>> {
        todo!()
    }

    fn consume_type_binding(
        tokens: TokenSlice<'a>,
        delim: ExprDelim,
        no_structs: Option<NoCurlyContext>,
        allow_comparison: bool,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(PostfixOp<'a>, TokenSlice<'a>), Option<usize>> {
        todo!()
    }
}

impl<'a> StructExpr<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<StructExpr<'a>, ()> {
        let (fields, poisoned) = Expr::consume_all_delimited(
            src,
            inner,
            ExprDelim::StructFields,
            ExpectedKind::StructFieldExpr,
            ExpectedKind::StructFieldExprDelim,
            errors,
        )?;

        Ok(StructExpr {
            src,
            fields,
            poisoned,
        })
    }
}

impl<'a> From<Delimited<'a>> for StructFieldExpr<'a> {
    fn from(delim: Delimited<'a>) -> Self {
        assert!(delim.name.is_some());

        StructFieldExpr {
            src: delim.src,
            name: delim.name.unwrap(),
            value: delim.expr,
        }
    }
}

impl<'a> ArrayExpr<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ArrayExpr<'a>, ()> {
        let (values, poisoned) = Expr::consume_all_delimited(
            src,
            inner,
            ExprDelim::Comma,
            ExpectedKind::ArrayElement,
            ExpectedKind::ArrayDelim,
            errors,
        )?;

        Ok(ArrayExpr {
            src,
            values,
            poisoned,
        })
    }
}

impl<'a> TupleExpr<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TupleExpr<'a>, ()> {
        let (values, poisoned) = Expr::consume_all_delimited(
            src,
            inner,
            ExprDelim::Comma,
            ExpectedKind::TupleElement,
            ExpectedKind::TupleDelim,
            errors,
        )?;

        Ok(TupleExpr {
            src,
            values,
            poisoned,
        })
    }
}

impl<'a> From<Delimited<'a>> for Expr<'a> {
    fn from(delim: Delimited<'a>) -> Expr<'a> {
        assert!(delim.name.is_none());

        delim.expr.unwrap()
    }
}

impl<'a> BlockExpr<'a> {
    /// Parses a block expression from the given token
    ///
    /// Because block expressions are always given by the curly braces they're enclosed by, the
    /// single token is expected to be a curly-brace-enclosed block.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub fn parse(
        token: Option<&'a TokenResult<'a>>,
        ends_early: bool,
        none_source: Source<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<BlockExpr<'a>, ()> {
        todo!()
    }
}

impl<'a> ForExpr<'a> {
    /// Consumes a "for" loop expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "for", and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ForExpr<'a>, Option<usize>> {
        // For loops are fairly simple - the BNF is exactly:
        //   "for" Pattern "in" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs
        //
        // Our primary task here is just to glue together the other parsers.
        //
        // The first thing we're going to do is just to check that the input we were given *did*
        // start with the `for` keyword.

        let for_kwd = match tokens.first() {
            None | Some(Err(_)) => panic!("expected keyword `for`, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::For) => t,
                _ => panic!("expected keyword `for`, found token kind {:?}", t.kind),
            },
        };

        let mut consumed = 1;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let pat_ctx = PatternContext::For(for_kwd);
        let pat = Pattern::consume(
            &tokens[consumed..],
            pat_ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += pat.consumed();

        // After the pattern, we expect the keyword "in"
        expect!((
            TokenKind::Keyword(Kwd::In) => consumed += 1,
            @else ExpectedKind::ForLoopInKwd(&tokens[..consumed])
        ));

        // And then we expect an expression. This expression can't include curly braces (in certain
        // places) because they would be ambiguous with the following block.
        let iter = Expr::consume_no_delim(
            &tokens[consumed..],
            Some(NoCurlyContext::ForIter),
            true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += iter.consumed();

        // And this is followed by a block expression
        let body = BlockExpr::parse(
            tokens.get(consumed),
            ends_early,
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        // For loops may be optionally followed by an 'else' branch
        let else_branch =
            ElseBranch::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|cs| cs.map(|c| c + consumed))?
                .map(Box::new);
        consumed += else_branch.consumed();

        Ok(ForExpr {
            src: &tokens[..consumed],
            pat,
            iter,
            body,
            else_branch,
        })
    }
}

impl<'a> WhileExpr<'a> {
    /// Consumes a `while` loop expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "while", and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<WhileExpr<'a>, Option<usize>> {
        // More simple than `for` loops, while loops have the following BNF:
        //   "while" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs

        match tokens.first() {
            None | Some(Err(_)) => panic!("Expected keyword `while`, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::While) => (),
                _ => panic!("Expected keyword `while`, found token kind {:?}", t.kind),
            },
        }

        let mut consumed = 1;
        let condition = Expr::consume_no_delim(
            &tokens[..consumed],
            Some(NoCurlyContext::WhileCondition),
            true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += condition.consumed();

        let body = BlockExpr::parse(
            tokens.get(consumed),
            ends_early,
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        // While loops may be optionally followed by an 'else' branch:
        let else_branch =
            ElseBranch::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|cs| cs.map(|c| c + consumed))?
                .map(Box::new);
        consumed += else_branch.consumed();

        Ok(WhileExpr {
            src: &tokens[..consumed],
            condition: Box::new(condition),
            body,
            else_branch,
        })
    }
}

impl<'a> DoWhileExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<DoWhileExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> LoopExpr<'a> {
    /// Consumes a `loop` expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword "loop", and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<LoopExpr<'a>, Option<usize>> {
        // Loop expressions are very simple; the BNF is just:
        //   "loop" BlockExpr

        match tokens.first() {
            None | Some(Err(_)) => panic!("Expected keyword `loop`, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Loop) => (),
                _ => panic!("Expected keyword `loop`, found token kind {:?}", t.kind),
            },
        }

        // If we won't be able to parse a block expression, due to the token list ending early,
        // we'll just return an error - we don't want to pass it down to `BlockExpr::parse`
        if tokens.len() < 2 && ends_early {
            return Err(None);
        }

        BlockExpr::parse(
            tokens.get(1),
            ends_early,
            end_source!(containing_token),
            errors,
        )
        .map(|body| LoopExpr {
            src: &tokens[..2],
            body,
        })
        .map_err(|()| None)
    }
}

impl<'a> IfExpr<'a> {
    /// Consumes an "if" conditional expression
    ///
    /// This function assumes that the starting token is the keyword `if`, and will panic if this
    /// condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<IfExpr<'a>, Option<usize>> {
        // If conditions are fairly simple - they are defined with the following BNF:
        //   "if" Expr* BlockExpr [ "else" BigExpr ]
        // * excluding structs

        match tokens.first() {
            None | Some(Err(_)) => panic!("expected keyword `if`, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::If) => (),
                _ => panic!("expected keyword `if`, found token kind {:?}", t.kind),
            },
        }

        let mut consumed = 1;
        let condition = Expr::consume_no_delim(
            &tokens[consumed..],
            Some(NoCurlyContext::IfCondition),
            true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += condition.consumed();

        let body = BlockExpr::parse(
            tokens.get(consumed),
            ends_early,
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| Some(consumed))?;
        consumed += 1;

        let else_branch =
            ElseBranch::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|cs| cs.map(|c| c + consumed))?
                .map(Box::new);
        consumed += else_branch.consumed();

        Ok(IfExpr {
            src: &tokens[consumed..],
            condition: Box::new(condition),
            body,
            else_branch,
        })
    }
}

impl<'a> MatchExpr<'a> {
    /// Consumes a "match" expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword `match`, and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MatchExpr<'a>, Option<usize>> {
        // Match expressions are defined by the following BNF:
        //   "match" Expr* "{" { MatchArm } "}"
        // * excluding structs

        let match_kwd = match tokens.first() {
            None | Some(Err(_)) => panic!("expected keyword `match`, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Match) => t,
                _ => panic!("expected keyword `match`, found token kind {:?}", t.kind),
            },
        };

        let mut consumed = 1;
        let expr = Expr::consume_no_delim(
            &tokens[consumed..],
            Some(NoCurlyContext::MatchExpr),
            true,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(|cs| cs.map(|c| c + consumed))?;

        let (arms, poisoned) = match tokens.get(consumed) {
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::MatchBody(match_kwd),
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
            Some(Err(token_tree::Error::UnclosedDelim(Delim::Curlies, _))) => return Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::MatchBody(match_kwd),
                    found: Source::TokenResult(Err(*e)),
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
                    MatchArm::parse_all(match_kwd, t, inner, errors)
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::MatchBody(match_kwd),
                        found: Source::TokenResult(Ok(t)),
                    });

                    return Err(Some(consumed));
                }
            },
        };

        Ok(MatchExpr {
            src: &tokens[..consumed],
            expr: Box::new(expr),
            arms,
            poisoned,
        })
    }
}

impl<'a> MatchArm<'a> {
    /// A helper function for [`MatchExpr::consume`](struct.MatchExpr.html#method.consume)
    ///
    /// This function parses the entire contents of a curly-brace enclosed block as the body of a
    /// match expression, returning the match arms and whether that list is poisoned.
    fn parse_all(
        match_kwd: &'a Token<'a>,
        curly_src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> (Vec<MatchArm<'a>>, bool) {
        let mut consumed = 0;
        let mut poisoned = false;
        let mut arms = Vec::new();
        let ends_early = false;

        let pat_ctx = PatternContext::Match(match_kwd);
        while consumed < inner.len() {
            let arm_res = MatchArm::consume(
                &inner[consumed..],
                pat_ctx,
                ends_early,
                Some(curly_src),
                errors,
            );
            let arm_src;

            match arm_res {
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    arm_src = &inner[consumed..consumed + c];
                    consumed += c;
                    poisoned = true;
                }
                Ok(arm) => {
                    arm_src = &inner[consumed..consumed + arm.consumed()];
                    consumed += arm.consumed();
                    let requires_delim = arm.requires_delim();
                    arms.push(arm);
                    if !requires_delim {
                        continue;
                    }
                }
            }

            // After each match arm that requires it, we'll expect a comma to delimit the arms
            match inner.get(consumed) {
                // Running out of tokens is fine- we don't have any more arms to parse, so we'll do
                // a normal exit
                None => {
                    if ends_early {
                        poisoned = true;
                    }
                    break;
                }
                // If the arms have already been poisoned and we find a tokenizer error, we'll just
                // exit because we don't have enough information
                Some(Err(_)) if poisoned => break,
                // Otherwise, we were expecting a comma - we'll produce an error because we didn't
                // find one.
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::MatchArmDelim(arm_src),
                        found: Source::TokenResult(Err(*e)),
                    });

                    poisoned = true;
                    break;
                }
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::MatchArmDelim(arm_src),
                            found: Source::TokenResult(Ok(t)),
                        });

                        poisoned = true;
                        break;
                    }
                },
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
        tokens: TokenSlice<'a>,
        pat_ctx: PatternContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MatchArm<'a>, Option<usize>> {
        todo!()
    }

    /// A helper function to determine whether a match arm requires a trailing comma. Only
    /// `BigExpr` expressions are allowed to omit the trailing comma.
    fn requires_delim(&self) -> bool {
        self.eval.is_big_expr()
    }
}

impl<'a> ContinueExpr<'a> {
    /// Consumes a `continue` expression as a prefix of the given tokens
    ///
    /// This function assumes that the starting token is the keyword `continue`, and will panic if
    /// this condition is not met.
    ///
    /// Like other parsing functions, if an error occurs, this function may return `Err(Some)` to
    /// indicate the number of tokens consumed, or `Err(None)` if no more parsing should be done
    /// inside the current token tree.
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ContinueExpr<'a>, Option<usize>> {
        todo!()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Path                                                                                         //
//   * PathComponent                                                                              //
// * FnArg                                                                                        //
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
/// Path = Ident [ GenericArgs ] { "." Ident [ GenericArgs ] } .
/// ```
///
/// The helper type [`PathComponent`] is defined as well to manage the token sources for individual
/// elements, where its BNF is:
/// ```text
/// PathComponent = Ident [ GenericArgs ] .
/// ```
///
/// [`PathComponent`]: struct.PathComponent.html
#[derive(Debug, Clone)]
pub struct Path<'a> {
    pub(super) src: TokenSlice<'a>,
    pub components: Vec<PathComponent<'a>>,
}

/// A single component of a type
///
/// For more information, refer to the documentation of [`Path`](struct.Path.html).
#[derive(Debug, Clone)]
pub struct PathComponent<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub generic_args: Option<GenericArgs<'a>>,
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
#[derive(Debug, Clone)]
pub struct FnArg<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Option<Ident<'a>>,
    pub value: Expr<'a>,
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
/// BigExpr = IfExpr | MatchExpr | ForExpr | WhileExpr | LoopExpr | BlockExpr .
/// ```
#[derive(Debug, Clone)]
pub struct ElseBranch<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Expr<'a>,
}

impl<'a> Path<'a> {
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
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Path<'a>, Option<usize>> {
        // We always require a first element in the path
        let fst = PathComponent::consume(tokens, None, ends_early, containing_token, errors)
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
            src: &tokens[..consumed],
            components,
        })
    }
}

impl<'a> PathComponent<'a> {
    /// Consumes a single `PathComponent` as a prefix of the given tokens
    ///
    /// This exists solely as a helper function for [`Path::consume`].
    ///
    /// [`Path::consume`]: struct.Path.html#method.consume
    fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: Option<TokenSlice<'a>>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PathComponent<'a>, Option<usize>> {
        // Path components are composed of - at most - two pieces: an identifier and optional
        // generic arguments.
        let ctx = PathComponentContext { prev_tokens };

        let name = Ident::parse(
            tokens.first(),
            IdentContext::PathComponent(ctx),
            end_source!(containing_token),
            errors,
        )
        .map_err(|_| None)?;

        let mut consumed = name.consumed();

        let generic_args =
            GenericArgs::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|_| None)?;

        consumed += generic_args.consumed();

        Ok(PathComponent {
            src: &tokens[..consumed],
            name,
            generic_args,
        })
    }
}

impl<'a> ElseBranch<'a> {
    fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<ElseBranch<'a>>, Option<usize>> {
        todo!()
    }
}
