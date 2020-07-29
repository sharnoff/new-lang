//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
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
    /// Expressions that occur as part of function argumentsf
    FnArgs,
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
#[derive(Debug)]
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
#[derive(Debug)]
pub struct ConditionalSet<'a, T> {
    /// The expression that must *not* be generic for the tokens to be interpreted as this set
    determiner: Expr<'a>,
    /// The set of expressions that are must be generic for the tokens to be interpreted as this
    /// set
    implied: Vec<Expr<'a>>,
    set: Vec<T>,
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
pub struct MatchExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub expr: Box<Expr<'a>>,
    pub arms: Vec<MatchArm<'a>>,
    pub poisoned: bool,
}

/// A single `match` arm; a helper type for [`MatchExpr`](#struct.MatchExpr.html)
#[derive(Debug)]
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
#[derive(Debug)]
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
    }
}

impl<'a> Expr<'a> {
    /// Consumes an expression as a prefix of the tokens - assuming that no delimeter occurs within
    /// the binding power.
    ///
    /// This function has a very particular use, made possible by a single, strict assumption that
    /// it makes. For a given set of tokens here, we assume that an expression with the given
    /// minimum binding power occurs before any delimeter, of any kind. If the outer delimeter *is*
    /// a comma, then the binding power must be strictly greater than `Shr` and `Gt` - this is not
    /// checked here.
    ///
    /// Please additionally note that `no_delim` additionally applies to semicolon-delimited
    /// expressions - because ambiguity only occurs with comma-separated lists of expressions, we
    /// can treat all other cases with this.
    pub fn consume_no_delim(
        tokens: TokenSlice<'a>,
        min_bp: Option<BindingPower>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Expr<'a>, Option<usize>> {
        assert!(min_bp > Some(BindingPower::Shr) && min_bp > Some(BindingPower::Gt));

        // Here, we're doing regular Pratt parsing, because the assumptions made by this function
        // allow us to get rid of any ambiguity that we'd otherwise have.
        //
        // For an intro to Pratt parsing, see this article:
        //     https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

        let mut lhs = Some(Expr::consume_lhs_no_delim(
            tokens,
            allow_structs,
            ends_early,
            containing_token,
            errors,
        )?);
        let mut consumed = lhs.consumed();

        loop {
            let postfix_res = PostfixOp::consume_if_bp_ge_no_delim(
                &tokens[consumed..],
                min_bp,
                allow_structs,
                ends_early,
                containing_token,
                errors,
            );
            match postfix_res {
                Ok(Err(is_postfix_op)) => match is_postfix_op {
                    true => break,
                    false => (),
                },
                Ok(Ok((op, op_src))) => {
                    consumed += op_src.len();

                    lhs = Some(Expr::PostfixOp(PostfixOpExpr {
                        src: &tokens[..consumed],
                        expr: Box::new(lhs.take().unwrap()),
                        op,
                        op_src,
                    }));

                    continue;
                }
                Err(None) => return Err(None),
                Err(Some(c)) => return Err(Some(consumed + c)),
            }

            if let Some((left_bp, right_bp, op_src, op)) = BinOp::bp(&tokens[consumed..]) {
                if Some(left_bp) < min_bp {
                    break;
                }

                let rhs_start_idx = consumed + op_src.len();
                let rhs_res = Expr::consume_no_delim(
                    &tokens[rhs_start_idx..],
                    Some(right_bp),
                    allow_structs,
                    ends_early,
                    containing_token,
                    errors,
                );

                match rhs_res {
                    Ok(rhs) => {
                        consumed = rhs_start_idx + rhs.consumed();
                        lhs = Some(Expr::BinOp(Box::new(BinOpExpr {
                            src: &tokens[..consumed],
                            lhs: lhs.take().unwrap(),
                            op_src,
                            op,
                            rhs,
                        })));
                    }
                    Err(Some(c)) => return Err(Some(c + rhs_start_idx)),
                    Err(None) => return Err(None),
                }

                continue;
            }

            break;
        }

        Ok(lhs.take().unwrap())
    }

    /// A helper function for [`consume_no_delim`](#method.consume_no_delim), documented internally
    fn consume_lhs_no_delim(
        tokens: TokenSlice<'a>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Expr<'a>, Option<usize>> {
        // When looking at the left-hand side of an expression, we're completely ignoring binary
        // and postfix operators.
        //
        // Where normally there would be ambiguity from geneics arguments, we can ignore this here
        // because of the guarantees provided by `consume_no_delim`

        // First, we'll define a helper macro for some of the elements of this function that we
        // pass off elsewhere. Not all calls will fit the format of this macro, but we get enough
        // mileage to make this useful.
        macro_rules! consume {
            ($ty_name:ident, $variant:ident) => {{
                $ty_name::consume(tokens, ends_early, containing_token, errors).map(Expr::$variant)
            }};
            ($ty_name:ident, box $variant:ident) => {{
                $ty_name::consume(tokens, ends_early, containing_token, errors)
                    .map(|ex| Expr::$variant(Box::new(ex)))
            }};
        }

        // We'll use the first token to determine how to consume the rest of the expression.
        match tokens.first() {
            // If there is no first token, this is typically an error. If this token tree ended
            // early, however, that error has already been reported - we shouldn't generate a
            // second error from it.
            None if ends_early => Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ExprLhs,
                    found: end_source!(containing_token),
                });

                Err(None)
            }

            // If we find that the first token is a tokenizer error, it *might* not actually be
            // incorrect: an unclosed delimeter error is not actually an error here, because any
            // token tree *might* be a valid expression.
            //
            // So: We'll only produce a second error here if the tokenizer error *also* wouldn't
            // have been a valid expression.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ExprLhs,
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }

            // And if the token is successful, we'll determine what to match on, based on this.
            Some(Ok(fst_token)) => match &fst_token.kind {
                // The first group is literals - these are fairly simple
                TokenKind::Literal(_, _) => consume!(Literal, Literal),

                // Identifiers are always treated as a path segment. They may contain trailing
                // generics arguments, so we use a dedicated function to handle this.
                TokenKind::Ident(_) => Expr::consume_path_component_no_delim(
                    tokens,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Expr::Named),

                // Token trees (as briefly mentioned above) all have expressions they can be parsed
                // as.
                TokenKind::Tree { delim, inner, .. } => {
                    use Delim::{Curlies, Parens, Squares};

                    // All parsing of token trees returns Result<_, ()>, so we'll map that to mark
                    // the amount we consumed.
                    let res = match delim {
                        // Curly braces are ambiguous, so we have a separate function to handle that
                        Curlies => Expr::parse_curly_block(fst_token, inner, errors, tokens),

                        // Square brackets corresond to array literals and parentheses to tuples, so we
                        // parse both as such.
                        Squares => ArrayExpr::parse(fst_token, inner, errors).map(Expr::Array),
                        Parens => TupleExpr::parse(fst_token, inner, errors).map(Expr::Tuple),
                    };

                    res.map_err(|()| Some(1))
                }

                // With those aside, we have prefix operators as our penultimate group. As per
                // 'bnf.md', the following tokens are allowed as prefix operators:
                //   PreifxOp = "!" | "-" | "&" [ "mut" ] | "*" | LetPrefix | "break" | "return"
                //    --> LetPrefix = "let" Pattern [ ":" Type ] "="
                // We'll use dedicated function provided by `PrefixOpExpr` for this.
                TokenKind::Punctuation(Punc::Not)
                | TokenKind::Punctuation(Punc::Minus)
                | TokenKind::Punctuation(Punc::And)
                | TokenKind::Punctuation(Punc::Star)
                | TokenKind::Keyword(Kwd::Let)
                | TokenKind::Keyword(Kwd::Break)
                | TokenKind::Keyword(Kwd::Return) => PrefixOpExpr::consume_no_delim(
                    tokens,
                    allow_structs,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(|pre| Expr::PrefixOp(Box::new(pre))),

                // And finally, we have all of the various keywords that may start an expression:
                TokenKind::Keyword(Kwd::For) => consume!(ForExpr, box For),
                TokenKind::Keyword(Kwd::While) => consume!(WhileExpr, While),
                TokenKind::Keyword(Kwd::Do) => consume!(DoWhileExpr, DoWhile),
                TokenKind::Keyword(Kwd::Loop) => consume!(LoopExpr, Loop),
                TokenKind::Keyword(Kwd::If) => consume!(IfExpr, If),
                TokenKind::Keyword(Kwd::Match) => consume!(MatchExpr, Match),
                TokenKind::Keyword(Kwd::Continue) => consume!(ContinueExpr, Continue),

                // Otherwise, if we couldn't find any of these, we had an error
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::ExprLhs,
                        found: Source::TokenResult(Ok(fst_token)),
                    });

                    Err(None)
                }
            },
        }
    }

    /// A helper function for [`consume_lhs_no_delim`](#method.consume_lhs_no_delim)
    ///
    /// This consumes a single path component as part of an expression, given the restrictions
    /// provided by [`consume_no_delim`]. We're able to walk though a set of tokens that *might*
    /// constitute generics arguments, where encountering a comma indicates that an opening angle
    /// bracket ("<") is certainly part of generics arguments.
    ///
    /// This function assumes (panicking otherwise) that the first token given is an identifier.
    ///
    /// [`consume_no_delim`]: #method.consume_no_delim
    fn consume_path_component_no_delim(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PathComponent<'a>, Option<usize>> {
        // This function is complex due to the problem it tries to solve: When we see the following
        // tokens
        //   [ Ident, "<", .. ]
        // at the start of the input, we don't immediately know whether the path component ends with
        // the identifier (without generics arguments) or whether the angle bracket gives the start
        // of the generics arguments.
        //
        // Elsewhere (outside the `no_delim` variants of these parsing functions), this hard
        // problem is not entirely dealt with - ambiguity is still left over, and we end up
        // recursively parsing using different assumptions.
        //
        // Thankfully, the assumptions given with `Expr::consume_no_delim` allow us to
        // unambiguously parse path components. This is because of two guarantees:
        //   1. If the outer delimeter is a comma, the expression we're parsing cannot include
        //      comparison operators (i.e. the tokens "<" .. "," must be due to generics)
        //   2. Otherwise, the outer delimeter is not a comma - meaning that any comma we find here
        //      must be generics.
        //
        // There's a few other things we'll note as we get into all of the cases here.

        // To start off with, we'll verify that we were given an identifier to start with.
        let name = {
            let src = tokens[0].as_ref().unwrap();
            let name = match &src.kind {
                TokenKind::Ident(name) => name,
                _ => panic!("expected identifier token as first token, found {:?}", src),
            };

            Ident { src, name }
        };

        // We'll now define a couple helper macros so that we can simply return once we know
        // whether there's generics arguments.
        macro_rules! return_name {
            () => {{
                return Ok(PathComponent {
                    src: &tokens[..1],
                    name,
                    generic_args: None,
                });
            }};
        }

        macro_rules! return_path_component {
            () => {{
                return PathComponent::consume(
                    tokens,
                    // TODO: Give PathComponents a more detailed context so that we know this is
                    // within an expression, not a full `Path`.
                    None,
                    ends_early,
                    containing_token,
                    errors,
                );
            }};
        }

        // Now, if the second token *isn't* "<", we know there aren't any generics arguments here,
        // so we can simply return.
        match tokens.get(1) {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Lt) => (),
                _ => return_name!(),
            },
            _ => return_name!(),
        }

        let mut consumed = 2;

        // At this point, we've consumed `Ident "<"`, and we're expecting either a generics
        // argument or an expression. Generics arguments are any of:
        //   GenericArg = [ Ident ":" ] Type
        //              | [ Ident ":" ] Expr
        //              | "ref" Expr
        // So, we can match through the first couple tokens to determine how to interpret the
        // entire input.

        match tokens.get(consumed) {
            // Unless there was a previous tokenizer error, finding the end of the input after an
            // opening angle-bracket is always an error. We would have expected a generics argument
            // or an expression here.
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericArgOrExpr,
                    found: end_source!(containing_token),
                });

                Err(None)
            }

            // Other tokenizer errors might also be an error here - but only some of them. This
            // isn't too difficult, as any token tree can follow as part of an expression - so we
            // can generate a second error for anything aside from an `UnclosedDelim` error.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericArgOrExpr,
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }

            // With no errors here, we continue on with what the first token has given us.
            Some(Ok(t)) => {
                // If we find the "ref" keyword, this must be a generics argument
                if let TokenKind::Keyword(Kwd::Ref) = &t.kind {
                    return_path_component!();
                }

                // If we find an identifier, we'll check whether the next token is a colon - if so,
                // we'd have something like:
                //   `foo<T: `
                // which must be a generics argument.
                match tokens.get(consumed + 1) {
                    Some(Ok(next)) => match &next.kind {
                        TokenKind::Punctuation(Punc::Colon) => return_path_component!(),
                        _ => (),
                    },
                    _ => (),
                }

                // Otherwise, we'll make use of the existing functions for disambiguating between
                // types and expressions.
                let res = TypeOrExpr::consume(
                    &tokens[consumed..],
                    &tokens[1..2],
                    ends_early,
                    containing_token,
                    errors,
                );

                match res {
                    Err(None) => return Err(None),
                    Err(Some(c)) => return Err(Some(consumed + c)),
                    Ok(TypeOrExpr::Type(_)) => return_path_component!(),
                    Ok(TypeOrExpr::Expr(_)) => return_name!(),
                    Ok(TypeOrExpr::Ambiguous { consumed: c, .. }) => consumed += c,
                }

                // And if there's still ambiguity, we look at the next token. At this point, we've
                // consumed a single type or expression. The next token is all we need to determine
                // what to interpret the input as.
                match tokens.get(consumed) {
                    // If we get an error here, we'll return to let this be handled as an
                    // expression, which it will be in most cases.
                    None | Some(Err(_)) => return_name!(),

                    Some(Ok(t)) => match &t.kind {
                        // As we mentioned above, if we know that any input that has
                        //   Ident "<" .. ","
                        // must be from generics arguments
                        TokenKind::Punctuation(Punc::Comma) => return_path_component!(),

                        // Similarly, if we have an input of the form:
                        //   Ident "<" ( Expr | Type ) ">"
                        // we know it must also be a path component.
                        TokenKind::Punctuation(Punc::Gt) => return_path_component!(),

                        // For anything else, we'll treat the original angle-bracket as an
                        // expression because - even though it might be erroneous - it definitely
                        // isn't generics arguments.
                        _ => return_name!(),
                    },
                }
            }
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

    /// Consumes a single (possibly ambiguous) expression within a given delimeter context
    fn consume_delimited<T: From<Delimited<'a>>>(
        tokens: TokenSlice<'a>,
        delim: ExprDelim,
        no_elem_err: ExpectedKind<'a>,
    ) -> Result<Ambiguous<'a, T>, Option<usize>> {
        todo!()
    }

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
                    let res = Expr::consume_delimited(&inner[consumed..], delim, no_elem_err);

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
}

impl ExprDelim {
    /// A convenience method to return whether the expression delimeter context requires the first
    /// token to be an identifier
    ///
    /// This returns true precisely if the `ExprDelim` is the `StructFields` variant.
    fn requires_name(&self) -> bool {
        match self {
            ExprDelim::StructFields => true,
            ExprDelim::Comma | ExprDelim::FnArgs => false,
        }
    }
}

impl<'a> PrefixOpExpr<'a> {
    /// Consumes a prefix-operator expression as a prefix of the given tokens
    ///
    /// This function expects the first token to be a prefix operator, and will panic if it is not.
    ///
    /// This makes a recursive call to [`Expr::consume_no_delim`] in order to
    fn consume_no_delim(
        tokens: TokenSlice<'a>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PrefixOpExpr<'a>, Option<usize>> {
        // This function is farily simple - we start off by generating the prefix operator, and
        // then parse the rest of the expression.

        // First off, we'll get the prefix operator
        let (op, op_src, binding_power) = match tokens.first() {
            None | Some(Err(_)) => panic!("expected a prefix operator, found {:?}", tokens.first()),
            Some(Ok(t)) => {
                macro_rules! op_with_bp {
                    ($kind:ident) => {{
                        (PrefixOp::$kind, &tokens[..1], BindingPower::$kind)
                    }};
                }

                match &t.kind {
                    // The first bunch are simple, and given directly by 'bnf.md'
                    TokenKind::Punctuation(Punc::Not) => op_with_bp!(Not),
                    TokenKind::Punctuation(Punc::Minus) => op_with_bp!(Minus),
                    TokenKind::Punctuation(Punc::Star) => op_with_bp!(Deref),
                    TokenKind::Keyword(Kwd::Break) => op_with_bp!(Break),
                    TokenKind::Keyword(Kwd::Return) => op_with_bp!(Return),
                    // The final one is from the reference operator. It's allowed to be followed by
                    // "mut" to take a mutable reference, so we'll
                    TokenKind::Punctuation(Punc::And) => {
                        let (is_mut, len) = match tokens.get(1) {
                            Some(Ok(t)) => match &t.kind {
                                TokenKind::Keyword(Kwd::Mut) => (true, 2),
                                _ => (false, 1),
                            },
                            _ => (false, 1),
                        };

                        (PrefixOp::Ref { is_mut }, &tokens[..len], BindingPower::Ref)
                    }
                    TokenKind::Keyword(Kwd::Let) => {
                        let res =
                            PrefixOpExpr::consume_let(tokens, ends_early, containing_token, errors);
                        match res {
                            Err(_) => return Err(None),
                            Ok((op, src)) => (op, src, BindingPower::Let),
                        }
                    }
                    _ => panic!("Expected prefix operator, found {:?}", t),
                }
            }
        };

        let rhs_res = Expr::consume_no_delim(
            &tokens[op_src.len()..],
            Some(binding_power),
            allow_structs,
            ends_early,
            containing_token,
            errors,
        );

        match rhs_res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(c + op_src.len())),
            Ok(rhs) => {
                let src = &tokens[..op_src.len() + rhs.consumed()];
                Ok(PrefixOpExpr {
                    src,
                    op_src,
                    op,
                    expr: Box::new(rhs),
                })
            }
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
    /// Returns the left and right binding power of a leading binary operator, alongside its source
    ///
    /// The first two elements of the returned tuple are the left and right binding power,
    /// respectively. The third and fourth elements give the binary operator found, alongside its
    /// source.
    fn bp<'a>(
        tokens: TokenSlice<'a>,
    ) -> Option<(BindingPower, BindingPower, TokenSlice<'a>, BinOp)> {
        macro_rules! op {
            // Most operators will only occupy a single token
            ($kind:ident) => {{
                op!($kind, 1)
            }};

            // But some use more, so we provide the second variant here to allow that
            ($kind:ident, $len:expr) => {{
                // We say that the required binding power on the right is one greater than the
                // left, so that the operators are left-associative. Every binary operator we have
                // is left-associative, so we can simply make this a general rule.
                let left_bp = BindingPower::$kind;
                let right_bp = left_bp.inc().unwrap();
                Some((left_bp, right_bp, &tokens[..$len], BinOp::$kind))
            }};
        }

        macro_rules! punc {
            ($($kind:ident),+) => {
                [$(&TokenKind::Punctuation(Punc::$kind),)+ ..]
            };
        }

        let token = tokens.first()?.as_ref().ok()?;

        let mut first_two_kinds = Vec::with_capacity(2);
        first_two_kinds.push(&token.kind);
        match tokens.get(2) {
            Some(Ok(t)) if token.trailing_whitespace.is_empty() => first_two_kinds.push(&t.kind),
            _ => (),
        }

        match &first_two_kinds as &[_] {
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
            punc!(Lt, Lt) => op!(Shl, 2),
            punc!(Gt, Gt) => op!(Shr, 2),
            punc!(Lt) => op!(Lt),
            punc!(Gt) => op!(Gt),
            punc!(Le) => op!(Le),
            punc!(Ge) => op!(Ge),
            punc!(EqEq) => op!(Eq),
            punc!(NotEq) => op!(Ne),
            _ => None,
        }
    }
}

impl<'a> PostfixOp<'a> {
    /// Attempts to consume a postfix operator of the given tokens, so long as it meets the
    /// required minimum binding power.
    ///
    /// Like most parsing functions, this uses `Err(Some(_))` to indicate the number of tokens
    /// consumed on failure. In order to express whether the tokens *do* start with a postfix
    /// operator, this function returns `Ok(Err(false))` if the tokens don't start with a postfix
    /// operator, and `Ok(Err(true))` if they do, but the required binding power is too high.
    ///
    /// In the event that the first token is a tokenizer error, this function will either return
    /// `Err(None)` or `Ok(Err(false))`.
    ///
    /// This function additionally makes all of the assumptions given by
    /// [`Expr::consume_no_delim`], and can only be used in those contexts.
    ///
    /// [`Expr::consume_no_delim`]: enum.Expr.html#method.consume_no_delim
    fn consume_if_bp_ge_no_delim(
        tokens: TokenSlice<'a>,
        min_bp: Option<BindingPower>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Result<(PostfixOp<'a>, TokenSlice<'a>), bool>, Option<usize>> {
        use Delim::{Curlies, Parens, Squares};

        match tokens.first() {
            // If we're given an empty list of tokens, it's probably fine - we aren't required to
            // parse anything here
            None => Ok(Err(false)),

            // Most tokenizer errors *will* actually be errors in the outer scope. We do, however,
            // allow any token tree as a postfix operator (through array indexing, function calls,
            // and named struct instantiation) - so unclosed delimeters are not additionally an
            // error here. We'll produce an appropriate error because of it.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => Err(None),
            // Otherwise, we'll let the outer scope handle the tokenizer error (and likely produce
            // an additional error message)
            Some(Err(_)) => Ok(Err(false)),

            // Now we'll go through all of the different postfix operators we can parse as,
            // returning `Ok(Err(true))` if the required binding power is too high.
            Some(Ok(t)) => match &t.kind {
                // Indexing
                TokenKind::Tree { delim: Squares, .. } if Some(BindingPower::Index) < min_bp => {
                    Ok(Err(true))
                }
                TokenKind::Tree {
                    delim: Squares,
                    inner,
                    ..
                } => PostfixOp::parse_index(t, inner, errors)
                    .map(|idx| Ok((idx, &tokens[..1])))
                    .map_err(|()| Some(1)),

                // There's two postfix operators that start with dots, so we'll make a brief
                // assertion that the binding powers of the two are equal.
                TokenKind::Punctuation(Punc::Dot) => {
                    assert!(
                        BindingPower::Access == BindingPower::TupleIndex,
                        "These binding powers should be equal, else the `PostfixOp` parser gets much more complicated"
                    );

                    if Some(BindingPower::Access) < min_bp {
                        return Ok(Err(true));
                    }

                    PostfixOp::consume_dot_no_delim(tokens, ends_early, containing_token, errors)
                        .map(Ok)
                }

                // Function calls
                TokenKind::Tree { delim: Parens, .. } if Some(BindingPower::FnCall) < min_bp => {
                    Ok(Err(true))
                }
                TokenKind::Tree {
                    delim: Parens,
                    inner,
                    ..
                } => PostfixOp::parse_fn_args(t, inner, errors)
                    .map(|args| Ok((args, &tokens[..1])))
                    .map_err(|()| Some(1)),

                // Named structs
                TokenKind::Tree { delim: Curlies, .. }
                    if Some(BindingPower::NamedStruct) < min_bp =>
                {
                    Ok(Err(true))
                }
                TokenKind::Tree {
                    delim: Curlies,
                    inner,
                    ..
                } => StructExpr::parse(t, inner, errors)
                    .map(|st| Ok((PostfixOp::NamedStruct(st), &tokens[..1])))
                    .map_err(|()| Some(1)),

                // Type binding - "~" Type
                TokenKind::Punctuation(Punc::Tilde) if Some(BindingPower::TypeBinding) < min_bp => {
                    Ok(Err(true))
                }
                TokenKind::Punctuation(Punc::Tilde) => PostfixOp::consume_type_binding_no_delim(
                    tokens,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Ok),

                // Pattern equivalence - "is" Pattern
                TokenKind::Keyword(Kwd::Is) if Some(BindingPower::IsPattern) < min_bp => {
                    Ok(Err(true))
                }
                TokenKind::Keyword(Kwd::Is) => {
                    PostfixOp::consume_is_pattern(tokens, ends_early, containing_token, errors)
                        .map(Ok)
                }

                // The "try" operator
                TokenKind::Punctuation(Punc::Question) if Some(BindingPower::Try) < min_bp => {
                    Ok(Err(true))
                }
                // This one is simple, so we can do it directly
                TokenKind::Punctuation(Punc::Question) => Ok(Ok((PostfixOp::Try, &tokens[..1]))),

                // Anything else can't be interpreted as a postfix operator - we'll just return.
                _ => Ok(Err(false)),
            },
        }
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

    fn consume_dot_no_delim(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(PostfixOp<'a>, TokenSlice<'a>), Option<usize>> {
        todo!()
    }

    fn parse_fn_args(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PostfixOp<'a>, ()> {
        todo!()
    }

    fn consume_type_binding_no_delim(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<(PostfixOp<'a>, TokenSlice<'a>), Option<usize>> {
        todo!()
    }

    fn consume_is_pattern(
        tokens: TokenSlice<'a>,
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
            None,
            Some(NoCurlyContext::ForIter),
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
            None,
            Some(NoCurlyContext::WhileCondition),
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
            None,
            Some(NoCurlyContext::IfCondition),
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
            None,
            Some(NoCurlyContext::MatchExpr),
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
#[derive(Debug)]
pub struct Path<'a> {
    pub(super) src: TokenSlice<'a>,
    pub components: Vec<PathComponent<'a>>,
}

/// A single component of a type
///
/// For more information, refer to the documentation of [`Path`](struct.Path.html).
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
