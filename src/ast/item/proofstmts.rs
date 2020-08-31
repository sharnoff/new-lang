use super::*;

// NOTE: Proof statements are currently unimplemented, pending revision.

/// A collection of proof statements, given before an item
///
/// This is provided so that we can track groups of proof statements together, keeping certain
/// attributes (like whether the values have been poisoned) as part of this struct instead of
/// elsewhere.
///
/// The single-token source for proof statments is always a [`ProofLines`] token. For more
/// information on the structure of proof statements, see [`ProofStmt`].
///
/// [`ProofLines`]: ../../token_tree/enum.TokenKind.html
/// [`ProofStmt`]: struct.ProofStmt.html
#[derive(Debug, Clone)]
pub struct ProofStmts<'a> {
    pub(in crate::ast) src: &'a Token<'a>,
    // TODO: note - see above.
    // pub stmts: Vec<ProofStmt<'a>>,
    pub poisoned: bool,
}
/*

/// A single proof statement as part of a collection
///
/// There are multiple types of statements possible, which are each represented by the variants of
/// this type.
///
/// The BNF definitions for all of the related types have been collected here for TODO
/// ```text
/// ProofStmts = { ProofStmt ";" }
/// ProofStmt  = Invariant
///            | Forall
///            | Existential
///            | Implies
///            | DoubleImplies
///            | Expr .
/// ProofBlock = ":" ProofStmt
///            | "{" ProofStmts "}" .
/// Invariant     = "invariant" [ StringLiteral ] ProofBlock .
/// Forall        = "forall" Pattern [ "in" Expr ] ProofBlock .
/// Existential   = "exists" Pattern [ "in" Expr ] "where" Expr .
/// Implies       = Expr "=>" Expr .
/// DoubleImplies = Expr "<=>" Expr .
/// ```
///
/// Proof statements essentially form their own DSL inside of the main language, and so this is why
/// we see so much complexity here. One crucial thing about this is that implication operators
/// (`=>` and `<=>`) are not allowed normally inside expressions; this allows certain
/// simplifications in the proof system that are discussed later.
///
/// The final piece of syntax to note here is that the trailing semicolon listed for [`ProofStmts`]
/// may be omitted in certain circumstances, much like the trailing semicolons in
/// [block expressions].
///
/// [`ProofStmts`]: struct.ProofStmts.html
/// [block expression]: ../../expr/struct.BlockExpr.html
#[derive(Debug, Clone)]
pub enum ProofStmt<'a> {
    Invariant(Invariant<'a>),
    Forall(Forall<'a>),
    Existential(Existential<'a>),
    Implies(Implies<'a>),
    DoubleImplies(DoubleImplies<'a>),
    Expr(Expr<'a>),
}

/// An "invariant" proof statment
///
/// Invariants specify a certain property that must be true at all times. They are defined with the
/// following syntax:
/// ```text
/// Invariant = "invariant" [ StringLiteral ] ProofBlock .
/// ```
/// Invariants may additionally be named.
#[derive(Debug, Clone)]
pub struct Invariant<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub name: Option<StringLiteral<'a>>,
    pub block: ProofBlock<'a>,
}

/// A universal quantifier proof statement
///
/// "forall" statements specify that a certain proof statement (or list of proof statments) must
/// hold for all elements in a given iterator. These are defined by the following BNF:
/// ```text
/// Forall = "forall" Pattern "in" Expr ProofBlock .
/// ```
#[derive(Debug, Clone)]
pub struct Forall<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub pat: Pattern<'a>,
    pub iter: Option<Expr<'a>>,
}

/// An existential qualifier proof statement
///
/// Existential statements use the `exists` keywod to define that
#[derive(Debug, Clone)]
pub struct Existential<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
}

#[derive(Debug, Clone)]
pub struct Implies<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
}

#[derive(Debug, Clone)]
pub struct DoubleImplies<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
}

#[derive(Debug, Clone)]
pub enum ProofBlock<'a> {
    Stmt(Box<ProofStmt<'a>>),
    Block(ProofStmts<'a>),
}
*/

impl<'a> ProofStmts<'a> {
    /// Parses a single token tree as a list of proof statements
    ///
    /// This function always returns a set of proof statements, marking them internally as poisoned
    /// if any errors occured.
    ///
    /// NOTE: At time of writing, this function will always add a `ProofStmtsUnimplemented` error
    /// to the given list, because syntax for proof statements has not yet been decided.
    pub(super) fn parse(
        src: &'a Token<'a>,
        _inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> ProofStmts<'a> {
        errors.push(Error::ProofStmtsUnimplemented { proof_lines: src });

        ProofStmts {
            src,
            poisoned: true,
        }
    }
}
