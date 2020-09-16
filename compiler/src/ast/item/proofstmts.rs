use super::*;
use crate::files::{FileInfo, Span};

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
#[derive(Debug, Clone, Consumed)]
pub struct ProofStmts {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    // TODO: note - see above.
    // pub stmts: Vec<ProofStmt>,
    #[consumed(@ignore)]
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
pub enum ProofStmt {
    Invariant(Invariant),
    Forall(Forall),
    Existential(Existential),
    Implies(Implies),
    DoubleImplies(DoubleImplies),
    Expr(Expr),
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
pub struct Invariant {
    pub(in crate::ast) src: TokenSlice,
    pub name: Option<StringLiteral>,
    pub block: ProofBlock,
}

/// A universal quantifier proof statement
///
/// "forall" statements specify that a certain proof statement (or list of proof statments) must
/// hold for all elements in a given iterator. These are defined by the following BNF:
/// ```text
/// Forall = "forall" Pattern "in" Expr ProofBlock .
/// ```
#[derive(Debug, Clone)]
pub struct Forall {
    pub(in crate::ast) src: TokenSlice,
    pub pat: Pattern,
    pub iter: Option<Expr>,
}

/// An existential qualifier proof statement
///
/// Existential statements use the `exists` keywod to define that
#[derive(Debug, Clone)]
pub struct Existential {
    pub(in crate::ast) src: TokenSlice,
}

#[derive(Debug, Clone)]
pub struct Implies {
    pub(in crate::ast) src: TokenSlice,
}

#[derive(Debug, Clone)]
pub struct DoubleImplies {
    pub(in crate::ast) src: TokenSlice,
}

#[derive(Debug, Clone)]
pub enum ProofBlock {
    Stmt(Box<ProofStmt>),
    Block(ProofStmts),
}
*/

impl ProofStmts {
    /// Parses a single token tree as a list of proof statements
    ///
    /// This function always returns a set of proof statements, marking them internally as poisoned
    /// if any errors occured.
    ///
    /// NOTE: At time of writing, this function will always add a `ProofStmtsUnimplemented` error
    /// to the given list, because syntax for proof statements has not yet been decided.
    pub(super) fn parse(
        file: &FileInfo,
        src: &Token,
        _inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> ProofStmts {
        errors.push(Error::ProofStmtsUnimplemented { proof_lines: src.span(file) });

        ProofStmts {
            src: src.span(file),
            poisoned: true,
        }
    }
}
