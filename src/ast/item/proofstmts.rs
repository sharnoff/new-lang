use super::*;

/// A collection of proof statements, given before an item
///
/// This is provided so that we can track groups of proof statements together, keeping certain
/// attributes (like whether the values have been poisoned) as part of this struct instead of
/// elsewhere.
///
/// For more information on the structure of proof statements, see [`ProofStmt`].
///
/// [`ProofStmt`]: struct.ProofStmt.html
#[derive(Debug, Clone)]
pub struct ProofStmts<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub stmts: Vec<ProofStmt<'a>>,
    pub poisoned: bool,
}

/// A single proof statment - i.e. a single line starting with `#`
///
/// There are multiple types of the statments possibe; these are given by the `kind` field.
///
/// The BNF for proof statements is:
/// ```text
/// ProofStmts = { "#" ProofStmt "\n" } .
/// ProofStmt = Expr ( "=>" | "<=>" ) Expr
///           | Expr
///           | "invariant" [ StringLiteral ] ":"
///           | "forall" Pattern [ "in" Expr ] ":"
///           | "exists" Pattern [ "in" Expr ] where ":"
/// ```
/// Please note that these are likely to change - the precise syntax here is far from final.
///
/// The first `ProofStmt` variant indicates single- or double-implication between certain
/// conditions, given by expressions. The second simply gives a boolean statement that is always
/// true (or always required). The remaining three should hopefully be relatively clear without
/// further detail.
///
/// These types of statements are enumerated in the variants of [`ProofStmtKind`].
///
/// ## Structure
///
/// Broadly speaking, the nesting of proof statements is given by their indentation level; the BNF
/// here accurately describes single lines, but not the tree structure created between them.
///
/// For example, one might write the following:
/// ```text
/// # invariant "foo":
/// #   x > 4
/// # forall y in 0..x:
/// #   exists z where:
/// #       bar(z) = 0
/// ```
/// in which the statement `x > 4` is part of the invariant, and `bar(z) = 0` is part of
/// `exists z where:`, inside `forall y in 0..x`.
///
/// [`ProofStmtKind`]: enum.ProofStmtKind.html
#[derive(Debug, Clone)]
pub struct ProofStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub kind: ProofStmtKind<'a>,
}

/// The different types of proof statements available
///
/// For information on proof statments, refer to the documentation for [`ProofStmt`].
///
/// [`ProofStmt`]: struct.ProofStmt.html
#[derive(Debug, Clone)]
pub enum ProofStmtKind<'a> {
    /// Single implication: `Expr "=>" Expr`
    Implies(Expr<'a>, Expr<'a>),
    /// Double implication: `Expr "<=>" Expr`
    DoubleImplies(Expr<'a>, Expr<'a>),
    /// A single value that is given to be true
    Predicate(Expr<'a>),
    Invariant {
        name: Option<StringLiteral<'a>>,
        stmts: Vec<ProofStmt<'a>>,
    },
    Forall {
        pattern: Pattern<'a>,
        iter: Option<Expr<'a>>,
        stmts: Vec<ProofStmt<'a>>,
    },
    Exists {
        pattern: Pattern<'a>,
        iter: Option<Expr<'a>>,
        stmts: Vec<ProofStmt<'a>>,
    },
}

impl<'a> ProofStmts<'a> {
    /// Consumes multiple `ProofStmt`s as a prefix of the tokens given
    pub(super) fn try_consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<ProofStmts<'a>>, Option<usize>> {
        todo!()
    }
}
