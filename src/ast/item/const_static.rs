use super::*;

/// A `const` statment
///
/// Const statments may appear as an item in any scope - either as an associated `impl` or trait
/// item - or simply as a module-level constant. Only some forms might be valid in each, however.
///
/// The BNF can be defined by either of these equivalent definitions:
/// ```text
/// ConstStmt = [ Vis ] "const" Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ] ";" .
/// ```
/// The first definition is more accurate to how a `ConstStmt` is represented, whereas the second
/// gives a better idea as to how it is actually parsed.
///
/// Typically, const statements will be of the (simpler) form:
/// ```text
/// [ Vis ] "const" Ident ":" Type "=" Expr ";"
/// ```
/// This form is the only form that is semantically valid outside of trait definitions. All of the
/// other variants possible correspond to the particular forms that are allowed within trait
/// definitions.
///
/// More specifically, const statments of each variant take on the following meanings when inside
/// of trait definitions:
/// * If a value is given (with `"=" Expr`), this will be given as a default value that may be
///   overriden by the implementor
/// * If no value is given, implementors must supply one.
/// * Instead of a concrete type, a [`TypeBound`] may be given to give additional freedom to the
///   types that may be used as an associated constant (e.g. `const Foo :: Debug`).
///
/// Finally, it should be noted that visibility qualifiers are invalid within trait definitions (or
/// implementations) as the scoping is given instead by the visibility of the trait.
///
/// [`TypeBound`]: struct.TypeBound.html
#[derive(Debug, Clone)]
pub struct ConstStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub vis: Option<Vis<'a>>,
    pub name: Ident<'a>,
    pub value_ty: Option<Type<'a>>,
    pub bound: Option<TypeBound<'a>>,
    pub value: Option<Expr<'a>>,
}

/// A `static` statement
///
/// Syntactically, these are identical to [const statements], with one notable exception -
/// because static values may mutate, proof statments *are* allowed here, where they aren't with
/// const statments.
///
/// For further information, refer to the documentation for [const statements].
///
/// [const statements]: struct.ConstStmt.html
#[derive(Debug, Clone)]
pub struct StaticStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub proof_stmts: Option<ProofStmts<'a>>,
    pub vis: Option<Vis<'a>>,
    pub name: Ident<'a>,
    pub value_ty: Option<Type<'a>>,
    pub bound: Option<TypeBound<'a>>,
    pub value: Option<Expr<'a>>,
}

impl<'a> ConstStmt<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<ConstStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> StaticStmt<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<StaticStmt<'a>, Option<usize>> {
        todo!()
    }
}
