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
    pub field: Field<'a>,
}

/// A `static` statement
///
/// Syntactically, these are identical to [`const` statements], with one notable exception -
/// because static values may mutate, proof statments *are* allowed here, where they aren't with
/// const statments.
///
/// For further information, refer to the documentation for [`const` statements].
///
/// [`const` statements]: struct.ConstStmt.html
#[derive(Debug, Clone)]
pub struct StaticStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub proof_stmts: Option<ProofStmts<'a>>,
    pub vis: Option<Vis<'a>>,
    pub field: Field<'a>,
}

impl<'a> ConstStmt<'a> {
    /// Consumes a `const` item as a prefix of the given tokens
    ///
    /// Some of the pieces common to many items are passed into this function - namely `ident_idx`
    /// and `vis`. The latter should be fairly self-explanatory, but the former is non-trivial.
    ///
    /// The value of `ident_idx` specifies the index in `tokens` where we'll expect the name of the
    /// constant declared here. All of the other components (i.e. visibility qualifiers and the
    /// `const` keyword) are parsed by the caller in [`Item::consume`], so the rest of the parsing
    /// is free to start from the name of the item.
    ///
    /// [`Item::consume`]: ../enum.Item.html#method.consume
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<ConstStmt<'a>, ItemParseErr> {
        let mut consumed = ident_idx;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let field = Field::consume(
            &tokens[consumed..],
            FieldContext::ConstStmt,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;

        consumed += field.consumed();

        // After the field, we're expecting a semicolon:
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::ConstTrailingSemi,
        ));

        Ok(ConstStmt {
            src: &tokens[..consumed],
            vis,
            field,
        })
    }
}

impl<'a> StaticStmt<'a> {
    /// Consumes a `static` item as a prefix of the given tokens
    ///
    /// The arguments to this function serve the same purpose as those to [`FnDecl::consume`]; for
    /// an explanation, please refer to the documentation there.
    ///
    /// [`FnDecl::consume`]: ../fndecl/struct.FnDecl.html#method.consume
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: Option<ProofStmts<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<StaticStmt<'a>, ItemParseErr> {
        // The portion of static statements that we need to parse isn't actually that much. This is
        // basically copied from `ConstStmt::consume` above.
        let mut consumed = ident_idx;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        let field = Field::consume(
            &tokens[consumed..],
            FieldContext::StaticStmt,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;

        consumed += field.consumed();

        // After the field, we're expecting a semicolon:
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::StaticTrailingSemi,
        ));

        Ok(StaticStmt {
            src: &tokens[..consumed],
            proof_stmts,
            vis,
            field,
        })
    }
}
