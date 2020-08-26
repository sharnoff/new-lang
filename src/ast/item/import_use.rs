use super::*;

/// An import statment
///
/// **Note that this feature is a work-in-progress, and so the specifics have not yet been
/// defined.**
///
/// These serve to bring in external libraries as identifiers - for bringing individual items into
/// scope, see [`UseStmt`s].
///
/// The BNF definition for import statmtents is:
/// ```text
/// ImportStmt = "import" StringLiteral [ "~" StringLiteral ] [ "as" Ident ] .
/// ```
///
/// The first string literal gives the source for the library - typically a url. The second string,
/// if provided, indicates the version of the library to use. If left out, the version will be
/// assumed to be identical to whatever is present elsewhere in the local source tree. This is not
/// allowed if there are different versions of the same library in use within the same source tree.
///
/// The final identifier optionally gives a namespace to import the library under. In most cases,
/// this will be automatically determined - in others (typically with names that cannot be
/// converted to an identifier), the user *must* supply an identifier to rename as.
///
/// [`UseStmt`s]: struct.UseStmt.html
#[derive(Debug, Clone)]
pub struct ImportStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub source: StringLiteral<'a>,
    pub version: Option<StringLiteral<'a>>,
    pub as_name: Ident<'a>,
}

/// A "use" statment
///
/// These serve to bring individual items into scope. Each item brought into scope requires the
/// type of the item to be explicitly given (e.g. `fn`, `type`, `trait`, etc).
///
/// "Use" statments are not allowed within trait definitions, but are allowed within `impl` blocks,
/// simply as a method of providing items to the local scope - in these cases, they cannot affect
/// how the impl block is viewed from outside.
///
/// The BNF definition is defined in parts - we'll list all three here for completeness:
/// ```text
/// UseStmt = Vis "use" UsePath ";" .
/// UsePath = Path "." "{" UsePath { "," UsePath } [ "," ] "}" .
///         | UseKind Path [ "as" Ident ] .
/// UseKind = "fn" | "macro" | "type" | "trait" | "const" | "static" .
/// ```
/// Multiple items under a single namespace may be brought into scope with curly braces (as seen by
/// the first variant of [`UsePath`]). Items may also be renamed as they are brought into scope.
///
/// [`UsePath`]: enum.UsePath.html
#[derive(Debug, Clone)]
pub struct UseStmt<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub vis: Option<Vis<'a>>,
    pub path: UsePath<'a>,
}

#[derive(Debug, Clone)]
pub enum UsePath<'a> {
    Multi(MultiUse<'a>),
    Single(SingleUse<'a>),
}

#[derive(Debug, Clone)]
pub struct MultiUse<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub root: Path<'a>,
    pub children: Vec<UsePath<'a>>,
}

#[derive(Debug, Clone)]
pub struct SingleUse<'a> {
    pub(in crate::ast) src: TokenSlice<'a>,
    pub kind: UseKind,
    pub path: Path<'a>,
    pub use_as: Option<Ident<'a>>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UseKind {
    /// `fn`
    Fn,
    /// `macro`
    Macro,
    /// `type`
    Type,
    /// `trait`
    Trait,
    /// `const`
    Const,
    /// `static`
    Static,
}

impl<'a> ImportStmt<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ImportStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> UseStmt<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<UseStmt<'a>, Option<usize>> {
        todo!()
    }
}
