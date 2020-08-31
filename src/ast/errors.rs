//! Error types and messages for parsing into the AST

use super::{ExprDelim, GenericsArg, Ident, TokenSlice};
use crate::error::{Builder as ErrorBuilder, ToError, ERR_COLOR};
use crate::token_tree::{self, Kwd, Token};
use std::ops::Range;

#[derive(Debug)]
pub enum Error<'a> {
    /// A catch-all error for generically expecting certain tokens or syntax elements
    Expected {
        kind: ExpectedKind<'a>,
        found: Source<'a>,
    },

    /// Certain `Item`s are not allowed to have proof statements before them. This error allows us
    /// to give a clear error message when this type of mistake has been made.
    ProofStmtsDisallowedBeforeItem {
        stmts: TokenSlice<'a>,
        item_kind: ItemKind,
    },

    /// Certain `Item`s aren't allowed to have visibility qualifiers before them. This error allows
    /// us to give a clear error message when this type of mistake has been made.
    VisDisallowedBeforeItem {
        vis: Source<'a>,
        item_kind: ItemKind,
    },

    /// Generic const parameters are required to start with the keyword "const". This error results
    /// from cases where we expect the user has mistakenly missed this piece.
    GenericConstParamMissingConst {
        /// The complete source for the generic parameter that's been parsed. The first two tokens
        /// here are guaranteed to match `[ Ident, ":" ]`.
        full_src: TokenSlice<'a>,
        /// The source for the *type* we parsed.
        type_src: TokenSlice<'a>,
    },

    /// The user has attempted to write `"impl" "<"`, which might indicate generic parameters in
    /// other languages (e.g. Rust), but is not allowed here.
    GenericParamsOnImplBlock {
        /// The less-than token immediately following the `impl`
        src: &'a Token<'a>,
    },

    /// In some places (e.g. 'if' conditions or match scrutinee expressions), curly braces are not
    /// allowed as they are ambiguous with the curly braces of the following block.
    CurliesDisallowed {
        ctx: NoCurlyContext,
        /// The curly brace that was found
        source: Source<'a>,
    },

    /// Comparison expressions are disallowed within a single generics argument
    ComparisonExprDisallowed { source: TokenSlice<'a> },

    /// Some delimited expressions don't allow colons
    UnexpectedExprColon {
        delim: ExprDelim,
        src: TokenSlice<'a>,
    },

    /// There's a unique sort of error that we might run across when parsing an expression. For
    /// more information about this, refer to `Expr::consume_path_component`.
    ///
    /// This error is mostly defined by the place that generates it.
    AmbiguousCloseGenerics {
        path: TokenSlice<'a>,
        op_src: TokenSlice<'a>,
    },

    /// A comma was found after generics argumetns
    UnexpectedGenericsArgsComma {
        ident: &'a Token<'a>,
        args: Vec<GenericsArg<'a>>,
    },

    /// An anonymous struct instantiation was being used as a "big" expression; this is not
    /// allowed, but block expressions *are*.
    StructAsBigExpr {
        outer: &'a Token<'a>,
        ctx: BigExprContext<'a>,
    },

    /// There are expression contexts (namely: do..while conditions) where expressions with
    /// optional else branches aren't allowed.
    PotentialElseDisallowed { src: &'a Token<'a>, kwd: Kwd },

    /// Do..while expressions aren't allowed as part of more complex expressions; if we find one
    /// there, we'll produce an error.
    DoWhileDisallowed { do_token: &'a Token<'a> },

    /// In a similar fashion to the two above, type hints are disallowed within refinement
    /// expressions because they might themselves have refinements
    TypeHintDisallowed { tilde_token: &'a Token<'a> },

    /// Sometimes, we might find a comma following a single generics argument, without being
    /// enclosed by parentheses - e.g:
    /// ```text
    /// Foo<T, S>
    ///      ^ this comma
    /// ```
    /// This should have instead been written as `Foo<(T, S)>`, and so this error message reflects
    /// that, with the angle-bracket, argument, and trailing comma.
    GenericsArgsNotEnclosed {
        leading_angle: &'a Token<'a>,
        arg: TokenSlice<'a>,
        comma: &'a Token<'a>,
    },

    /// "Reference" generics args - i.e. `"ref" Expr` cannot be named
    NamedReferenceGenericsArg {
        name: Ident<'a>,
        ref_kwd: &'a Token<'a>,
    },

    /// Parentheses were found as part of a [`UsePath`] following a dot token, e.g:
    /// ```text
    /// foo.bar.(<something inside parens>)
    /// ```
    /// The user probably meant to use curly braces instead
    ///
    /// [`UsePath`]: ../item/import_use/enum.UsePath.html
    UsePathDotParens {
        path: TokenSlice<'a>,
        parens: &'a Token<'a>,
    },

    /// A [`UsePath`] was likely intended to be a simple use, which requires the type of item
    /// brought into scope to prefix the path
    ///
    /// [`UsePath`]: ../item/import_use/enum.UsePath.html
    MissingUseKind { path: TokenSlice<'a> },

    /// A [glob use] was likely intended, but is missing the dot token between the path and the
    /// asterisk. For example: `foo.bar*` instead of `foo.bar.*`.
    ///
    /// [glob use]: ../item/import_use/struct.GlobUse.html
    MissingGlobUseDot { star_token: &'a Token<'a> },

    /// A [multi-use] was likely intended, but is missing the dot token between the path and curly
    /// braces. For example: `foo{bar, baz}` intead of `foo.{bar, baz}`.
    ///
    /// [multi-use]: ../item/import_use/struct.MultiUse.html
    MissingMultiUseDot { curly_token: &'a Token<'a> },

    /// Type declarations may optionally have bounds; these must be preceeded by a double-colon,
    /// but a user might have accidentally left a single colon instead.
    TypeDeclSingleColonBound { colon: &'a Token<'a> },

    /// Macros are currently unimplemented
    MacrosUnimplemented { macro_kwd: &'a Token<'a> },

    /// Proof statements are currently unimplemented
    ProofStmtsUnimplemented { proof_lines: &'a Token<'a> },
}

/// An individual source for a range of the source text, used within error messages.
#[derive(Debug, Copy, Clone)]
pub enum Source<'a> {
    EndDelim(&'a Token<'a>),
    TokenResult(Result<&'a Token<'a>, token_tree::Error<'a>>),
    EOF,
}

impl<'a> From<&'a Result<Token<'a>, token_tree::Error<'a>>> for Source<'a> {
    fn from(res: &'a Result<Token<'a>, token_tree::Error<'a>>) -> Source<'a> {
        Source::TokenResult(res.as_ref().map_err(|e| *e))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ItemKind {
    Const,
    ImplBlock,
    ImportStmt,
    UseStmt,
}

#[derive(Debug, Copy, Clone)]
pub enum ExpectedKind<'a> {
    ItemKwd(&'static [Kwd]),
    /// We parsed the `const` keyword as the start of an `Item`, but didn't find what we were
    /// expecting - either an `FnDecl` or a `ConstStmt`.
    ///
    /// Function declarations are started by `[ "const" ] [ "pure" ] "fn"`, whereas const
    /// statements are started by `"const" Ident`.
    ///
    /// This is a more specialized error because it exists for a very specific case to provide a
    /// better error message.
    ItemAfterConst {
        /// The token giving us the "const" keyword
        before: &'a Token<'a>,
    },

    /// If parsing an item starts with `["const", "pure"]` or `["pure", "const"]`, we expect `"fn"`
    /// next. In the event that this wasn't what we found, we have a special case here because it
    /// might not be completely clear to the user what went wrong.
    ConstPureExpectedFn {
        /// The two tokens preceeding what we expected to be a "fn" keyword
        before: [&'a Token<'a>; 2],
    },

    /// Whenever we have an item definition starting with the "pure" keyword, we're expecting a
    /// function declaration. We're therefore expecting the next token to be either a "const"
    /// keyword or "fn" keyword.
    PureItemExpectedFnDecl {
        /// The token giving the "pure" keyword
        before: &'a Token<'a>,
    },

    /// When parsing an item, after finding the tokens `"fn" Ident` (and possibly generics
    /// parameters), we'll be expecting the actual parameters of the function
    FnParams {
        /// The tokens starting the function declaration - i.e. `"fn" Ident [ GenericsParams ]`
        fn_start: TokenSlice<'a>,
    },

    /// A comma following a function parameter - either the method receiver or a "normal" parameter
    FnParamsDelim,

    MethodReceiverOrParam,
    MethodReceiverMutOrSelf,
    MethodReceiverSelf,

    ConstTrailingSemi,
    StaticTrailingSemi,

    /// After the `impl` keyword in an item, we're expecting a trait to implement or an
    /// implementing type.
    ImplTraitOrType,

    /// There's some ambiguity when we first see `"impl" Path` - it could be that the path is a
    /// trait we're implementing, or that the path refers instead to the type we're implementing
    /// standalone methods on. There's a set of tokens that we might expect after a path, and this
    /// error indicates that we didn't find something in that set.
    ImplAfterPath,
    ImplBody,

    /// The body of a trait definition; either a semicolon or curly braces.
    TraitDefBody,
    TraitDefTypeBoundOrImplBody,

    ImportSourceString,
    /// In import statements, a tilde may be given after the source string in order to specify
    /// version information. This variant represents a failure to find a tilde or any of the tokens
    /// allowed after the initial source.
    ImportVersionTilde,
    /// The string literal giving the version of an imported library, given directly following the
    /// tilde
    ImportVersionString,
    /// Like `ImportVersionTilde`, this error signifies that none of the set of expected tokens at
    /// the point where we *might* parse the `as` keyword were there
    ImportRenameAs,
    ImportRenameIdent,
    /// The trailing semicolon required after an import statement
    ImportTrailingSemi,

    UsePath,
    /// The trailing semicolon required after a `use` statement
    UseTrailingSemi,
    UsePathSingleAsIdent,
    /// The set of tokens in a `UsePath` that are allowed after a dot token - identifiers, curlies,
    /// stars, and commas/semicolons.
    UsePathPostDot,
    /// Commas are expected between `UsePath`s in a `MultiUse`
    MultiUseCommaDelim,

    TypeDeclBoundOrAfter,
    TypeDeclTrailingSemi,
    TypeDeclType,

    FieldBound(FieldContext),

    Ident(IdentContext<'a>),
    ExprLhs,
    GenericsArgOrExpr,
    LetColonOrEq(LetContext<'a>),
    LetEq(LetContext<'a>),
    ForLoopInKwd(TokenSlice<'a>), // The previous tokens in the start of the for loop
    FnArgDelim(&'a Token<'a>),    // The containing token
    StructFieldExprName,
    StructFieldExprColonOrComma {
        name: &'a Token<'a>,
        containing_token: &'a Token<'a>,
    },
    StructFieldExprDelim(&'a Token<'a>), // The containing token
    ArrayDelim(&'a Token<'a>),           // The containing token
    TupleDelim(&'a Token<'a>),           // The containing token
    MatchBody(&'a Token<'a>),            // The `match` token
    MatchArmArrow,
    MatchArmDelim(TokenSlice<'a>), // The arm after which we're expecting a delimiter
    DotAccess(&'a Token<'a>),      // The dot token
    BlockExpr,
    Stmt,
    TrailingSemi {
        expr_src: TokenSlice<'a>,
    },
    EndOfIndexPostfix,
    BigExpr(BigExprContext<'a>),
    DoWhileWhileToken,
    Pattern(PatternContext<'a>),
    StructPatternField(PatternContext<'a>),
    StructPatternEnd(PatternContext<'a>),
    StructPatternDelim(PatternContext<'a>, &'a Token<'a>), // The containing token
    TuplePatternElement(PatternContext<'a>),
    TuplePatternDelim(PatternContext<'a>, &'a Token<'a>), // The containing token
    ArrayPatternElement(PatternContext<'a>),
    ArrayPatternDelim(PatternContext<'a>, &'a Token<'a>), // The containing token
    GenericsParams(GenericsParamsContext<'a>),
    Type(TypeContext<'a>),
    MutTypeKeyword(TypeContext<'a>),
    ArrayTypeSemi(TypeContext<'a>),
    ArrayTypeInnerEnd,
    StructTypeFieldDelim,
    StructTypeFieldColon,
    TupleTypeElemDelim,
    EnumTypeCurlies,
    EnumTypeVariantDelim,
    GenericsArgDelim,
    RefinementDelim,
    GenericsParam {
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
    },
    GenericTypeParamColons {
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
    },
    GenericsParamDelim {
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
    },
    GenericsArg {
        prev_tokens: TokenSlice<'a>,
    },
    GenericsArgCloseAngleBracket {
        args_tokens: TokenSlice<'a>,
    },
    TypeParamFollowOn {
        after_type_bound: bool,
        ctx: GenericsParamsContext<'a>,
        prev_tokens: TokenSlice<'a>,
        param: TokenSlice<'a>,
    },
    FnBody {
        fn_src: TokenSlice<'a>,
    },
    FnBodyOrReturnType {
        fn_src: TokenSlice<'a>,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum IdentContext<'a> {
    /// The identifier used to name functions, provided immediately following the `fn` keyword. The
    /// attached slice of tokens gives the keywords used that indicate a function declaration.
    FnDeclName(TokenSlice<'a>),

    /// The name at the start of a generic type parameter, given as part of a function declaration
    /// or type declaration. The attached slice of tokens gives the set of tokens already parsed as
    /// part of the list of generic parameters.
    TypeParam(GenericsParamsContext<'a>, TokenSlice<'a>),

    /// The name defined in a trait definition; the token here is the "trait" keyword
    TraitDef {
        kwd_token: &'a Token<'a>,
    },

    GenericRefParam,

    /// Path components expect an identifier
    PathComponent(PathComponentContext<'a>),
    PatternPath(PatternContext<'a>, TokenSlice<'a>),
    NamedExpr(super::ExprDelim),
    StructTypeField,
    EnumVariant,
    Field(FieldContext),
}

#[derive(Debug, Copy, Clone)]
pub enum GenericsParamsContext<'a> {
    /// The generics parameters used in a function declaration. The attached slice of tokens gives
    /// the keywords and name that indicate a function declaration.
    FnDecl(TokenSlice<'a>),

    /// The tokens given here are the
    TraitDef(TokenSlice<'a>),

    TypeDecl,
}

#[derive(Debug, Copy, Clone)]
pub enum TypeContext<'a> {
    /// The optional return type used in a function declaration. The attached slice of tokens gives
    /// all of the preceeding parts of the item.
    FnDeclReturn(TokenSlice<'a>),
    GenericTypeParam {
        param: TokenSlice<'a>,
        ctx: GenericsParamsContext<'a>,
    },
    GenericConstParam {
        param: TokenSlice<'a>,
        ctx: GenericsParamsContext<'a>,
    },
    GenericsArg {
        prev_tokens: TokenSlice<'a>,
        name: Option<&'a Token<'a>>,
    },
    LetHint(LetContext<'a>),
    TypeBinding {
        tilde: &'a Token<'a>,
    },
    ImplBlockType {
        /// The tokens starting the `impl` block; essentially defined to satisfy
        /// `"impl" [ Trait "for" ]`
        prev_tokens: TokenSlice<'a>,
    },
    TypeDecl,
    FieldBound(FieldContext),
}

#[derive(Debug, Copy, Clone)]
pub enum FieldContext {
    FnParam,
    ConstStmt,
    StaticStmt,
    GenericConstParam,
}

#[derive(Debug, Copy, Clone)]
pub struct PathComponentContext<'a> {
    /// The previous tokens within the greater path; this will be `None` if the expected path
    /// component is the first.
    pub prev_tokens: Option<TokenSlice<'a>>,
}

#[derive(Debug, Copy, Clone)]
pub enum NoCurlyContext {
    IfCondition,
    ForIter,
    WhileCondition,
    MatchExpr,
}

#[derive(Debug, Copy, Clone)]
pub enum BigExprContext<'a> {
    Else(&'a Token<'a>),
}

#[derive(Debug, Copy, Clone)]
pub struct LetContext<'a> {
    pub let_kwd: &'a Token<'a>,
    pub pat: TokenSlice<'a>,
}

#[derive(Debug, Copy, Clone)]
pub enum PatternContext<'a> {
    Let(&'a Token<'a>),
    Match(&'a Token<'a>),
    For(&'a Token<'a>),
    Is(&'a Token<'a>),
}

impl<F: Fn(Option<&str>) -> Range<usize>> ToError<(F, &str)> for Error<'_> {
    fn to_error(self, aux: &(F, &str)) -> ErrorBuilder {
        use Error::*;

        let (ref ranger, ref file_name) = aux;

        match self {
            Expected { kind, found } => kind.make_error(found, ranger, file_name),
            _ => {
                println!("unformatted error: {:?}", self);
                todo!()
            }
        }

        // // TODO: This is really just a temporary implementation until we give these good formatting
        // // later. It's just for checking that it *does* work
        // let s = format!("{:?}", self);
        // ErrorBuilder::new("Parse error").text(s)
    }
}

// impl Error<'_> {
//
// }

impl ExpectedKind<'_> {
    fn make_error(
        &self,
        src: Source,
        ranger: impl Fn(Option<&str>) -> Range<usize>,
        file_name: &str,
    ) -> ErrorBuilder {
        let src_range = src.range(ranger);

        // TODO: This is really just a temporary implementation until we give these good formatting
        // later. It's just for checking that it *does* work
        let s = format!("{:?}", self);
        ErrorBuilder::new("Parse error")
            .context(file_name, src_range.start)
            .highlight(file_name, vec![src_range], ERR_COLOR)
            .text(s)
    }
}

trait Ranged {
    fn range(&self, ranger: impl Fn(Option<&str>) -> Range<usize>) -> Range<usize>;
}

impl Ranged for Token<'_> {
    fn range(&self, ranger: impl Fn(Option<&str>) -> Range<usize>) -> Range<usize> {
        let start = ranger(Some(self.src[0].src));
        let end = ranger(Some(self.src.last().unwrap().src));

        start.start..end.end
    }
}

impl Ranged for Source<'_> {
    fn range(&self, ranger: impl Fn(Option<&str>) -> Range<usize>) -> Range<usize> {
        match self {
            Source::EndDelim(token) => {
                let Range { start, end } = token.range(ranger);
                assert!(start < end);

                (end - 1)..end
            }
            Source::TokenResult(Ok(t)) => t.range(ranger),
            Source::TokenResult(Err(e)) => {
                use token_tree::Error::*;

                match e {
                    UnexpectedCloseDelim(t) => ranger(Some(t.src)),
                    MismatchedCloseDelim { end, .. } => ranger(Some(end.src)),
                    UnclosedDelim(_, ts, _) => {
                        let start = ranger(Some(ts[0].src));
                        let end = ranger(Some(ts.last().unwrap().src));
                        start.start..end.end
                    }
                    NestedProofLines(_, t) => ranger(Some(t.src)),
                }
            }
            Source::EOF => ranger(None),
        }
    }
}
