//! Error types and messages for parsing into the AST

use super::{ExprDelim, TokenResult};
use crate::error::{Builder as ErrorBuilder, ERR_COLOR};
use crate::files::{FileInfo, Span};
use crate::token_tree::{self, Kwd};
use crate::token_tree::{Token, TokenKindMarker as TokenKind};
use std::ops::Range;

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug)]
pub enum Error {
    /// A catch-all error for generically expecting certain tokens or syntax elements
    Expected { kind: ExpectedKind, found: Source },

    /// Certain `Item`s are not allowed to have proof statements before them. This error allows us
    /// to give a clear error message when this type of mistake has been made.
    ProofStmtsDisallowedBeforeItem { stmts: Span, item_kind: ItemKind },

    /// Certain `Item`s aren't allowed to have visibility qualifiers before them. This error allows
    /// us to give a clear error message when this type of mistake has been made.
    VisDisallowedBeforeItem { vis: Span, item_kind: ItemKind },

    /// Generic const parameters are required to start with the keyword "const". This error results
    /// from cases where we expect the user has mistakenly missed this piece.
    GenericConstParamMissingConst {
        /// The complete source for the generic parameter that's been parsed. The first two tokens
        /// here are guaranteed to match `[ Ident, ":" ]`.
        full_src: Span,
        /// The source for the *type* we parsed.
        type_src: Span,
    },

    /// The user has attempted to write `"impl" "<"`, which might indicate generic parameters in
    /// other languages (e.g. Rust), but is not allowed here.
    GenericParamsOnImplBlock {
        /// The less-than token immediately following the `impl`
        src: Source,
    },

    /// In some places (e.g. 'if' conditions or match scrutinee expressions), curly braces are not
    /// allowed as they are ambiguous with the curly braces of the following block.
    CurliesDisallowed {
        ctx: NoCurlyContext,
        /// The curly brace that was found
        src: Source,
    },

    /// Some delimited expressions don't allow colons
    UnexpectedExprColon { delim: ExprDelim, src: Span },

    /// There's a unique sort of error that we might run across when parsing an expression. For
    /// more information about this, refer to `Expr::consume_path_component`.
    ///
    /// This error is mostly defined by the place that generates it.
    AmbiguousCloseGenerics { path: Span, op_src: Span },

    /// A comma was found after generics arguments
    UnexpectedGenericsArgsComma { ident: Span, args: Vec<Span> },

    /// Assignment operators are disallowed in struct expressions. For more information, please
    /// refer to the documentation for `StructExpr` and the comment inside of
    /// `StructTypeOrExpr::parse`.
    AssignOpDisallowedInStructExpr { op_src: Span },

    /// An anonymous struct instantiation was being used as a "big" expression; this is not
    /// allowed, but block expressions *are*.
    StructAsBigExpr { outer: Span, ctx: BigExprContext },

    /// There are expression contexts (namely: do..while conditions) where expressions with
    /// optional else branches aren't allowed.
    PotentialElseDisallowed { src: Source, kwd: Kwd },

    /// Do..while expressions aren't allowed as part of more complex expressions; if we find one
    /// there, we'll produce an error.
    DoWhileDisallowed { do_token: Source },

    /// In a similar fashion to the two above, type hints are disallowed within refinement
    /// expressions because they might themselves have refinements
    TypeHintDisallowed { tilde_token: Source },

    /// Sometimes, we might find a comma following a single generics argument, without being
    /// enclosed by parentheses - e.g:
    /// ```text
    /// Foo<T, S>
    ///      ^ this comma
    /// ```
    /// This should have instead been written as `Foo<(T, S)>`, and so this error message reflects
    /// that, with the angle-bracket, argument, and trailing comma.
    GenericsArgsNotEnclosed {
        leading_angle: Source,
        arg: Span,
        comma: Source,
    },

    /// "Reference" generics args - i.e. `"ref" Expr` cannot be named
    NamedReferenceGenericsArg { name: Span, ref_kwd: Source },

    /// Parentheses were found as part of a [`UsePath`] following a dot token, e.g:
    /// ```text
    /// foo.bar.(<something inside parens>)
    /// ```
    /// The user probably meant to use curly braces instead
    ///
    /// [`UsePath`]: ../item/import_use/enum.UsePath.html
    UsePathDotParens { path: Span, parens: Source },

    /// A [`UsePath`] was likely intended to be a simple use, which requires the type of item
    /// brought into scope to prefix the path
    ///
    /// [`UsePath`]: ../item/import_use/enum.UsePath.html
    MissingUseKind { path: Span },

    /// A [glob use] was likely intended, but is missing the dot token between the path and the
    /// asterisk. For example: `foo.bar*` instead of `foo.bar.*`.
    ///
    /// [glob use]: ../item/import_use/struct.GlobUse.html
    MissingGlobUseDot { star_token: Source },

    /// A [multi-use] was likely intended, but is missing the dot token between the path and curly
    /// braces. For example: `foo{bar, baz}` intead of `foo.{bar, baz}`.
    ///
    /// [multi-use]: ../item/import_use/struct.MultiUse.html
    MissingMultiUseDot { curly_token: Source },

    /// Type declarations may optionally have bounds; these must be preceeded by a double-colon,
    /// but a user might have accidentally left a single colon instead.
    TypeDeclSingleColonBound { colon: Source },

    /// Macros are currently unimplemented
    MacrosUnimplemented { macro_kwd: Source },

    /// Proof statements are currently unimplemented
    ProofStmtsUnimplemented { proof_lines: Span },

    /// Very occasionally, we'll have token following pipes that *might* be refinements in a way
    /// that is properly ambiguous. We don't allow that as valid syntax, so we request that the user
    /// disambiguate with parentheses.
    ///
    /// For context, here's an example of the type of expression that would produce this error:
    /// ```text
    /// (foo, bar ~ Vec |len == 4, baz| -3)
    /// //          ^^^^^^^^^^^^^  ^^^^^^^ perhaps a single tuple entry?
    /// //                \- the start of refinements?
    /// ```
    /// This should be rewritten as either of the following:
    /// ```text
    /// (foo, (bar ~ Vec |len == 4, baz|), -3)
    /// (foo, (bar ~ Vec | len == 4), baz | -3)
    /// ```
    ///
    /// This can happen for any token that can both start an expression and continue a fully-formed
    /// one; it cannot happen for anything else.
    AmbiguousExprAfterRefinements {
        refinements_src: Span,
        ambiguous_token: Source,
    },
}

/// An individual source for a range of the source text, used within error messages.
#[derive(Debug, Copy, Clone)]
pub struct Source {
    pub(super) span: Span,
    kind: SourceKind,
}

/// The types of error sources available, aside from [`Span`]s
///
/// [`Span`]: ../../files/struct.Span.html
#[derive(Debug, Copy, Clone)]
enum SourceKind {
    EOF,
    Error(token_tree::ErrorKind),
    Token(TokenKind),
    TokenEnd(TokenKind),
}

impl Source {
    /// Produces a `Source` from a token result, given the source file for the token
    pub fn from(file: &FileInfo, res: &TokenResult) -> Source {
        match res {
            Err(e) => Source::err(file, e),
            Ok(t) => Source::token(file, t),
            // Err(e) => (e.span(file), SourceKind::Error(e.kind())),
            // Ok(t) => (t.span(file), SourceKind::Token(t.kind())),
        }
    }

    /// Produces a `Source` from a single token, given the corresponding source file
    pub fn token(file: &FileInfo, token: &Token) -> Source {
        Source {
            span: token.span(file),
            kind: SourceKind::Token(token.kind()),
        }
    }

    pub fn err(file: &FileInfo, err: &token_tree::Error) -> Source {
        Source {
            span: err.span(file),
            kind: SourceKind::Error(err.kind()),
        }
    }

    /// Returns the `Source` corresponding exactly to the end of the given file
    pub fn eof(file: &FileInfo) -> Source {
        Source {
            span: file.eof_span(),
            kind: SourceKind::EOF,
        }
    }

    /// Returns the [`Span`] corresponding to the slice of tokens
    ///
    /// [`Span`]: ../../files/struct.Span.html
    pub fn slice_span(file: &FileInfo, range: &[TokenResult]) -> Span {
        let start = Source::from(file, &range[0]);
        let end = Source::from(file, &range[range.len() - 1]);
        start.span.join(end.span)
    }

    /// Produces a `Source` from the end of a given token
    ///
    /// If the provided token was not a delimited token or collection of proof lines, this function
    /// will panic.
    pub fn end_delim(file: &FileInfo, token: &Token) -> Source {
        let span = token.end_span(file);

        let kind = token.kind();
        match kind {
            TokenKind::Tree(delim) => Source {
                span,
                kind: SourceKind::TokenEnd(kind),
            },
            TokenKind::ProofLines => {
                // Because proof lines don't have a unique ending token (unlike parentheses, curly
                // braces, etc.), we need some way of getting a span that indicates what we
                // *actually* mean. The simple way we'll do that is by going *just* past the end of
                // the span of the last token:
                let start = span.end;

                let span = Span {
                    file: file.id,
                    start,
                    end: start + 1,
                };

                // This is okay to do because there's support built in elsewhere for handling spans
                // that go one byte past the end of the file.
                Source {
                    span,
                    kind: SourceKind::TokenEnd(kind),
                }
            }
            k => panic!("unexpected token kind for `Source::end_delim`; got {:?}", k),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ItemKind {
    Const,
    ImplBlock,
    ImportStmt,
    UseStmt,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum ExpectedKind {
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
        before: Source,
    },

    /// If parsing an item starts with `["const", "pure"]` or `["pure", "const"]`, we expect `"fn"`
    /// next. In the event that this wasn't what we found, we have a special case here because it
    /// might not be completely clear to the user what went wrong.
    ConstPureExpectedFn {
        /// The two tokens preceeding what we expected to be a "fn" keyword
        before: [Source; 2],
    },

    /// Whenever we have an item definition starting with the "pure" keyword, we're expecting a
    /// function declaration. We're therefore expecting the next token to be either a "const"
    /// keyword or "fn" keyword.
    PureItemExpectedFnDecl {
        /// The token giving the "pure" keyword
        before: Source,
    },

    /// When parsing an item, after finding the tokens `"fn" Ident` (and possibly generics
    /// parameters), we'll be expecting the actual parameters of the function
    FnParams {
        /// The tokens starting the function declaration - i.e. `"fn" Ident [ GenericsParams ]`
        fn_start: Span,
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

    Ident(IdentContext),
    ExprLhs,
    LetColonOrEq(LetContext),
    LetEq(LetContext),
    ForLoopInKwd(Span), // The previous tokens in the start of the for loop
    FnArgDelim(Source), // The containing token
    StructFieldExprName,
    StructFieldExprColonOrComma {
        name: Source,
        containing_token: Span,
    },
    StructFieldExprDelim(Source), // The containing token
    ArrayDelim(Source),           // The containing token
    TupleDelim(Source),           // The containing token
    MatchBody(Source),            // The `match` token
    MatchArmArrow,
    MatchArmDelim(Span), // The arm after which we're expecting a delimiter
    DotAccess(Source),   // The dot token
    BlockExpr,
    TrailingSemi {
        expr_src: Span,
    },
    EndOfIndexPostfix,
    BigExpr(BigExprContext),
    DoWhileWhileToken,
    Pattern(PatternContext),
    StructPatternField(PatternContext),
    StructPatternEnd(PatternContext),
    StructPatternDelim(PatternContext, Source), // The containing token
    TuplePatternElement(PatternContext),
    TuplePatternDelim(PatternContext, Source), // The containing token
    ArrayPatternElement(PatternContext),
    ArrayPatternDelim(PatternContext, Source), // The containing token
    GenericsParams(GenericsParamsContext),
    Type(TypeContext),
    MutTypeKeyword(TypeContext),
    ArrayTypeSemi(TypeContext),
    ArrayTypeInnerEnd,
    StructTypeFieldDelim,
    StructTypeFieldColon,
    TupleTypeElemDelim,
    EnumTypeCurlies,
    EnumTypeVariantDelim,
    GenericsArgDelim,
    RefinementDelim,
    GenericsParam {
        ctx: GenericsParamsContext,
        prev_tokens: Span,
    },
    GenericTypeParamColons {
        ctx: GenericsParamsContext,
        prev_tokens: Span,
    },
    GenericsParamDelim {
        ctx: GenericsParamsContext,
        prev_tokens: Span,
    },
    GenericsArg {
        prev_tokens: Span,
    },
    GenericsArgCloseAngleBracket {
        args_tokens: Span,
    },
    TypeOrExpr,
    /// After a dot token (`.`) when parsing a `TypeOrExpr`, we're expecting either an integer
    /// literal (for tuple access) or an identifier
    TypeOrExprFollowDot,
    /// After a reference (`&`), we're expecting refinements, a type, or an expression.
    TypeOrExprFollowRef,
    /// After something like `&!`, we're either expecting the keyword "mut" for a type, or an
    /// expression.
    ///
    /// Note that neither of these are typically *semantically* valid, but we're required to parse
    /// them correctly.
    TypeOrExprFollowRefNot,
    /// The comma separating items in a tuple `TypeOrExpr`
    TupleTypeOrExprComma,
    /// At the start of parsing a curly-brace-enclosed `TypeOrExpr`, we might have a visibility
    /// qualifier. This is either part of a struct (type) field OR as an item in a block expression
    /// (even though that visibility qualifier might be semantically invalid).
    StructTypeFieldOrItem,
    /// The first tokens inside of an ambiguous struct type or (maybe block) expression. This is an
    /// exceptionally rare error because *literally anything* can go here.
    StructTypeOrExprInner,
    /// If we find an ambiguous struct type or expression with a leading identifier inside, we can
    /// parse it as an expression, struct *expression* field name, or struct *type* field name.
    /// This error represents none of these patterns fitting.
    StructTypeOrExprFollowIdent,
    /// The comma delimiting multiple fields in an ambiguous struct
    StructTypeOrExprComma,
    /// In a struct `TypeOrExpr`, each field must start with a name (or a visibility qualifier,
    /// implying that it is a type).
    StructTypeOrExprFieldNameOrVis,
    /// Individual field names in struct `TypeOrExpr`s must be followed by any of ":" (ambiguous),
    /// "," (expression), or the closing curly brace (also as an expression).
    StructTypeOrExprFollowFieldIdent,

    /// After an initial `TypeOrExpr` inside an array, we're either expecting a comma (to indicate
    /// repeated elements in an expression) or a semicolon (to indicate the length, as a type).
    ArrayTypeOrExprCommaOrSemi,

    TypeParamFollowOn {
        after_type_bound: bool,
        ctx: GenericsParamsContext,
        prev_tokens: Span,
        param: Span,
    },
    FnBody {
        fn_src: Span,
    },
    FnBodyOrReturnType {
        fn_src: Span,
    },
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum IdentContext {
    /// The identifier used to name functions, provided immediately following the `fn` keyword. The
    /// attached slice of tokens gives the keywords used that indicate a function declaration.
    FnDeclName(Span),

    /// The name at the start of a generic type parameter, given as part of a function declaration
    /// or type declaration. The attached slice of tokens gives the set of tokens already parsed as
    /// part of the list of generic parameters.
    TypeParam(GenericsParamsContext, Span),

    /// The name defined in a trait definition; the token here is the "trait" keyword
    TraitDef {
        kwd_token: Source,
    },

    GenericRefParam,

    /// Path components expect an identifier
    PathComponent(PathComponentContext),
    PatternPath(PatternContext, Span),
    StructTypeField,
    EnumVariant,
    Field(FieldContext),
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum GenericsParamsContext {
    /// The generics parameters used in a function declaration. The attached slice of tokens gives
    /// the keywords and name that indicate a function declaration.
    FnDecl(Span),

    /// The tokens given here are the
    TraitDef(Span),

    TypeDecl,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum TypeContext {
    /// The optional return type used in a function declaration. The attached slice of tokens gives
    /// all of the preceeding parts of the item.
    FnDeclReturn(Span),
    GenericTypeParam {
        param: Span,
        ctx: GenericsParamsContext,
    },
    GenericConstParam {
        param: Span,
        ctx: GenericsParamsContext,
    },
    GenericsArg {
        prev_tokens: Option<Span>,
        name: Option<Span>,
    },
    LetHint(LetContext),
    TypeBinding {
        tilde: Source,
    },
    ImplBlockType {
        /// The tokens starting the `impl` block; essentially defined to satisfy
        /// `"impl" [ Trait "for" ]`
        prev_tokens: Span,
    },
    TypeDecl,
    FieldBound(FieldContext),
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum FieldContext {
    FnParam,
    ConstStmt,
    StaticStmt,
    GenericConstParam,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub struct PathComponentContext {
    /// The previous tokens within the greater path; this will be `None` if the expected path
    /// component is the first.
    pub prev_tokens: Option<Span>,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum NoCurlyContext {
    IfCondition,
    ForIter,
    WhileCondition,
    MatchExpr,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum BigExprContext {
    Else(Source),
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub struct LetContext {
    pub let_kwd: Source,
    pub pat: Span,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum PatternContext {
    Let(Source),
    Match(Source),
    For(Source),
    Is(Source),
}

impl Into<ErrorBuilder> for Error {
    fn into(self) -> ErrorBuilder {
        use Error::*;

        match self {
            Expected { kind, found } => return kind.make_error(found),
            _ => (),
        }

        // TODO: This is really just a temporary implementation until we give these good formatting
        // later. It's just for checking that it *does* work
        let s = format!("{:?}", self);
        ErrorBuilder::new("Parse error").text(s)
    }
}

impl ExpectedKind {
    fn make_error(&self, src: Source) -> ErrorBuilder {
        // TODO: This is really just a temporary implementation until we give these good formatting
        // later. It's just for checking that it *does* work
        let s = format!("{:?}", self);
        ErrorBuilder::new("Parse error")
            .context(src.span)
            .highlight(src.span, ERR_COLOR)
            .text(s)
    }
}
