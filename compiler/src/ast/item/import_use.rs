use super::*;
use crate::files::{FileInfo, Span};
use crate::tokens::LiteralKind;
use std::convert::TryFrom;

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
/// ImportStmt = "import" StringLiteral [ "~" StringLiteral ] [ "as" Ident ] ";" .
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
#[derive(Debug, Clone, Consumed)]
pub struct ImportStmt {
    #[consumed(2)] // +1 for "import"; "+1" for trailing semicolon
    pub(in crate::ast) src: Span,
    pub source: StringLiteral,
    #[consumed(version.as_ref().map(|s| s.consumed() + 1).unwrap_or(0))] // +1 for "~"
    pub version: Option<StringLiteral>,
    #[consumed(rename.as_ref().map(|i| i.consumed() + 1).unwrap_or(0))] // +1 for "as"
    pub rename: Option<Ident>,
}

/// A `use` statment
///
/// These serve to bring individual items into scope. Each item brought into scope requires the
/// type of the item to be explicitly given (e.g. `fn`, `type`, `trait`, etc).
///
/// The BNF definition is defined in parts - we'll list them all here for completeness:
/// ```text
/// UseStmt   = Vis "use" UsePath ";" .
/// UsePath   = MultiUse | GlobUse | SingleUse .
///
/// MultiUse  = Path "." "{" UsePath { "," UsePath } [ "," ] "}" .
/// GlobUse   = Path "." "*" .
/// SingleUse = UseKind Path [ "as" Ident ] .
///
/// UseKind   = "fn" | "macro" | "type" | "trait" | "const" | "static" | "mod" .
/// ```
/// Multiple items under a single namespace may be brought into scope with curly braces (as seen by
/// the first variant of [`UsePath`] - [`MultiUse`]). Glob usage (bringing all of the items within a
/// namespace into scope) is given through [`GlobUse`]. Items may also be renamed as they are
/// brought into scope.
///
/// Finally, one piece to note is that `UseStmt`s are allowed to omit the trailing semicolon if and
/// only if the [`UsePath`] is a multi-use - i.e. if it uses curly-braces.
///
/// [`UsePath`]: enum.UsePath.html
/// [`MultiUse`]: enum.MultiUse.html
/// [`GlobUse`]: enum.GlobUse.html
#[derive(Debug, Clone, Consumed)]
pub struct UseStmt {
    #[consumed(2)] // +1 for "use"; "+1" for trailing semicolon
    pub(in crate::ast) src: Span,
    pub vis: Option<Vis>,
    pub path: UsePath,
}

/// A helper type for [`UseStmt`]s
///
/// This type gives the different options for the majority of the syntax in a single [`UseStmt`].
/// The BNF of this type is essentially given by the variants here. For more information, please
/// refer to the documentation for [`UseStmt`].
///
/// [`UseStmt`]: struct.UseStmt.html
#[derive(Debug, Clone, Consumed)]
pub enum UsePath {
    Multi(MultiUse),
    Glob(GlobUse),
    Single(SingleUse),
}

/// A [`UsePath`] variant that allows for bringing multiple items into scope
///
/// For more information, please refer to the documentation for [`UseStmt`].
///
/// [`UsePath`]: enum.UsePath.html
/// [`UseStmt`]: struct.UseStmt.html
#[derive(Debug, Clone, Consumed)]
pub struct MultiUse {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    pub root: Path,
    #[consumed(1)] // enclosed in curly braces
    pub children: Vec<UsePath>,
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A [`UsePath`] variant for bringing all items in a namespace into scope
///
/// For more information, please refer to the documentation for [`UseStmt`].
///
/// [`UsePath`]: enum.UsePath.html
/// [`UseStmt`]: struct.UseStmt.html
#[derive(Debug, Clone, Consumed)]
pub struct GlobUse {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    pub root: Path,
    #[consumed(2)] // +1 for the "." between the path and the star
    pub star_token: Span,
}

/// The standard method of bringing items into scope; a [`UsePath`] variant
///
/// This type is defined by the following BNF construction:
/// ```text
/// UsePath = UseKind Path [ "as" Ident ] .
/// ```
///
/// Examples include:
/// * `type std.foo.Bar`
/// * `mod baz.qux as my_mod`
#[derive(Debug, Clone, Consumed)]
pub struct SingleUse {
    #[consumed(@ignore)]
    pub(in crate::ast) src: Span,
    #[consumed(@ignore)]
    pub kind_src: Span,
    #[consumed(1)]
    pub kind: UseKind,
    pub path: Path,
    #[consumed(use_as.as_ref().map(|i| i.consumed() + 1).unwrap_or(0))] // +1 for "as"
    pub use_as: Option<Ident>,
}

/// The types of items that may be brought into scope with a [`UseStmt`]
///
/// [`UseStmt`]: struct.UseStmt.html
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
    /// `mod`
    Mod,
}

impl ImportStmt {
    /// Consumes an `import` statment as a prefix of the given tokens
    ///
    /// This function expects that the first token it is given is the keyword `import`, and will
    /// panic if this is not the case.
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<ImportStmt, ItemParseErr> {
        assert_token!(
            tokens.first() => "keyword `import`",
            Ok(t) && TokenKind::Keyword(Kwd::Import) => (),
        );

        let mut consumed = 1;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        macro_rules! err {
            () => {{
                return Err(ItemParseErr { consumed });
            }};
        }

        // The rest of the import statement goes as follows:
        //   StringLiteral [ "~" StringLiteral ] [ "as" Ident ] ";"
        // As such, it's fairly straightforward from here:
        //
        // We expect the first string literal:
        let source = expect!((
            Ok(src),
            TokenKind::Literal(content, LiteralKind::String) => StringLiteral { src: src.span(file), content: (*content).into() },
            @else { err!() } => ExpectedKind::ImportSourceString,
        ));

        consumed += 1;

        // [ "~" StringLiteral ]
        let version = expect!((
            Ok(_),
            TokenKind::Keyword(Kwd::As)
            | TokenKind::Punctuation(Punc::Semi) => None,
            TokenKind::Punctuation(Punc::Tilde) => {
                consumed += 1;

                let lit = expect!((
                    Ok(src),
                    TokenKind::Literal(content, LiteralKind::String) => {
                        StringLiteral { src: src.span(file), content: (*content).into() }
                    },
                    @else { err!() } => ExpectedKind::ImportVersionString,
                ));

                consumed += 1;
                Some(lit)
            },
            @else { err!() } => ExpectedKind::ImportVersionTilde,
        ));

        // [ "as" Ident ]
        let rename = expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Semi) => None,
            TokenKind::Keyword(Kwd::As) => {
                consumed += 1;

                let ident = expect!((
                    Ok(src), TokenKind::Ident(name) => Ident { src: src.span(file), name: (*name).into() },
                    @else { err!() } => ExpectedKind::ImportRenameIdent,
                ));

                consumed += 1;

                Some(ident)
            },
            @else { err!() } => ExpectedKind::ImportRenameAs,
        ));

        // And finaly, we're expecting a trailing semicolon
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            @else { err!() } => ExpectedKind::ImportTrailingSemi,
        ));

        Ok(ImportStmt {
            src: Source::slice_span(file, &tokens[..consumed]),
            source,
            version,
            rename,
        })
    }
}

impl UseStmt {
    /// Consumes a `use` statment as a prefix of the given tokens
    ///
    /// The arguments to this function follow the same semantics as [`FnDecl::consume`]. For an
    /// in-depth explanation, please see the documentation there.
    ///
    /// [`FnDecl::consume`]: ../fndecl/struct.FnDecl.html#method.consume
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
        vis: Option<Vis>,
    ) -> Result<UseStmt, ItemParseErr> {
        // Use statements are given by the following BNF:
        //   UseStmt = Vis "use" UsePath ";"
        // where `ident_idx` gives the index in `tokens` at which the `UsePath` starts.
        //
        // Because `UsePath` is (partially) defined recursively, it must have its own parser, which
        // is why this function ends up being so simple.

        let mut consumed = ident_idx;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let path = UsePath::consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(ItemParseErr::add(consumed))?;
        consumed += path.consumed();

        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Semi) => consumed += 1,
            @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::UseTrailingSemi,
        ));

        Ok(UseStmt {
            src: Source::slice_span(file, &tokens[..consumed]),
            vis,
            path,
        })
    }
}

impl UsePath {
    /// Consumes a `UsePath` as a prefix of the given tokens
    ///
    /// Please note that, unlike many other parsing functions, this always returns the number of
    /// tokens consumed. This does not necessarily reflect positions where it may be sensible to
    /// resume parsing, and so should be handled with intention by the caller.
    ///
    /// In practice, [`UseStmt::consume`] just converts this to an [`ItemParseErr`], which will be
    /// appropriately recovered from, and [`MultiUse::parse_inner`] makes no attempt to recover.
    ///
    /// [`UseStmt::consume`]: enum.UseStmt.html#method.consume
    /// [`ItemParseErr`]: ../struct.ItemParseErr.html
    /// [`MultiUse::parse_inner`]: struct.MultiUse.html#method.parse_inner
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<UsePath, Option<usize>> {
        let mut consumed = 0;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let path = expect!((
            Ok(fst),
            TokenKind::Ident(_) => {
                UsePath::consume_path(file, tokens, ends_early, containing_token, errors)?
            },
            // Otherwise, we'll handle the case of
            TokenKind::Keyword(k) if UseKind::try_from(*k).is_ok() => {
                return SingleUse::consume(file, tokens, ends_early, containing_token, errors)
                    .map(UsePath::Single);
            },
            @else(return None) => ExpectedKind::UsePath,
        ));

        consumed += path.consumed();

        // If we get here, we're expecting either a glob or a multi-use
        //
        // We'll do some prelimiary special-case error handling before we get into things
        if consumed >= tokens.len() {
            if !ends_early {
                errors.push(Error::MissingUseKind {
                    path: Source::slice_span(file, &tokens[..consumed]),
                });
            }

            return Err(Some(consumed));
        }

        expect!((
            Ok(fst),
            // Only if we find a dot afterwards to we get a glob or multi-use
            TokenKind::Punctuation(Punc::Dot) => {
                consumed += 1;

                // After a dot, we know there isn't an identifier (because otherwise
                // `consume_path()` would have taken that), so we're expecting a curly braces (for
                // multi-use) or a star (for glob use).
                expect!((
                    Ok(snd),
                    TokenKind::Punctuation(Punc::Star) => {
                        consumed += 1;
                        Ok(UsePath::Glob(GlobUse {
                            src: Source::slice_span(file, &tokens[..consumed]),
                            root: path,
                            star_token: snd.span(file),
                        }))
                    },
                    TokenKind::Tree { delim: Delim::Curlies, inner, .. } => {
                        let (children, poisoned) = MultiUse::parse_inner(file, snd, inner, errors);
                        consumed += 1;
                        Ok(UsePath::Multi(MultiUse {
                            src: Source::slice_span(file, &tokens[..consumed]),
                            root: path,
                            children,
                            poisoned,
                        }))
                    },

                    // And some error handling:
                    @err TokenKind::Tree { delim: Delim::Parens, .. } => {
                        Error::UsePathDotParens { path: Source::slice_span(file, &tokens[..consumed]), parens: Source::token(file, snd) }
                    },
                    @else(return Some) => ExpectedKind::UsePathPostDot,
                ))
            },
            // The rest of this `expect` call is for handling errors of various kinds

            @err TokenKind::Punctuation(Punc::Semi)
            | TokenKind::Punctuation(Punc::Comma) => {
                Error::MissingUseKind { path: Source::slice_span(file, &tokens[..consumed] )}
            },
            @err TokenKind::Punctuation(Punc::Star) => {
                Error::MissingGlobUseDot { star_token: Source::token(file, fst) }
            },
            @err TokenKind::Tree { delim: Delim::Curlies, .. } => {
                Error::MissingMultiUseDot { curly_token: Source::token(file, fst) }
            },
            @err _ => {
                Error::MissingUseKind { path: Source::slice_span(file, &tokens[..consumed] )}
            },
            // We can safely not return an error here because we've covered all of the variants of
            // Some(Ok(_)) and None - the latter is taken care of before this expansion of expect!
            @else(return Some) => @no_error,
        ))
    }

    /// A helper function to consume a [`Path`], under a different set of base assumptions than the
    /// standard [`Path::consume`]
    ///
    /// Unlike the standard function, this function does not expect trailing path segments after
    /// finding a dot token unless it is followed by an identifier.
    ///
    /// [`Path`]: ../../expr/struct.Path.html
    /// [`Path::consume`]: ../../expr/struct.Path.html#method.consume
    fn consume_path(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Path, Option<usize>> {
        let base =
            PathComponent::consume(file, tokens, None, ends_early, containing_token, errors)?;
        let mut consumed = base.consumed();
        let mut components = vec![base];

        while let Some(TokenKind::Punctuation(Punc::Dot)) = kind!(tokens)(consumed) {
            consumed += 1;

            let next = PathComponent::consume(
                file,
                &tokens[consumed..],
                Some(&tokens[..consumed]),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(|c| c.unwrap_or(0) + consumed)?;
            consumed += next.consumed();

            components.push(next);
        }

        Ok(Path {
            src: Source::slice_span(file, &tokens[..consumed]),
            components,
        })
    }
}

impl MultiUse {
    /// Parses the inner portion of a `MultiUse`, returning the list of paths and whether that list
    /// was *directly* poisoned by any failures.
    fn parse_inner(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        errors: &mut Vec<Error>,
    ) -> (Vec<UsePath>, bool) {
        let mut consumed = 0;
        let mut paths = Vec::new();
        let mut poisoned = false;

        let ends_early = false;
        make_expect!(file, inner, consumed, ends_early, Some(src), errors);

        macro_rules! stop {
            () => {{
                poisoned = true;
                break;
            }};
        }

        while consumed < inner.len() {
            let path_res =
                UsePath::consume(file, &inner[consumed..], ends_early, Some(src), errors);
            match path_res {
                Ok(p) => {
                    consumed += p.consumed();
                    paths.push(p);
                }
                Err(_) => stop!(),
            }

            // After each path, we're expecting a comma
            if consumed < inner.len() {
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    @else { stop!() } => ExpectedKind::MultiUseCommaDelim,
                ));
            }
        }

        (paths, poisoned)
    }
}

impl SingleUse {
    /// Consumes a `SingleUse` variant of [`UseKind`] as a prefix of the given tokens
    ///
    /// This function assumes that the first of the provided tokens satisfies
    /// [`UseKind::can_parse`]
    ///
    /// [`UseKind`]: enum.UseKind.html
    /// [`UseKind::can_parse`]: enum.UseKind.html#method.can_parse
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<SingleUse, Option<usize>> {
        let (fst_token, kwd) = assert_token!(
            tokens.first() => "keyword token",
            Ok(t) && TokenKind::Keyword(k) => (t, *k),
        );

        let kind = UseKind::try_from(kwd).unwrap();
        let mut consumed = 1;
        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let path = Path::consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;
        consumed += path.consumed();

        // [ "as" Ident ]
        let mut use_as = None;
        if let Some(TokenKind::Keyword(Kwd::As)) = kind!(tokens)(consumed) {
            consumed += 1;

            let ident = expect!((
                Ok(src),
                TokenKind::Ident(name) => Ident { src: src.span(file), name: (*name).into() },
                @else(return Some) => ExpectedKind::UsePathSingleAsIdent,
            ));

            use_as = Some(ident);
            consumed += 1;
        }

        Ok(SingleUse {
            src: Source::slice_span(file, &tokens[..consumed]),
            kind_src: fst_token.span(file),
            kind,
            path,
            use_as,
        })
    }
}

impl TryFrom<Kwd> for UseKind {
    type Error = ();

    fn try_from(kwd: Kwd) -> Result<UseKind, ()> {
        macro_rules! kwds {
            ($($ks:ident),+$(,)?) => {{
                match kwd {
                    $(Kwd::$ks => Ok(UseKind::$ks),)+
                    _ => Err(()),
                }
            }}
        }

        kwds! { Fn, Macro, Type, Trait, Const, Static, Mod }
    }
}
