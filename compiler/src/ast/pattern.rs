//! Pattern parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;
use crate::files::FileInfo;
use crate::files::Span;

/// A pattern, used for destructuring and pattern matching
///
/// Individual details are given in the documentation for the variant types.
#[derive(Debug, Clone, Consumed)]
pub enum Pattern {
    Named(NamedPattern),
    Struct(StructPattern),
    Tuple(TuplePattern),
    Array(ArrayPattern),
    Assign(AssignPattern),
    Ref(RefPattern),
    Literal(Literal),
}

/// A named pattern - either empty, a named tuple, or a named struct
///
/// The BNF is defined as:
/// ```text
/// NamedPattern = PatternPath [ StructPattern | TuplePattern ] .
/// ```
///
/// The name is given by a [`PatternPath`], which is similar to standard [`Path`]s but with a
/// couple key distinctions that are elaborated upon further in the documentation. The variant of
/// the right-hand-side is given by [`NamedPatternKind`], which expresses the three variants that
/// may follow the name.
///
/// Finally, please note that there is a special case of `NamedPattern`s when they are exactly a
/// single identifier - here, they may *also* be used to bind a local variable, depending on
/// whether that identifier is in scope as a type or not.
///
/// [`PatternPath`]: enum.PatternPath.html
/// [`Path`]: ../expr/struct.Path.html
/// [`NamedPatternKind`]: enum.NamedPatternKind.html
#[derive(Debug, Clone, Consumed)]
pub struct NamedPattern {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub path: PatternPath,
    pub kind: Option<NamedPatternKind>,
}

/// A path used in [`NamedPattern`]s
///
/// This type is distinct from the typical [`Path`] in two key ways: (1) It does not allow generics
/// arguments (those should be implied otherwise), and (2) it may also be represented in a
/// "relative" fashion for `enum` variants. The BNF definition makes this more clear:
/// ```text
/// PatternPath = "." Ident
///             | Ident { "." Ident } .
/// ```
///
/// The first variant here is the "relative" path - any `enum` variant may be matched by a pattern
/// containing its name in this fashion.
///
/// As mentioned in the documentation for [`NamedPattern`], if the path is exactly a single
/// identifier (using the second variant above), it may instead be used to bind a local variable.
///
/// [`NamedPattern`]: struct.NamedPattern.html
#[derive(Debug, Clone, Consumed)]
pub enum PatternPath {
    Relative(RelativePatternPath),
    Absolute(AbsolutePatternPath),
}

/// "Relative" pattern paths - a helper type for [`PatternPath`](#enum.PatternPath.html)
#[derive(Debug, Clone, Consumed)]
pub struct RelativePatternPath {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(2)] // +1 for the leading "."
    pub name: Ident,
}

/// "Absolute" pattern paths - a helper type for [`PatternPath`](#enum.PatternPath.html)
#[derive(Debug, Clone, Consumed)]
pub struct AbsolutePatternPath {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(components.len() * 2 - 1)]
    components: Vec<Ident>,
}

/// A helper type to express the right-hand-side of [`NamedPattern`]s
///
/// [`NamedPattern`]: struct.NamedPattern.html
#[derive(Debug, Clone, Consumed)]
pub enum NamedPatternKind {
    Struct(StructPattern),
    Tuple(TuplePattern),
}

/// A struct pattern, which can be used to destructure or match named and anonymous structs
///
/// Struct patterns are defined by the following BNF:
/// ```text
/// StructPattern = "{" [ FieldPattern [ "," FieldPattern ] [ "," ] ] [ ".." ] "}" .
/// ```
/// Essentially, there may be any number of comma-separated fields, optionally followed by two dots
/// (`..`) to indicate that there are other fields in the struct not represented by the pattern.
/// Fields are represented by individual [`FieldPattern`]s.
///
/// Please note that one element not conveyed in the BNF definition is that trailing dots are
/// syntactically invalid without a preceeding comma if there are fields named here.
///
/// [`FieldPattern`]: struct.FieldPattern.html
#[derive(Debug, Clone, Consumed)]
pub struct StructPattern {
    #[consumed(1)]
    pub(super) src: Span,

    #[consumed(@ignore)]
    pub fields: Vec<FieldPattern>,

    /// A marker for whether the pattern includes trailing dots. If it does, this token will give
    /// the souce for them, and won't if there aren't any.
    #[consumed(@ignore)]
    pub has_dots: Option<Span>,

    /// Whether there were significant in parsing as to prevent some of the above elements from
    /// being properly instantiated.
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A single field pattern; a helper type for [`StructPattern`]
///
/// Field patterns are defined by the following (simple) BNF:
/// ```text
/// FieldPattern = Ident [ ":" Pattern ] .
/// ```
/// Omitting the trailing pattern is sytax sugar for `<Ident>: <Ident>`, where the identifier is
/// repeated - i.e. binding a local variable equal to the name of the field. This mirrors the
/// abbreviation available in struct instantiation.
///
/// [`StructPattern`]: struct.StructPattern.html
#[derive(Debug, Clone, Consumed)]
pub struct FieldPattern {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub name: Ident,

    // consumed + 1 to account for the additional colon token
    #[consumed(binding.consumed() + 1)]
    pub binding: Option<Pattern>,
}

/// A tuple pattern, which can be used to destructure or match named and anonymous tuples
///
/// Tuple patterns are defined by the following BNF:
/// ```text
/// TuplePattern = "(" [ Pattern { "," Pattern } [ "," ] ] ")" .
/// ```
/// Tuple patterns consist of a list of elements, which are required to have the same arity as the
/// tuple they are matching against.
#[derive(Debug, Clone, Consumed)]
pub struct TuplePattern {
    #[consumed(1)]
    pub(super) src: Span,

    #[consumed(@ignore)]
    pub elements: Vec<Pattern>,
    /// Whether there were errors in parsing so significant that we weren't able to provide a value
    /// in `elements` for each `Pattern` we parsed.
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// An array pattern, which can be used to destructure or match arrays and (by extension) slices
///
/// Array patterns are defined by the following BNF definitions:
/// ```text
/// ArrayPattern = "[" [ ElementPattern { "," ElementPattern } [ "," ] ] "]" .
/// ElementPattern = ".." | Pattern .
/// ```
/// While the definition indicates that dots (`..`) may be given anywhere in the list, it is
/// important to note that only a small class of options here are semantically valid, primarily for
/// practical reasons (e.g. not constant-time to match).
#[derive(Debug, Clone, Consumed)]
pub struct ArrayPattern {
    #[consumed(1)]
    pub(super) src: Span,

    #[consumed(@ignore)]
    pub elements: Vec<ElementPattern>,

    /// Whether there were significant in parsing as to prevent some of the above elements from
    /// being properly instantiated.
    #[consumed(@ignore)]
    pub poisoned: bool,
}

/// A helper type for [`ArrayPattern`](#struct.ArrayPattern.html)s
#[derive(Debug, Clone, Consumed)]
pub enum ElementPattern {
    #[consumed(1)]
    Dots(Span),
    Pattern(Pattern),
}

/// Assignment to an expression on a successful match or destructuring
///
/// These are allowed so that value may be bound within the outer scope of a match. This is only
/// done on success.
///
/// The BNF for assignment patterns gives the following definition:
/// ```text
/// AssignPattern = "assign" Expr .
/// ```
/// An additional quirk is that `x = foo` is equivalent to `let assign x = foo` for any lvalue `x`
/// and expression `foo`.
#[derive(Debug, Clone, Consumed)]
pub struct AssignPattern {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(assignee.consumed() + 1)]
    pub assignee: Box<Expr>,
}

/// Reference patterns that allow moving out behind references within matches
///
/// These are allowed so that patterns may convert references to the owned version behin them -
/// essentially helpful syntax sugar.
///
/// The BNF definition for reference patterns is:
/// ```text
/// RefPattern = "&" Pattern .
/// ```
#[derive(Debug, Clone, Consumed)]
pub struct RefPattern {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(pat.consumed() + 1)]
    pub pat: Box<Pattern>,
}

type ConsumeFn<T> = fn(
    &FileInfo,
    TokenSlice,
    PatternContext,
    bool,
    Option<&Token>,
    &mut Vec<Error>,
) -> Result<T, Option<usize>>;

impl Pattern {
    /// Consumes a single pattern as a prefix of the given tokens
    pub fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: PatternContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Pattern, Option<usize>> {
        make_expect!(file, tokens, 0, ends_early, containing_token, errors);
        expect!((
            Ok(fst_token),
            TokenKind::Ident(_) => {
                NamedPattern::consume_absolute(file, tokens, ctx, ends_early, containing_token, errors)
                    .map(Pattern::Named)
            },
            TokenKind::Punctuation(Punc::Dot) => {
                NamedPattern::consume_relative(file, tokens, ctx, ends_early, containing_token, errors)
                    .map(Pattern::Named)
            },
            TokenKind::Tree { delim, inner, .. } => {
                let res = match delim {
                    Delim::Curlies => StructPattern::parse(file, fst_token, inner, ctx, errors).map(Pattern::Struct),
                    Delim::Parens => TuplePattern::parse(file, fst_token, inner, ctx, errors).map(Pattern::Tuple),
                    Delim::Squares => ArrayPattern::parse(file, fst_token, inner, ctx, errors).map(Pattern::Array),
                };

                res.map_err(|()| Some(1))
            },
            TokenKind::Keyword(Kwd::Assign) => {
                let res = Expr::consume(
                    file,
                    &tokens[1..],
                    ExprDelim::Comma,
                    Restrictions::default(),
                    ends_early,
                    containing_token,
                    errors
                );

                match res {
                    Err(None) => Err(None),
                    Err(Some(c)) => Err(Some(c + 1)),
                    Ok(expr) => {
                        let src = Source::slice_span(file, &tokens[..1+expr.consumed()]);
                        Ok(Pattern::Assign(AssignPattern { src, assignee: Box::new(expr) }))
                    }
                }
            },
            TokenKind::Punctuation(Punc::And) => {
                match Pattern::consume(file, &tokens[1..], ctx, ends_early, containing_token, errors) {
                    Err(None) => Err(None),
                    Err(Some(c)) => Err(Some(c + 1)),
                    Ok(pat) => {
                        let src = Source::slice_span(file, &tokens[..1+pat.consumed()]);
                        Ok(Pattern::Ref(RefPattern {
                            src,
                            pat: Box::new(pat),
                        }))
                    }
                }
            },
            TokenKind::Literal(_,_) => Literal::consume(file, tokens)
                .map(Pattern::Literal),
            @else(return None) => ExpectedKind::Pattern(ctx),
        ))
    }

    /// A helper function to extract the common parts of [`TuplePattern::parse`] and
    /// [`ArrayPattern::parse`]
    ///
    /// On success, this function returns the list of parsed elements, alongside whether that list
    /// was poisoned.
    ///
    /// For more information, refer to either of the above functions.
    ///
    /// [`TuplePattern::parse`]: struct.TuplePattern.html#method.parse
    /// [`ArrayPattern::parse`]: struct.ArrayPattern.html#method.parse
    fn consume_delimited<T: Consumed>(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        ctx: PatternContext,
        consume_fn: ConsumeFn<T>,
        no_elem_err: fn(PatternContext) -> ExpectedKind,
        delim_err: fn(PatternContext, Source) -> ExpectedKind,
        errors: &mut Vec<Error>,
    ) -> Result<(Vec<T>, bool), ()> {
        let mut consumed = 0;
        let ends_early = false;
        let mut poisoned = false;
        let mut elements = Vec::new();

        loop {
            match inner.get(consumed) {
                // Running out of tokens is actually fine ~ we'll break out of the loop to do a
                // normal return.
                None => {
                    if ends_early {
                        poisoned = true;
                    }

                    break;
                }

                // Some tokenizer errors are additionally parsing errors. However, because any token
                // tree can represent a pattern, any error due to an unclosed delimiter is not
                // necessarily a double-error.
                Some(Err(token_tree::Error::UnclosedDelim(_, _, _))) => {
                    poisoned = true;
                    break;
                }
                // The other tokenizer errors cannot represent a valid pattern, so we produce a
                // secondary error.
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: no_elem_err(ctx),
                        found: Source::err(file, e),
                    });

                    poisoned = true;
                    break;
                }

                Some(Ok(_)) => {
                    let res =
                        consume_fn(file, &inner[consumed..], ctx, ends_early, Some(src), errors);

                    match res {
                        Err(None) => {
                            poisoned = true;
                            break;
                        }
                        Err(Some(c)) => {
                            poisoned = true;
                            consumed += c;
                        }
                        Ok(elem) => {
                            consumed += elem.consumed();
                            elements.push(elem);
                        }
                    }
                }
            }

            // Between fields, we'll expect trailing commas
            match inner.get(consumed) {
                // If we ran out of tokens, it's because there's no more elements - that's exactly
                // what's expected, so we're good to just exit the loop and return.
                None => {
                    if ends_early {
                        poisoned = true;
                    }
                    break;
                }
                // If there was a tokenizer error, we'll simply exit without producing any more
                // errors here.
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
                            kind: delim_err(ctx, Source::token(file, src)),
                            found: Source::token(file, t),
                        });

                        poisoned = true;
                        break;
                    }
                },
            }
        }

        Ok((elements, poisoned))
    }
}

impl NamedPattern {
    /// Consumes an "absolute" named pattern
    ///
    /// Absolute named patterns are of the following form:
    /// ```text
    /// Ident { "." Ident } [ StructPattern | TuplePattern ]
    /// ```
    ///
    /// This function additionally expects the first token it receives to be an identifier, and will
    /// panic if this is not the case.
    fn consume_absolute(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: PatternContext,
        _ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<NamedPattern, Option<usize>> {
        // This function comes in two pieces: we first consume the leading path, and then we parse
        // the trailing `[ StructPattern | TuplePattern ]`. We're able to assume that the first
        // token is an identifier because of the guarantees of this function, so we can simplify
        // the inner loop a little bit.

        let fst_ident = assert_token!(
            tokens.first() => "identifier",
            Ok(t) && TokenKind::Ident(name) => Ident { src: t.span(file), name: (*name).into() },
        );

        let mut consumed = 1;
        let mut components = vec![fst_ident];

        // After consuming the first identifier in the path, we'll keep going until we find
        loop {
            // We always enter the loop body having just consumed an identifier, so we'll (loosely)
            // expect a dot (`.`) token to separate them. If we don't find one, we'll simply break
            // out of the loop because the is over.

            match tokens.get(consumed) {
                // We'll leave ambiguous failure cases for other parsers to handle
                None | Some(Err(_)) => break,
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Dot) => consumed += 1,
                    _ => break,
                },
            }

            // After finding `.`, we'll expect an identifier
            let id = Ident::parse(
                file,
                tokens.get(consumed),
                IdentContext::PatternPath(ctx, Source::slice_span(file, &tokens[..consumed])),
                end_source!(file, containing_token),
                errors,
            )
            .map_err(|()| Some(consumed))?;

            components.push(id);
            consumed += 1;
        }

        let path = PatternPath::Absolute(AbsolutePatternPath {
            src: Source::slice_span(file, &tokens[..consumed]),
            components,
        });

        // After parsing the absolute path, we then just parse the trailing struct or tuple
        // pattern, if it's there.
        let kind = NamedPatternKind::try_parse(file, tokens.get(consumed), ctx, errors)
            .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += kind.consumed();

        Ok(NamedPattern {
            src: Source::slice_span(file, &tokens[..consumed]),
            path,
            kind,
        })
    }

    /// Consumes a "relative" named pattern
    ///
    /// Relative named patterns are of the following form:
    /// ```text
    /// "." Ident [ StructPattern | TuplePattern ]
    /// ```
    ///
    /// This function additionally expects the first token it receives to be the initial "dot"
    /// token, and will panic if this is not the case.
    fn consume_relative(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: PatternContext,
        _ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<NamedPattern, Option<usize>> {
        assert_token!(
            tokens.first() => "dot (`.`)",
            Ok(t) && TokenKind::Punctuation(Punc::Dot) => (),
        );

        let mut consumed = 1;

        let name = Ident::parse(
            file,
            tokens.get(consumed),
            IdentContext::PatternPath(ctx, Source::slice_span(file, &tokens[..consumed])),
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| None)?;
        consumed += 1;

        let path = PatternPath::Relative(RelativePatternPath {
            src: Source::slice_span(file, &tokens[..consumed]),
            name,
        });

        let kind = NamedPatternKind::try_parse(file, tokens.get(consumed), ctx, errors)
            .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += kind.consumed();

        Ok(NamedPattern {
            src: Source::slice_span(file, &tokens[..consumed]),
            path,
            kind,
        })
    }
}

impl NamedPatternKind {
    fn try_parse(
        file: &FileInfo,
        token: Option<&Result<Token, token_tree::Error>>,
        ctx: PatternContext,
        errors: &mut Vec<Error>,
    ) -> Result<Option<NamedPatternKind>, Option<usize>> {
        // We'll either expect a struct or tuple pattern here - if the next token consists either
        // of a curly-brace or parentheses enclosed token tree, we'll attempt to parse it.
        // Otherwise, we'll simply return `Ok(None)` because we didn't find the right-hand-side of
        // a named pattern and they're optional.

        match token {
            // Running out of tokens here is fine; we can just return `Ok(None)`
            None => Ok(None),
            // Certain tokenizer errors might constitute double-errors. Because curly braces and
            // parentheses *are* valid here, we'll intentionally prevent the caller from emitting
            // another error.
            Some(Err(token_tree::Error::UnclosedDelim(d, _, _))) => match d {
                Delim::Curlies | Delim::Parens => Err(None),
                // Square brackets will be left for the caller
                Delim::Squares => Ok(None),
            },
            // We'll leave other errors for the caller to discover later
            Some(Err(_)) => Ok(None),

            // Otherwise, we'll only parse a tuple or struct pattern, if they're available. If they
            // aren't we'll simply return `Ok(None)`
            Some(Ok(t)) => match &t.kind {
                TokenKind::Tree {
                    delim: Delim::Parens,
                    inner,
                    ..
                } => TuplePattern::parse(file, t, inner, ctx, errors)
                    .map(NamedPatternKind::Tuple)
                    .map(Some)
                    .map_err(|()| Some(1)),
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => StructPattern::parse(file, t, inner, ctx, errors)
                    .map(NamedPatternKind::Struct)
                    .map(Some)
                    .map_err(|()| Some(1)),
                _ => Ok(None),
            },
        }
    }
}

impl StructPattern {
    /// Parses a struct pattern from the given curly-brace token and its inner tokens
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        ctx: PatternContext,
        errors: &mut Vec<Error>,
    ) -> Result<StructPattern, ()> {
        // This function has a fairly simple structure - we loop over the tokens (where the
        // majority of visual space is taken up) and parse fields individually. This is broken into
        // two match statements (both on `inner.get(consumed)`)
        //
        // Because struct patterns are allowed to have trailing dots, but they must be the last
        // token in the list, the loop evaluates to the source for trailing dots, if they are
        // there.
        let mut consumed = 0;
        let ends_early = false;
        let mut poisoned = false;
        let mut fields = Vec::new();

        let has_dots = loop {
            match inner.get(consumed) {
                // Running out of tokens is actually fine ~ we'll break out of the loop to do a
                // normal return.
                None => {
                    if ends_early {
                        poisoned = true;
                    }

                    break None;
                }

                // All tokenizer errors are additionally parsing errors here because we're
                // explicitly expecting an identifier.
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::StructPatternField(ctx),
                        found: Source::err(file, e),
                    });

                    poisoned = true;
                    break None;
                }

                // At this point, we've either just started the inside of the struct pattern or we
                // just parsed the comma after a struct element. We're either expecting the next
                // field (which must start with an identifier) or dots (`..`).
                Some(Ok(t)) => match &t.kind {
                    // An identifier indicates the field
                    TokenKind::Ident(_) => {
                        let res = FieldPattern::consume(
                            file,
                            &inner[consumed..],
                            ctx,
                            ends_early,
                            Some(src),
                            errors,
                        );

                        match res {
                            Err(None) => {
                                poisoned = true;
                                break None;
                            }
                            Err(Some(c)) => {
                                poisoned = true;
                                consumed += c;
                            }
                            Ok(field) => {
                                consumed += field.consumed();
                                fields.push(field);
                            }
                        }
                    }

                    // If we find "..", we're expecting to be done with the set of tokens. If we
                    // still find more, we'll produce an error, indicate that this pattern was
                    // poisoned, and continue.
                    TokenKind::Punctuation(Punc::DotDot) => {
                        consumed += 1;
                        match inner.get(consumed) {
                            None => break Some(t.span(file)),
                            Some(res) => {
                                errors.push(Error::Expected {
                                    kind: ExpectedKind::StructPatternEnd(ctx),
                                    found: Source::from(file, res),
                                });

                                poisoned = true;
                                break None;
                            }
                        }
                    }

                    // Anything else isn't expected -- we'll return. We'll avoid generating errors
                    // if we've marked the struct pattern as poisoned, because it might be that the
                    // parsing error was due to some other, already emitted, error.
                    _ => {
                        if !poisoned {
                            errors.push(Error::Expected {
                                kind: ExpectedKind::StructPatternField(ctx),
                                found: Source::token(file, t),
                            });
                        }

                        poisoned = true;
                        break None;
                    }
                },
            }

            // Between fields, we'll expect trailing commas
            match inner.get(consumed) {
                // If we ran out of tokens, it's because there's no more fields - that's exactly
                // what's expected, so we're good to just exit the loop and return.
                None => {
                    if ends_early {
                        poisoned = true;
                    }
                    break None;
                }
                // If there was a tokenizer error, we'll simply exit without producing any more
                // errors here.
                Some(Err(_)) => {
                    poisoned = true;
                    break None;
                }

                // Otherwise, we'll check that we *do* have a trailing comma
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    // If we didn't have one, we'll produce an error
                    _ => {
                        errors.push(Error::Expected {
                            kind: ExpectedKind::StructPatternDelim(ctx, Source::token(file, src)),
                            found: Source::token(file, t),
                        });

                        poisoned = true;
                        break None;
                    }
                },
            }
        };

        Ok(StructPattern {
            src: src.span(file),
            fields,
            has_dots,
            poisoned,
        })
    }
}

impl FieldPattern {
    /// Consumes a single struct field pattern as a prefix of the given tokens
    ///
    /// This function expects that the first token in the list will be an identifier, and will
    /// panic if this condition is not met.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: PatternContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<FieldPattern, Option<usize>> {
        let name = assert_token!(
            tokens.first() => "identifier",
            Ok(t) && TokenKind::Ident(name) => Ident { src: t.span(file), name: (*name).into() },
        );

        macro_rules! only_name {
            () => {{
                Ok(FieldPattern {
                    src: Source::slice_span(file, &tokens[..1]),
                    name,
                    binding: None,
                })
            }};
        }

        // We'll check the second token to see which format this field is being given as - either
        // as the form `Ident ":" Pattern` or simply as `Ident`. If the second token is anything
        // other than a colon, we'll just return the field as the single identifier.
        match tokens.get(1) {
            None | Some(Err(_)) => return only_name!(),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Colon) => (),
                _ => return only_name!(),
            },
        }

        // At this point, we are expecting a pattern to bind for the field, so we'll do that now
        let pat_res = Pattern::consume(
            file,
            &tokens[2..],
            ctx,
            ends_early,
            containing_token,
            errors,
        );
        match pat_res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(c + 2)),
            Ok(pat) => Ok(FieldPattern {
                src: Source::slice_span(file, &tokens[..pat.consumed() + 2]),
                name,
                binding: Some(pat),
            }),
        }
    }
}

impl TuplePattern {
    /// Parses a tuple pattern from the given parentheses-enclosed block and its inner tokens
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        ctx: PatternContext,
        errors: &mut Vec<Error>,
    ) -> Result<TuplePattern, ()> {
        let (elements, poisoned) = Pattern::consume_delimited(
            file,
            src,
            inner,
            ctx,
            Pattern::consume,
            ExpectedKind::TuplePatternElement,
            ExpectedKind::TuplePatternDelim,
            errors,
        )?;

        Ok(TuplePattern {
            src: src.span(file),
            elements,
            poisoned,
        })
    }
}

impl ArrayPattern {
    fn parse(
        file: &FileInfo,
        src: &Token,
        inner: TokenSlice,
        ctx: PatternContext,
        errors: &mut Vec<Error>,
    ) -> Result<ArrayPattern, ()> {
        let (elements, poisoned) = Pattern::consume_delimited(
            file,
            src,
            inner,
            ctx,
            ElementPattern::consume,
            ExpectedKind::ArrayPatternElement,
            ExpectedKind::ArrayPatternDelim,
            errors,
        )?;

        Ok(ArrayPattern {
            src: src.span(file),
            elements,
            poisoned,
        })
    }
}

impl ElementPattern {
    /// Consumes a single array element pattern; a helper function for [`ArrayPattern::parse`]
    ///
    /// [`ArrayPattern::parse`]: struct.ArrayPattern.html#method.parse
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: PatternContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<ElementPattern, Option<usize>> {
        match tokens.first() {
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ArrayPatternElement(ctx),
                    found: end_source!(file, containing_token),
                });

                Err(None)
            }
            // Because any delimiter can be a valid pattern, we won't emit a second error here
            Some(Err(token_tree::Error::UnclosedDelim(_, _, _))) => return Err(None),
            // Otherwise, this is *still* an error, so we'll generate another one
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ArrayPatternElement(ctx),
                    found: Source::err(file, e),
                });

                Err(None)
            }

            // If we do find a token, we'll give a special case for dots (`..`), else we'll try a
            // regular pattern.
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::DotDot) => Ok(ElementPattern::Dots(t.span(file))),
                _ => Pattern::consume(file, tokens, ctx, ends_early, containing_token, errors)
                    .map(ElementPattern::Pattern),
            },
        }
    }
}
