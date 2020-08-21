//! Pattern parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

/// A pattern, used for destructuring and pattern matching
///
/// Individual details are given in the documentation for the variant types.
#[derive(Debug, Clone)]
pub enum Pattern<'a> {
    Named(NamedPattern<'a>),
    Struct(StructPattern<'a>),
    Tuple(TuplePattern<'a>),
    Array(ArrayPattern<'a>),
    Assign(AssignPattern<'a>),
    Ref(RefPattern<'a>),
    Literal(Literal<'a>),
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
#[derive(Debug, Clone)]
pub struct NamedPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    pub path: PatternPath<'a>,
    pub kind: Option<NamedPatternKind<'a>>,
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
#[derive(Debug, Clone)]
pub enum PatternPath<'a> {
    Relative(RelativePatternPath<'a>),
    Absolute(AbsolutePatternPath<'a>),
}

/// "Relative" pattern paths - a helper type for [`PatternPath`](#enum.PatternPath.html)
#[derive(Debug, Clone)]
pub struct RelativePatternPath<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
}

/// "Absolute" pattern paths - a helper type for [`PatternPath`](#enum.PatternPath.html)
#[derive(Debug, Clone)]
pub struct AbsolutePatternPath<'a> {
    pub(super) src: TokenSlice<'a>,
    components: Vec<Ident<'a>>,
}

/// A helper type to express the right-hand-side of [`NamedPattern`]s
///
/// [`NamedPattern`]: struct.NamedPattern.html
#[derive(Debug, Clone)]
pub enum NamedPatternKind<'a> {
    Struct(StructPattern<'a>),
    Tuple(TuplePattern<'a>),
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
#[derive(Debug, Clone)]
pub struct StructPattern<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<FieldPattern<'a>>,
    /// A marker for whether the pattern includes trailing dots. If it does, this token will give
    /// the souce for them, and won't if there aren't any.
    pub has_dots: Option<&'a Token<'a>>,
    /// Whether there were significant in parsing as to prevent some of the above elements from
    /// being properly instantiated.
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
#[derive(Debug, Clone)]
pub struct FieldPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub binding: Option<Pattern<'a>>,
}

/// A tuple pattern, which can be used to destructure or match named and anonymous tuples
///
/// Tuple patterns are defined by the following BNF:
/// ```text
/// TuplePattern = "(" [ Pattern { "," Pattern } [ "," ] ] ")" .
/// ```
/// Tuple patterns consist of a list of elements, which are required to have the same arity as the
/// tuple they are matching against.
#[derive(Debug, Clone)]
pub struct TuplePattern<'a> {
    pub(super) src: &'a Token<'a>,
    pub elements: Vec<Pattern<'a>>,
    /// Whether there were errors in parsing so significant that we weren't able to provide a value
    /// in `elements` for each `Pattern` we parsed.
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
#[derive(Debug, Clone)]
pub struct ArrayPattern<'a> {
    pub(super) src: &'a Token<'a>,
    pub elements: Vec<ElementPattern<'a>>,

    /// Whether there were significant in parsing as to prevent some of the above elements from
    /// being properly instantiated.
    pub poisoned: bool,
}

/// A helper type for [`ArrayPattern`](#struct.ArrayPattern.html)s
#[derive(Debug, Clone)]
pub enum ElementPattern<'a> {
    Dots(&'a Token<'a>),
    Pattern(Pattern<'a>),
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
#[derive(Debug, Clone)]
pub struct AssignPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    pub assignee: Box<Expr<'a>>,
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
#[derive(Debug, Clone)]
pub struct RefPattern<'a> {
    pub(super) src: TokenSlice<'a>,
    pub pat: Box<Pattern<'a>>,
}

type ConsumeFn<'a, T> = fn(
    TokenSlice<'a>,
    PatternContext<'a>,
    bool,
    Option<&'a Token<'a>>,
    &mut Vec<Error<'a>>,
) -> Result<T, Option<usize>>;

impl<'a> Pattern<'a> {
    /// Consumes a single pattern as a prefix of the given tokens
    pub fn consume(
        tokens: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Pattern<'a>, Option<usize>> {
        make_expect!(tokens, 0, ends_early, containing_token, errors);
        expect!((
            TokenKind::Ident(_) => {
                NamedPattern::consume_absolute(tokens, ctx, ends_early, containing_token, errors)
                    .map(Pattern::Named)
            },
            TokenKind::Punctuation(Punc::Dot) => {
                NamedPattern::consume_relative(tokens, ctx, ends_early, containing_token, errors)
                    .map(Pattern::Named)
            },
            TokenKind::Tree { delim, inner, .. } => {
                let src = tokens[0].as_ref().unwrap();
                let res = match delim {
                    Delim::Curlies => StructPattern::parse(src, inner, ctx, errors).map(Pattern::Struct),
                    Delim::Parens => TuplePattern::parse(src, inner, ctx, errors).map(Pattern::Tuple),
                    Delim::Squares => ArrayPattern::parse(src, inner, ctx, errors).map(Pattern::Array),
                };

                res.map_err(|()| Some(1))
            },
            TokenKind::Keyword(Kwd::Assign) => {
                let res = Expr::consume(&tokens[1..], ExprDelim::Comma, true, None, None, ends_early, containing_token, errors);
                match res {
                    Err(None) => Err(None),
                    Err(Some(c)) => Err(Some(c + 1)),
                    Ok(expr) => {
                        let src = &tokens[..1+expr.consumed()];
                        Ok(Pattern::Assign(AssignPattern { src, assignee: Box::new(expr) }))
                    }
                }
            },
            TokenKind::Punctuation(Punc::And) => {
                match Pattern::consume(&tokens[1..], ctx, ends_early, containing_token, errors) {
                    Err(None) => Err(None),
                    Err(Some(c)) => Err(Some(c + 1)),
                    Ok(pat) => {
                        let src = &tokens[..1+pat.consumed()];
                        Ok(Pattern::Ref(RefPattern {
                            src,
                            pat: Box::new(pat),
                        }))
                    }
                }
            },
            TokenKind::Literal(_,_) => Literal::consume(tokens)
                .map(Pattern::Literal),
            @else ExpectedKind::Pattern(ctx),
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
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        consume_fn: ConsumeFn<'a, T>,
        no_elem_err: fn(PatternContext<'a>) -> ExpectedKind<'a>,
        delim_err: fn(PatternContext<'a>, &'a Token<'a>) -> ExpectedKind<'a>,
        errors: &mut Vec<Error<'a>>,
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
                Some(Err(token_tree::Error::UnclosedDelim(_, _))) => {
                    poisoned = true;
                    break;
                }
                // The other tokenizer errors cannot represent a valid pattern, so we produce a
                // secondary error.
                Some(Err(e)) => {
                    errors.push(Error::Expected {
                        kind: no_elem_err(ctx),
                        found: Source::TokenResult(Err(*e)),
                    });

                    poisoned = true;
                    break;
                }

                Some(Ok(_)) => {
                    let res = consume_fn(&inner[consumed..], ctx, ends_early, Some(src), errors);

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
                            kind: delim_err(ctx, src),
                            found: Source::TokenResult(Ok(t)),
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

impl<'a> NamedPattern<'a> {
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
        tokens: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        _ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<NamedPattern<'a>, Option<usize>> {
        // This function comes in two pieces: we first consume the leading path, and then we parse
        // the trailing `[ StructPattern | TuplePattern ]`. We're able to assume that the first
        // token is an identifier because of the guarantees of this function, so we can simplify
        // the inner loop a little bit.

        let fst_ident = match tokens.first() {
            None | Some(Err(_)) => panic!("Expected identifier token, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Ident(name) => Ident { src: t, name },
                _ => panic!("Expected identifier token kind, found {:?}", t.kind),
            },
        };

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
                tokens.get(consumed),
                IdentContext::PatternPath(ctx, &tokens[..consumed]),
                end_source!(containing_token),
                errors,
            )
            .map_err(|()| Some(consumed))?;

            components.push(id);
            consumed += 1;
        }

        let path = PatternPath::Absolute(AbsolutePatternPath {
            src: &tokens[..consumed],
            components,
        });

        // After parsing the absolute path, we then just parse the trailing struct or tuple
        // pattern, if it's there.
        let kind = NamedPatternKind::try_parse(tokens.get(consumed), ctx, errors)
            .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += kind.consumed();

        Ok(NamedPattern {
            src: &tokens[..consumed],
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
        tokens: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        _ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<NamedPattern<'a>, Option<usize>> {
        match tokens.first() {
            None | Some(Err(_)) => panic!("Expected dot (`.`) token, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Dot) => (),
                _ => panic!("Expected dot (`.`) token kind, found {:?}", t.kind),
            },
        }
        let mut consumed = 1;

        let name = Ident::parse(
            tokens.get(consumed),
            IdentContext::PatternPath(ctx, &tokens[..consumed]),
            end_source!(containing_token),
            errors,
        )
        .map_err(|()| None)?;
        consumed += 1;

        let path = PatternPath::Relative(RelativePatternPath {
            src: &tokens[..consumed],
            name,
        });

        let kind = NamedPatternKind::try_parse(tokens.get(consumed), ctx, errors)
            .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += kind.consumed();

        Ok(NamedPattern {
            src: &tokens[..consumed],
            path,
            kind,
        })
    }
}

impl<'a> NamedPatternKind<'a> {
    fn try_parse(
        token: Option<&'a Result<Token<'a>, token_tree::Error<'a>>>,
        ctx: PatternContext<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Option<NamedPatternKind<'a>>, Option<usize>> {
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
            Some(Err(token_tree::Error::UnclosedDelim(d, _))) => match d {
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
                } => TuplePattern::parse(t, inner, ctx, errors)
                    .map(NamedPatternKind::Tuple)
                    .map(Some)
                    .map_err(|()| Some(1)),
                TokenKind::Tree {
                    delim: Delim::Curlies,
                    inner,
                    ..
                } => StructPattern::parse(t, inner, ctx, errors)
                    .map(NamedPatternKind::Struct)
                    .map(Some)
                    .map_err(|()| Some(1)),
                _ => Ok(None),
            },
        }
    }
}

impl<'a> StructPattern<'a> {
    /// Parses a struct pattern from the given curly-brace token and its inner tokens
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<StructPattern<'a>, ()> {
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
                        found: Source::TokenResult(Err(*e)),
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
                            None => break Some(t),
                            Some(res) => {
                                errors.push(Error::Expected {
                                    kind: ExpectedKind::StructPatternEnd(ctx),
                                    found: Source::TokenResult(res.as_ref().map_err(|e| *e)),
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
                                found: Source::TokenResult(Ok(t)),
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
                            kind: ExpectedKind::StructPatternDelim(ctx, src),
                            found: Source::TokenResult(Ok(t)),
                        });

                        poisoned = true;
                        break None;
                    }
                },
            }
        };

        Ok(StructPattern {
            src,
            fields,
            has_dots,
            poisoned,
        })
    }
}

impl<'a> FieldPattern<'a> {
    /// Consumes a single struct field pattern as a prefix of the given tokens
    ///
    /// This function expects that the first token in the list will be an identifier, and will
    /// panic if this condition is not met.
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<FieldPattern<'a>, Option<usize>> {
        let name = match tokens.first() {
            None | Some(Err(_)) => panic!("Expected identifier token, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Ident(name) => Ident { src: t, name },
                _ => panic!("Expected identifier token kind, found {:?}", t.kind),
            },
        };

        macro_rules! only_name {
            () => {{
                Ok(FieldPattern {
                    src: &tokens[..1],
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
        let pat_res = Pattern::consume(&tokens[2..], ctx, ends_early, containing_token, errors);
        match pat_res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(c + 2)),
            Ok(pat) => {
                let src = &tokens[..pat.consumed() + 2];
                Ok(FieldPattern {
                    src,
                    name,
                    binding: Some(pat),
                })
            }
        }
    }
}

impl<'a> TuplePattern<'a> {
    /// Parses a tuple pattern from the given parentheses-enclosed block and its inner tokens
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TuplePattern<'a>, ()> {
        let (elements, poisoned) = Pattern::consume_delimited(
            src,
            inner,
            ctx,
            Pattern::consume,
            ExpectedKind::TuplePatternElement,
            ExpectedKind::TuplePatternDelim,
            errors,
        )?;

        Ok(TuplePattern {
            src,
            elements,
            poisoned,
        })
    }
}

impl<'a> ArrayPattern<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ArrayPattern<'a>, ()> {
        let (elements, poisoned) = Pattern::consume_delimited(
            src,
            inner,
            ctx,
            ElementPattern::consume,
            ExpectedKind::ArrayPatternElement,
            ExpectedKind::ArrayPatternDelim,
            errors,
        )?;

        Ok(ArrayPattern {
            src,
            elements,
            poisoned,
        })
    }
}

impl<'a> ElementPattern<'a> {
    /// Consumes a single array element pattern; a helper function for [`ArrayPattern::parse`]
    ///
    /// [`ArrayPattern::parse`]: struct.ArrayPattern.html#method.parse
    fn consume(
        tokens: TokenSlice<'a>,
        ctx: PatternContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ElementPattern<'a>, Option<usize>> {
        match tokens.first() {
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ArrayPatternElement(ctx),
                    found: end_source!(containing_token),
                });

                Err(None)
            }
            // Because any delimiter can be a valid pattern, we won't emit a second error here
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => return Err(None),
            // Otherwise, this is *still* an error, so we'll generate another one
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ArrayPatternElement(ctx),
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }

            // If we do find a token, we'll give a special case for dots (`..`), else we'll try a
            // regular pattern.
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::DotDot) => Ok(ElementPattern::Dots(t)),
                _ => Pattern::consume(tokens, ctx, ends_early, containing_token, errors)
                    .map(ElementPattern::Pattern),
            },
        }
    }
}
