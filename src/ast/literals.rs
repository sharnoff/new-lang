//! Literal parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;
use crate::tokens::LiteralKind;

#[derive(Debug, Copy, Clone)]
pub struct Ident<'a> {
    pub(super) src: &'a Token<'a>,
    pub name: &'a str,
}

#[derive(Debug)]
pub enum Literal<'a> {
    Char(CharLiteral<'a>),
    String(StringLiteral<'a>),
    Int(IntLiteral<'a>),
    Float(FloatLiteral<'a>),
}

/// Character literals
#[derive(Debug)]
pub struct CharLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    pub content: &'a str,
}

#[derive(Debug)]
pub struct StringLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    pub content: &'a str,
}

/// Integer literals
#[derive(Debug)]
pub struct IntLiteral<'a> {
    pub(super) src: TokenSlice<'a>,
    /// The content of the literal
    pub content: &'a str,
    /// An optional type suffix - we use an `Ident` to pair it with the source
    pub suffix: Option<Ident<'a>>,
}

/// Floating-point literals, represented by two integer literals glued to a dot (`.`) between them
#[derive(Debug)]
pub struct FloatLiteral<'a> {
    pub(super) src: TokenSlice<'a>,
    /// The value before the decimal point
    pub pre: &'a str,
    /// The value after the decimal point
    pub post: &'a str,
    /// An optional type suffix - we use an `Ident` to pair it with the source
    pub suffix: Option<Ident<'a>>,
}

impl<'a> Ident<'a> {
    /// Parses an identifier from the given token
    ///
    /// If the value of `token` is anything other than `Some(Ok(t))` where `t.kind` is an
    /// identifier, [`Error::Expecting`] will be added to the list of errors passed in, using
    /// `ExpectedKind::Ident(ctx)` as the context.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub fn parse(
        token: Option<&'a TokenResult<'a>>,
        ctx: IdentContext<'a>,
        none_source: Source<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Ident<'a>, ()> {
        let token = match token.map(|res| res.as_ref()) {
            Some(Ok(t)) => t,
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::Ident(ctx),
                    found: Source::TokenResult(Err(*e)),
                });

                return Err(());
            }
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::Ident(ctx),
                    found: none_source,
                });

                return Err(());
            }
        };

        let name = match &token.kind {
            TokenKind::Ident(id) => id,
            _ => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::Ident(ctx),
                    found: Source::TokenResult(Ok(token)),
                });

                return Err(());
            }
        };

        Ok(Ident { name, src: token })
    }
}

impl<'a> Literal<'a> {
    /// Consumes a literal as a prefix of the given tokens
    ///
    /// This function expects the first token to be a literal (note: distinct from the syntax
    /// element), and will panic if this is not the case.
    pub fn consume(
        tokens: TokenSlice<'a>,
        _ends_early: bool,
        _containing_token: Option<&'a Token<'a>>,
        _errors: &mut Vec<Error<'a>>,
    ) -> Result<Literal<'a>, Option<usize>> {
        // There's a few different literals that we can have here. They all start with a "literal"
        // token, and some continue on to use further tokens afterwards.
        //
        // This function completely parses all literal variants, and so we return character and
        // string literals early here, and continue on by building a floating-point literal piece
        // by piece. At each step (past the first couple), if building the floating-point literal
        // fails, we fall back to returning a simple integer literal.
        //
        // This function *does* expect a literal as the first token, so we'll panic if that isn't
        // the case.

        let (fst_token, value, kind) = match tokens.first() {
            Some(Err(_)) | None => panic!("Expected literal token, found {:?}", tokens.first()),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Literal(value, kind) => (t, value, kind),
                _ => panic!("Expected literal token kind, found {:?}", t.kind),
            },
        };

        // For character and string literals, we can simply return the values because they
        // aren't very complicated
        //
        // Otherwise, we'll keep the integer literal around to determine whether we're parsing an
        // integer or floating-point literal.
        match kind {
            LiteralKind::Char => {
                return Ok(Literal::Char(CharLiteral {
                    src: fst_token,
                    content: value,
                }));
            }
            LiteralKind::String => {
                return Ok(Literal::String(StringLiteral {
                    src: fst_token,
                    content: value,
                }));
            }
            LiteralKind::Int => (),
        }

        // We'll define a helper macro to generate a "simple" integer literal - this is so that
        macro_rules! simple_int_literal {
            () => {{
                Ok(Literal::Int(IntLiteral {
                    src: &tokens[..1],
                    content: value,
                    suffix: None,
                }))
            }};
        }

        // If there's whitespace after the first token, it's the end of the literal - we'll return
        // the integer
        if !fst_token.trailing_whitespace.is_empty() {
            return simple_int_literal!();
        }

        // Otherwise, we continue
        match tokens.get(1) {
            // In the case of an error, we'll just return what we have and leave it to the caller
            // to generate an error here.
            Some(Err(_)) | None => return simple_int_literal!(),

            Some(Ok(t)) => match &t.kind {
                // If we see a dot (`.`), we'll continue and try to parse the rest of the tokens as
                // a floating-point literal
                TokenKind::Punctuation(Punc::Dot) if t.trailing_whitespace.is_empty() => (),
                // If we find an identifier, it's a type suffix for an integer literal! We'll
                // return it
                TokenKind::Ident(suffix) => {
                    return Ok(Literal::Int(IntLiteral {
                        src: &tokens[..2],
                        content: value,
                        suffix: Some(Ident {
                            src: t,
                            name: suffix,
                        }),
                    }));
                }

                // Anything else isn't part of the literal, so we'll just return
                _ => return simple_int_literal!(),
            },
        }

        // At this point, we've found:
        //   IntLiteral "."
        // and so we're expecting another IntLiteral to finish up the floating-point value. If we
        // don't find it, however, it could have been something else, so we simply return the
        // simple integer literal
        let (snd_token, post_value) = match tokens.get(2) {
            Some(Err(_)) | None => return simple_int_literal!(),
            Some(Ok(t)) => match &t.kind {
                TokenKind::Literal(value, LiteralKind::Int) => (t, value),
                _ => return simple_int_literal!(),
            },
        };

        // If there's no trailing whitespace on the second token, we might be able to get a type
        // suffix - we'll try this, and fallback to the literal without one if it fails
        if snd_token.trailing_whitespace.is_empty() {
            match tokens.get(3) {
                Some(Err(_)) | None => (),
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Ident(suffix) => {
                        return Ok(Literal::Float(FloatLiteral {
                            src: &tokens[..4],
                            pre: value,
                            post: post_value,
                            suffix: Some(Ident {
                                src: t,
                                name: suffix,
                            }),
                        }));
                    }
                    _ => (),
                },
            }
        }

        // Finally, we return a plain float literal
        Ok(Literal::Float(FloatLiteral {
            src: &tokens[..3],
            pre: value,
            post: post_value,
            suffix: None,
        }))
    }
}
