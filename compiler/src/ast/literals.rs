//! Literal parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;
use crate::files::{FileInfo, Span};
use crate::tokens::LiteralKind;

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone, Consumed)]
pub struct Ident {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(1)]
    pub name: String,
}

#[derive(Debug, Clone, Consumed)]
pub enum Literal {
    Char(CharLiteral),
    String(StringLiteral),
    Int(IntLiteral),
    Float(FloatLiteral),
}

/// Character literals
#[derive(Debug, Clone, Consumed)]
pub struct CharLiteral {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(1)]
    pub content: String,
}

#[derive(Debug, Clone, Consumed)]
pub struct StringLiteral {
    #[consumed(@ignore)]
    pub(super) src: Span,

    #[consumed(1)]
    pub content: String,
}

/// Integer literals
#[derive(Debug, Clone, Consumed)]
pub struct IntLiteral {
    #[consumed(@ignore)]
    pub(super) src: Span,

    /// The content of the literal
    #[consumed(1)]
    pub content: String,

    /// An optional type suffix - we use an `Ident` to pair it with the source
    pub suffix: Option<Ident>,
}

/// Floating-point literals, represented by two integer literals glued to a dot (`.`) between them
#[derive(Debug, Clone, Consumed)]
pub struct FloatLiteral {
    #[consumed(@ignore)]
    pub(super) src: Span,

    /// The value before the decimal point
    #[consumed(1)]
    pub pre: String,

    /// The value after the decimal point
    #[consumed(1)]
    pub post: String,

    /// An optional type suffix - we use an `Ident` to pair it with the source
    pub suffix: Option<Ident>,
}

impl Ident {
    /// Parses an identifier from the given token
    ///
    /// If the value of `token` is anything other than `Some(Ok(t))` where `t.kind` is an
    /// identifier, [`Error::Expecting`] will be added to the list of errors passed in, using
    /// `ExpectedKind::Ident(ctx)` as the context.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub fn parse(
        file: &FileInfo,
        token: Option<&TokenResult>,
        ctx: IdentContext,
        none_source: Source,
        errors: &mut Vec<Error>,
    ) -> Result<Ident, ()> {
        let token = match token.map(|res| res.as_ref()) {
            Some(Ok(t)) => t,
            Some(Err(_)) => return Err(()),
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
                    found: Source::token(file, token),
                });

                return Err(());
            }
        };

        Ok(Ident {
            name: String::from(*name),
            src: token.span(file),
        })
    }
}

impl Literal {
    /// Consumes a literal as a prefix of the given tokens
    ///
    /// This function expects the first token to be a literal (note: distinct from the syntax
    /// element), and will panic if this is not the case.
    pub fn consume(file: &FileInfo, tokens: TokenSlice) -> Result<Literal, Option<usize>> {
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

        let (fst_token, value, kind) = assert_token!(
            tokens.first() => "literal",
            // `value` is converted from &&str -> String
            Ok(t) && TokenKind::Literal(value, kind) => (t, (*value).into(), kind),
        );

        // For character and string literals, we can simply return the values because they
        // aren't very complicated
        //
        // Otherwise, we'll keep the integer literal around to determine whether we're parsing an
        // integer or floating-point literal.
        match kind {
            LiteralKind::Char => {
                return Ok(Literal::Char(CharLiteral {
                    src: fst_token.span(file),
                    content: value,
                }));
            }
            LiteralKind::String => {
                return Ok(Literal::String(StringLiteral {
                    src: fst_token.span(file),
                    content: value,
                }));
            }
            LiteralKind::Int => (),
        }

        // We'll define a helper macro to generate a "simple" integer literal - this is so that
        macro_rules! simple_int_literal {
            () => {{
                Ok(Literal::Int(IntLiteral {
                    src: fst_token.span(file),
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
                        src: fst_token.span(file).join(t.span(file)),
                        content: value,
                        suffix: Some(Ident {
                            src: t.span(file),
                            name: (*suffix).into(),
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
                TokenKind::Literal(value, LiteralKind::Int) => (t, (*value).into()),
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
                            src: fst_token.span(file).join(t.span(file)),
                            pre: value,
                            post: post_value,
                            suffix: Some(Ident {
                                src: t.span(file),
                                name: (*suffix).into(),
                            }),
                        }));
                    }
                    _ => (),
                },
            }
        }

        // Finally, we return a plain float literal
        Ok(Literal::Float(FloatLiteral {
            src: fst_token.span(file).join(snd_token.span(file)),
            pre: value,
            post: post_value,
            suffix: None,
        }))
    }

    /// Returns the `Span` corresponding to the source of the literal
    pub fn span(&self) -> Span {
        match self {
            Literal::Char(lit) => lit.src,
            Literal::String(lit) => lit.src,
            Literal::Int(lit) => lit.src,
            Literal::Float(lit) => lit.src,
        }
    }
}
