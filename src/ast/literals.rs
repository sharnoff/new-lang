//! Literal parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

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

#[derive(Debug)]
pub struct CharLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    content: &'a str,
}

#[derive(Debug)]
pub struct StringLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    content: &'a str,
}

#[derive(Debug)]
pub struct IntLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    content: &'a str,
}

#[derive(Debug)]
pub struct FloatLiteral<'a> {
    pub(super) src: TokenSlice<'a>,
    /// The value before the decimal point
    pre: IntLiteral<'a>,
    /// The value after the decimal point
    post: IntLiteral<'a>,
}

impl<'a> Ident<'a> {
    /// Parses an identifier from the given token, which is required (though not assumed) to be
    /// `Some`
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
    pub fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Literal<'a>, Option<usize>> {
        todo!()
    }
}
