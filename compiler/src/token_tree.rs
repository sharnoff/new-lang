//! The second half of tokenizing
//!
//! The primary usage of this module is to take the output of [`crate::tokens`] and to construct
//! token trees from it.
//!
//! Token trees are a tree structure where certain matched characters (namely: parenthesis, square
//! brackets, and curly braces) are collapsed into a single node, where all of the children are
//! themselves nodes in the tree. This idea is primarily taken from Rust, which briefly mentions
//! them in [the reference](https://doc.rust-lang.org/stable/reference/tokens.html#delimiters).
//!
//! In addition to constructing token trees, the tokens here are additionally collapsed to be
//! independent of whitespace - each token may optionally have trailing whitespace or comments.
//!
//! Further details (e.g. how leading whitespace / comments at the start of a file are handled) can
//! be found in the description for the primary exported function from this module: [`file_tree`].
//!
//! [`crate::tokens`]: ../tokens/index.html
//! [`file_tree`]: fn.file_tree.html

use crate::error::{self, Builder as ErrorBuilder, ToError};
use crate::files::{FileInfo, Span};
use crate::tokens::{self, LiteralKind, SimpleToken};

// TODO: Document - gives the output of tokenizing the entire file.
pub fn file_tree<'a>(simple_tokens: &'a [SimpleToken<'a>], ends_early: bool) -> FileTokenTree<'a> {
    // Trim any leading whitespace from the tokens
    use tokens::TokenKind::{BlockComment, LineComment, Whitespace};

    let n_leading_whitespace = simple_tokens
        .iter()
        .take_while(|t| match t.kind {
            Whitespace | LineComment | BlockComment => true,
            _ => false,
        })
        .count();

    let mut idx = n_leading_whitespace;
    let mut tokens = Vec::new();
    while idx < simple_tokens.len() {
        let res = Token::consume(&simple_tokens[idx..], None, ends_early, None);
        match res {
            Ok((res, c)) => {
                tokens.push(res);
                idx += c;
            }
            Err((Some(e), c)) => {
                tokens.push(Err(e));
                idx += c;
            }
            Err((None, c)) => idx += c,
        }
    }

    FileTokenTree {
        leading_whitespace: &simple_tokens[..n_leading_whitespace],
        tokens,
    }
}

#[derive(Debug, Clone)]
pub struct FileTokenTree<'a> {
    pub leading_whitespace: &'a [SimpleToken<'a>],
    pub tokens: Vec<Result<Token<'a>, Error<'a>>>,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct Token<'a> {
    pub trailing_whitespace: &'a [SimpleToken<'a>],
    // Note: `src` doesn't contain leading or trailing whitespace
    pub src: &'a [SimpleToken<'a>],
    pub kind: TokenKind<'a>,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum TokenKind<'a> {
    Punctuation(Punc),
    Tree {
        delim: Delim,
        leading_whitespace: &'a [SimpleToken<'a>],
        inner: Vec<Result<Token<'a>, Error<'a>>>,
    },
    ProofLines(Vec<Result<Token<'a>, Error<'a>>>),
    Keyword(Kwd),
    Literal(&'a str, LiteralKind),
    Ident(&'a str),
}

/// A marker version [`TokenKind`], so that the type of a token can be given independently of what
/// it references
///
/// This type is returned from the [`kind`] method on a [`Token`].
///
/// [`TokenKind`]: enum.TokenKind.html
/// [`Token`]: struct.Token.html
/// [`kind`]: struct.Token.html#method.kind
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenKindMarker {
    Punctuation(Punc),
    Tree(Delim),
    ProofLines,
    Keyword(Kwd),
    Literal(LiteralKind),
    Ident,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub enum Error<'a> {
    UnexpectedCloseDelim(SimpleToken<'a>),
    MismatchedCloseDelim {
        delim: Delim,
        first: SimpleToken<'a>,
        end: SimpleToken<'a>,
    },
    UnclosedDelim(Delim, &'a [SimpleToken<'a>], Option<ProofSrc<'a>>),
    NestedProofLines(SimpleToken<'a>, SimpleToken<'a>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    UnexpectedCloseDelim(Delim),
    MismatchedCloseDelim(Delim),
    UnclosedDelim,
    NestedProofLines,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Copy, Clone)]
pub struct ProofSrc<'a>(SimpleToken<'a>);

macro_rules! kwds {
    (
        $($variant:ident => $str:expr,)*
    ) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub enum Kwd {
            $($variant,)*
        }

        impl Kwd {
            fn try_from(ident: &str) -> Option<Kwd> {
                match ident {
                    $($str => Some(Kwd::$variant),)*
                    _ => None,
                }
            }
        }
    }
}

kwds! {
    As => "as",
    Assign => "assign",
    Break => "break",
    Const => "const",
    Continue => "continue",
    Do => "do",
    Else => "else",
    Enum => "enum",
    Exists => "exists",
    Fn => "fn",
    For => "for",
    Forall => "forall",
    If => "if",
    Impl => "impl",
    Import => "import",
    In => "in",
    Init => "init",
    Invariant => "invariant",
    Is => "is",
    Let => "let",
    Loop => "loop",
    Macro => "macro",
    Match => "match",
    Mod => "mod",
    Mut => "mut",
    Pub => "pub",
    Pure => "pure",
    Ref => "ref",
    Return => "return",
    SelfKwd => "self",
    Static => "static",
    Trait => "trait",
    Type => "type",
    Use => "use",
    While => "while",
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Delim {
    Parens,
    Squares,
    Curlies,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Punc {
    Semi,        // ";"
    DoubleColon, // "::"
    Colon,       // ":"
    Comma,       // ","
    DotDot,      // ".."
    Dot,         // "."
    ThinArrow,   // "->"
    ThickArrow,  // "=>"
    DoubleImpl,  // "<=>"
    EqEq,        // "=="
    Eq,          // "="
    Le,          // "<="
    Lt,          // "<"
    Ge,          // ">="
    Gt,          // ">"
    And,         // "&"
    OrOr,        // "||"
    Or,          // "|"
    NotEq,       // "!="
    Not,         // "!"
    Plus,        // "+"
    Minus,       // "-"
    Star,        // "*"
    Slash,       // "/"
    Percent,     // "%"
    Caret,       // "^"
    Tilde,       // "~"
    Question,    // "?"
    Hash,        // "#"
}

/// A helper function to return whether a set of whitespace tokens constitutes a single newline
///
/// The exact semantics are a little weird here... the best idea of how this should be used is
/// given by the places that use it.
fn is_leading_newline(tokens: &[SimpleToken]) -> bool {
    use tokens::TokenKind::{BlockComment, LineComment, Whitespace};

    let mut found_newline = false;

    let mut finish_next = false;
    for t in tokens {
        finish_next = false;

        match t.kind {
            BlockComment => {
                for _ in t.src.chars().filter(|c| *c == '\n') {
                    // If we find a newline inside of a block comment, then we can't have a leading
                    // newline for our whitespace - this is because the block comment is guaranteed
                    // to end with '*/', so that will be *after* the newline.
                    return false;
                }
            }
            LineComment => (),
            Whitespace => {
                for _ in t.src.chars().filter(|c| *c == '\n') {
                    // we don't allow two newlines
                    if found_newline {
                        return false;
                    }

                    found_newline = true;
                }
            }
            _ => panic!("expected whitespace or comment token, found {:?}", t),
        }
    }

    found_newline && finish_next
}

impl Delim {
    fn open_char(&self) -> char {
        match self {
            Delim::Parens => '(',
            Delim::Squares => '[',
            Delim::Curlies => '{',
        }
    }

    fn close_char(&self) -> char {
        match self {
            Delim::Parens => ')',
            Delim::Squares => ']',
            Delim::Curlies => '}',
        }
    }
}

impl<'a> Token<'a> {
    fn consume(
        tokens: &'a [SimpleToken<'a>],
        inside_proof: Option<ProofSrc<'a>>,
        ends_early: bool,
        enclosing_delim: Option<SimpleToken<'a>>,
    ) -> Result<(Result<Token<'a>, Error<'a>>, usize), (Option<Error<'a>>, usize)> {
        use tokens::TokenKind::*;
        use Error::{MismatchedCloseDelim, UnexpectedCloseDelim};

        assert!(tokens.len() >= 1);

        macro_rules! punc {
            ($variant:ident) => {
                punc!($variant, 1)
            };
            ($variant:ident, $len:expr) => {{
                (Ok(TokenKind::Punctuation(Punc::$variant)), $len)
            }};
        }

        let first = tokens[0];
        let kinds = tokens.iter().map(|t| t.kind).take(2).collect::<Vec<_>>();

        let (kind_res, consumed) = match &kinds as &[_] {
            // This is unreachable because of the assert statement at the top
            [] => unreachable!(),

            // And *this* can't happen because we're given that the first token will be
            // non-whitespace.
            [Whitespace, ..] | [LineComment, ..] | [BlockComment, ..] => unreachable!(),

            // Multi-token elements
            [OpenParen, ..] | [OpenCurly, ..] | [OpenSquare, ..] => {
                let (kind, consumed) = Token::consume_delim(tokens, inside_proof, ends_early)?;
                (Ok(kind), consumed)
            }
            // -> Note: proof lines are multi-token as well
            [Hash, ..] if inside_proof.is_none() => {
                let (kind, consumed) = Token::consume_proof_lines(tokens, ends_early);
                (Ok(kind), consumed)
            }

            // Error cases - close delims should be handled by the caller
            [CloseParen, ..] | [CloseSquare, ..] | [CloseCurly, ..] => match enclosing_delim {
                Some(d) => (
                    Err(MismatchedCloseDelim {
                        delim: match d.kind {
                            OpenParen => Delim::Parens,
                            OpenSquare => Delim::Squares,
                            OpenCurly => Delim::Curlies,
                            _ => unreachable!(),
                        },
                        first: d,
                        end: first,
                    }),
                    1,
                ),
                None => (Err(UnexpectedCloseDelim(first)), 1),
            },

            // Some of the "complex" individual tokens
            [Literal(kind), ..] => (Ok(TokenKind::Literal(first.src, *kind)), 1),
            [Ident, ..] => match Kwd::try_from(first.src) {
                Some(kwd) => (Ok(TokenKind::Keyword(kwd)), 1),
                None => (Ok(TokenKind::Ident(first.src)), 1),
            },

            // And all of the punctuation
            [Semi, ..] => punc!(Semi),
            [Colon, Colon, ..] => punc!(DoubleColon, 2),
            [Colon, ..] => punc!(Colon),
            [Comma, ..] => punc!(Comma),
            [Dot, Dot, ..] => punc!(DotDot, 2),
            [Dot, ..] => punc!(Dot),
            [Minus, Gt, ..] => punc!(ThinArrow, 2),
            [Eq, Gt, ..] => punc!(ThickArrow, 2),
            [Lt, Eq, Gt, ..] => punc!(DoubleImpl, 3),
            [Eq, Eq, ..] => punc!(EqEq, 2),
            [Eq, ..] => punc!(Eq),
            [Lt, Eq, ..] => punc!(Le, 2),
            [Lt, ..] => punc!(Lt),
            [Gt, Eq, ..] => punc!(Ge, 2),
            [Gt, ..] => punc!(Gt),
            [And, ..] => punc!(And),
            [Pipe, Pipe, ..] => punc!(OrOr, 2),
            [Pipe, ..] => punc!(Or),
            [Not, Eq, ..] => punc!(NotEq, 2),
            [Not, ..] => punc!(Not),
            [Plus, ..] => punc!(Plus),
            [Minus, ..] => punc!(Minus),
            [Star, ..] => punc!(Star),
            [Slash, ..] => punc!(Slash),
            [Percent, ..] => punc!(Percent),
            [Caret, ..] => punc!(Caret),
            [Tilde, ..] => punc!(Tilde),
            [Question, ..] => punc!(Question),
            [Hash, ..] => punc!(Hash),
        };

        // We'll additionally consume any trailing whitespace.
        let trailing = tokens[consumed..]
            .iter()
            .take_while(|t| match t.kind {
                LineComment | BlockComment | Whitespace => true,
                _ => false,
            })
            .count();

        let token_res = kind_res.map(|kind| Token {
            trailing_whitespace: &tokens[consumed..consumed + trailing],
            src: &tokens[..consumed],
            kind,
        });

        Ok((token_res, consumed + trailing))
    }

    fn consume_delim(
        tokens: &'a [SimpleToken<'a>],
        inside_proof: Option<ProofSrc<'a>>,
        ends_early: bool,
    ) -> Result<(TokenKind<'a>, usize), (Option<Error<'a>>, usize)> {
        use tokens::TokenKind::{
            BlockComment, CloseCurly, CloseParen, CloseSquare, LineComment, OpenCurly, OpenParen,
            OpenSquare, Whitespace,
        };
        use Delim::{Curlies, Parens, Squares};
        use Error::UnclosedDelim;
        use TokenKind::Tree;

        assert!(tokens.len() >= 1);
        let (delim, close) = match tokens[0].kind {
            OpenParen => (Parens, CloseParen),
            OpenSquare => (Squares, CloseSquare),
            OpenCurly => (Curlies, CloseCurly),
            _ => panic!("unexpected initial delim token {:?}", tokens[0]),
        };

        let mut consumed = 1;
        let mut has_leading_newline = false;

        macro_rules! consume_whitespace {
            () => {{
                let n_whitespace = tokens[consumed..]
                    .iter()
                    .take_while(|t| match t.kind {
                        BlockComment | LineComment | Whitespace => true,
                        _ => false,
                    })
                    .count();

                let range = consumed..consumed + n_whitespace;
                consumed = range.end;
                has_leading_newline = is_leading_newline(&tokens[range]);

                n_whitespace
            }};
        }

        // We'll consume all leading whitespace to guarantee that `consume` is called where the
        // first token *isn't* whitespace
        let n_leading = consume_whitespace!();
        let mut inner = Vec::new();

        loop {
            if consumed == tokens.len() {
                // This is an error; we got to EOF and the delimeter wasn't closed.
                return match ends_early {
                    true => Err((None, consumed)),
                    false => Err((Some(UnclosedDelim(delim, tokens, None)), consumed)),
                };
            }

            if inside_proof.is_some() && has_leading_newline {
                // If we had a leading newline, we'll be expecting a '#' token. Otherwise, we have
                // an unclosed delimiter
                match tokens[consumed].kind {
                    tokens::TokenKind::Hash => {
                        consumed += 1;
                        consume_whitespace!();
                        continue;
                    }
                    _ => {
                        return Err((
                            Some(UnclosedDelim(delim, &tokens[..consumed], inside_proof)),
                            consumed,
                        ));
                    }
                }
            }

            if tokens[consumed].kind == close {
                // Increment to mark this token as consumed
                consumed += 1;
                break;
            }

            let (t, c) = Token::consume(
                &tokens[consumed..],
                inside_proof,
                ends_early,
                Some(tokens[0]),
            )?;

            match t.as_ref() {
                Ok(t) => has_leading_newline = is_leading_newline(t.trailing_whitespace),
                Err(_) => {
                    has_leading_newline = is_leading_newline(&tokens[consumed + 1..consumed + c])
                }
            }

            inner.push(t);
            consumed += c;
        }

        Ok((
            Tree {
                delim,
                leading_whitespace: &tokens[1..1 + n_leading],
                inner,
            },
            consumed,
        ))
    }

    fn consume_proof_lines(
        tokens: &'a [SimpleToken<'a>],
        ends_early: bool,
    ) -> (TokenKind<'a>, usize) {
        use tokens::TokenKind::{BlockComment, Hash, LineComment, Whitespace};

        assert!(tokens.len() >= 1);
        let inside_proof = Some(ProofSrc(tokens[0]));

        let mut consumed = 1;
        let mut has_leading_newline = false;

        macro_rules! consume_whitespace {
            () => {{
                let n_whitespace = tokens[consumed..]
                    .iter()
                    .take_while(|t| match t.kind {
                        BlockComment | LineComment | Whitespace => true,
                        _ => false,
                    })
                    .count();

                let range = consumed..consumed + n_whitespace;
                consumed = range.end;
                has_leading_newline = is_leading_newline(&tokens[range]);

                n_whitespace
            }};
        }

        consume_whitespace!();
        let mut inner = Vec::new();

        while consumed < tokens.len() {
            // If we there was a leading newline, we're either expecting a hash ("#") or we're
            // done with proof lines:
            if has_leading_newline {
                match tokens[consumed].kind {
                    Hash => {
                        consumed += 1;
                        consume_whitespace!();
                        continue;
                    }
                    _ => break,
                }
            }

            // Otherwise, we'll consume whatever token we can get here:
            let res = Token::consume(
                &tokens[consumed..],
                inside_proof,
                ends_early,
                Some(tokens[0]),
            );

            match res {
                Err((e, c)) => {
                    consumed += 1;
                    consume_whitespace!();
                    if let Some(e) = e {
                        inner.push(Err(e));
                    }
                }
                Ok((res, c)) => {
                    consumed += c;
                    inner.push(res);
                }
            }
        }

        (TokenKind::ProofLines(inner), consumed)
    }

    fn collect_errors(&self, errors: &mut Vec<Error<'a>>) {
        if let TokenKind::Tree { inner, .. } = &self.kind {
            inner.iter().for_each(|res| match res {
                Err(e) => errors.push(*e),
                Ok(t) => t.collect_errors(errors),
            });
        }
    }

    /// Returns the [`TokenKindMarker`] corresponding to this token's `kind` field
    ///
    /// Please note that this is *distinct* from the field, though related.
    pub fn kind(&self) -> TokenKindMarker {
        use TokenKind::*;
        use TokenKindMarker as Tkm;

        match &self.kind {
            Punctuation(p) => Tkm::Punctuation(*p),
            Tree { delim, .. } => Tkm::Tree(*delim),
            ProofLines(_) => Tkm::ProofLines,
            Keyword(k) => Tkm::Keyword(*k),
            Literal(_, kind) => Tkm::Literal(*kind),
            Ident(_) => Tkm::Ident,
        }
    }

    /// Returns the [`Span`] corresponding to the token's place in the provided file
    ///
    /// This function does not provide any failsafes if the source file does not actually contain
    /// the given token.
    ///
    /// [`Span`]: ../files/struct.Span.html
    pub fn span(&self, file: &FileInfo) -> Span {
        self.src[0]
            .span_in(file)
            .join(self.src.last().unwrap().span_in(file))
    }

    /// Returns the [`Span`] of the last [`SimpleToken`] comprising this token
    ///
    /// This is typically used for producing the end token for a delimited token (e.g. a closing
    /// parenthesis).
    pub fn end_span(&self, file: &FileInfo) -> Span {
        self.src.last().unwrap().span_in(file)
    }
}

impl<'a> FileTokenTree<'a> {
    pub fn collect_errors(&self) -> Vec<Error<'a>> {
        let mut errors = Vec::new();
        self.tokens.iter().for_each(|res| match res {
            Err(e) => errors.push(*e),
            Ok(t) => t.collect_errors(&mut errors),
        });

        errors
    }
}

impl Error<'_> {
    /// Given the source file that this error occured in, returns the span of the error
    pub fn span(&self, file: &FileInfo) -> Span {
        use Error::*;

        match self {
            UnexpectedCloseDelim(t)
            | MismatchedCloseDelim { end: t, .. }
            | UnclosedDelim(_, [t, ..], _)
            | NestedProofLines(_, t) => t.span_in(file),
            UnclosedDelim(_, [], _) => unreachable!(),
        }
    }

    /// Returns the type of error
    pub fn kind(&self) -> ErrorKind {
        use tokens::TokenKind::{CloseCurly, CloseParen, CloseSquare};
        use Error::*;

        match self {
            UnexpectedCloseDelim(token) => {
                let delim = match token.kind {
                    CloseParen => Delim::Parens,
                    CloseCurly => Delim::Curlies,
                    CloseSquare => Delim::Squares,
                    _ => panic!("unexpected `UnexpectedCloseDelim` token {:?}", token),
                };

                ErrorKind::UnexpectedCloseDelim(delim)
            }
            MismatchedCloseDelim { delim, .. } => ErrorKind::MismatchedCloseDelim(*delim),
            UnclosedDelim(_, _, _) => ErrorKind::UnclosedDelim,
            NestedProofLines(_, _) => ErrorKind::NestedProofLines,
        }
    }
}

impl ToError<FileInfo> for Error<'_> {
    fn to_error(self, file: &FileInfo) -> ErrorBuilder {
        use Error::*;

        let file_start_addr = &file.content as &str as *const str as *const u8 as usize;
        let span = |s: &str| {
            let start_addr = s as *const str as *const u8 as usize;
            let start = start_addr - file_start_addr;
            Span {
                file: file.id,
                start,
                end: start + s.len(),
            }
        };

        match self {
            UnexpectedCloseDelim(token) => {
                let span = span(token.src);

                ErrorBuilder::new(format!("unexpected close delimeter '{}'", token.src))
                    .context(span)
                    .highlight(span, error::ERR_COLOR)
            }
            MismatchedCloseDelim { delim, first, end } => {
                let end_span = span(end.src);

                ErrorBuilder::new(format!(
                    "mismatched delimeter; expected '{}', found '{}'",
                    delim.open_char(),
                    end.src,
                ))
                .context(end_span)
                .highlight(span(first.src), error::CTX_COLOR)
                .highlight(end_span, error::ERR_COLOR)
            }
            UnclosedDelim(delim, src, inside_proof) => {
                let end_span = span(src.last().unwrap().src);
                let span = span(src[0].src).join(end_span);

                match inside_proof {
                    None => ErrorBuilder::new(format!(
                        "unclosed delimeter '{}'; expected '{}', found EOF",
                        delim.open_char(),
                        delim.close_char(),
                    ))
                    .context(span)
                    .highlight(span, error::ERR_COLOR),

                    Some(_) => ErrorBuilder::new(format!(
                        "unclosed delimiter '{}' at end of proof lines",
                        delim.open_char(),
                    ))
                    .context(end_span)
                    .highlight(span, error::ERR_COLOR),
                }
            }
            NestedProofLines(fst, snd) => {
                let fst_span = span(fst.src);
                let snd_span = span(snd.src);

                ErrorBuilder::new("cannot nest proof lines")
                    .context(snd_span)
                    .highlight_all(
                        file.id,
                        vec![fst_span.range(), snd_span.range()],
                        error::ERR_COLOR,
                    )
            }
        }
    }
}
