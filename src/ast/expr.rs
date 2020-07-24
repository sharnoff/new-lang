//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Expr<'a> {
    Literal(Literal<'a>),
    Named(PathComponent<'a>),
    PrefixOp(PrefixOpExpr<'a>),
    BinOp(Box<BinOpExpr<'a>>),
    PostfixOp(PostfixOpExpr<'a>),
    Struct(StructExpr<'a>),
    Array(ArrayLitExpr<'a>),
    Tuple(TupleExpr<'a>),
    Block(BlockExpr<'a>),
    AmbiguousBlock(AmbiguousBlockExpr<'a>),
    Let(Box<LetExpr<'a>>),
    For(ForExpr<'a>),
    While(WhileExpr<'a>),
    DoWhile(DoWhileExpr<'a>),
    Loop(LoopExpr<'a>),
    If(IfExpr<'a>),
    Match(MatchExpr<'a>),
}

/// A type alias for managing ambiguous parsing results
type ExprResult<'a> = Result<Expr<'a>, Vec<Expr<'a>>>;

/// A prefix-operator expression, given by the operator and the right-hand-side expression
///
/// The operator is given by a [`PrefixOp`], which is merely a thin wrapper around
/// [`PrefixOpKind`]. The relevant BNFs definitions are:
/// ```text
/// PrefixOpExpr = PrefixOp Expr .
/// PrefixOp     = "!" | "-" | "&" [ "mut" ] | "*" .
/// ```
///
/// There are no publicly-exposed functions to produce prefix-operator expressions - this is
/// because expression parsing is a complex beast that is managed through a key selection of
/// methods on [`Expr`].
///
/// [`PrefixOp`]: struct.PrefixOp.html
/// [`PrefixOpKind`]: enum.PrefixOpKind.hmtl
/// [`Expr`]: enum.Expr.html
#[derive(Debug)]
pub struct PrefixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub op: PrefixOp<'a>,
    pub expr: Box<Expr<'a>>,
}

/// A thin wrapper around [`PrefixOpKind`]; a prefix operator for expressions
#[derive(Debug)]
pub struct PrefixOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: PrefixOpKind,
}

/// The different prefix operators available for expressions
///
/// This is defined by the BNF:
/// ```text
/// PrefixOp = "!" | "-" | "&" [ "mut" ] | "*" .
/// ```
///
/// For more information, see [`PrefixOpExpr`](struct.PrefixOpExpr.html).
#[derive(Debug)]
pub enum PrefixOpKind {
    /// `"!"`
    Not,
    /// `"-"`
    Minus,
    /// `"&" [ "mut" ]`
    Ref { is_mut: bool },
    /// `"*"`
    Deref,
}

#[derive(Debug)]
pub struct BinOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    lhs: Expr<'a>,
    op: BinOp<'a>,
    rhs: Expr<'a>,
}

#[derive(Debug)]
pub struct PostfixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Box<Expr<'a>>,
    op: PostfixOp<'a>,
}

#[derive(Debug)]
pub struct StructExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    ty_expr: Option<Box<Expr<'a>>>,
    fields: StructFieldsExpr<'a>,
}

#[derive(Debug)]
pub struct ArrayLitExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    values: Vec<Expr<'a>>,
}

#[derive(Debug)]
pub struct TupleExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    values: Vec<Expr<'a>>,
}

#[derive(Debug)]
pub struct BlockExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    items: Vec<Stmt<'a>>,
    tail: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct AmbiguousBlockExpr<'a> {
    pub(super) src: &'a Token<'a>,
    name: Ident<'a>,
}

#[derive(Debug)]
pub struct LetExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Pattern<'a>,
    ty: Option<Type<'a>>,
    expr: Expr<'a>,
}

#[derive(Debug)]
pub struct ForExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Pattern<'a>,
    iter: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct WhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pred: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct DoWhileExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    body: BlockExpr<'a>,
    pred: Box<Expr<'a>>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct LoopExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    body: BlockExpr<'a>,
}

#[derive(Debug)]
pub struct IfExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    condition: Box<Expr<'a>>,
    body: BlockExpr<'a>,
    else_branch: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub struct MatchExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Box<Expr<'a>>,
    arms: Vec<(Pattern<'a>, Expr<'a>)>,
}

binding_power! {
    #[derive(Debug, Copy, Clone)]
    pub enum BindingPower {
        // (Almost) All of the postfix operators have the highest binding power, because (almost)
        // all of them should apply before any prefix operators. The only one we leave is type
        // binding, because it is typically written with spaces around it, unlike the others.
        Access, Index, FnCall, NamedStruct, Try;

        // After them, we have the the prefix operators, all of which are present here.
        Not, Minus, Ref, Deref;

        // And then we add back in the remaining postfix operator - type binding, for the reason
        // given above.
        TypeBinding;

        // After the operators that are nearly all in a row, we have the multiplication operators
        Mul, Div, Mod;
        // Followed by addition/subtraction
        Add, Sub;
        // And then with bitshifts taking the rear.
        //
        // The decision for what precedence to give the bitshift operators is not simple. Indeed,
        // there is no standard answer across languages. For example, Rust and Python, and
        // JavaScript both put the precedence in exactly this place (which is part of the reason for
        // this choice), but Go places it with the multiplication operators (along with bitwise
        // AND), and Swift even places it above them!
        //
        // Even with all that, the bitshift operators were placed here simply because they occupy a
        // large amount of space, so a user might visually intuit them to be lower precedence than
        // smaller operators, e.g. addition/subtraction.
        Shl, Shr;

        // After bitshifts, we have the other bit operators. Python, Rust, and JavaScript all have
        // this distinction (albeit with JS placing these after comparison operators).
        BitAnd;
        BitXor;
        BitOr;
        // ^ A note for future changes: A large chunk of the disambiguation used in
        // `Expr::consume_path_segment` relies on `BitOr` having higher binding power than the
        // comparison operaors.

        // We then only have the comparison operators left. Some langauges (Python, Rust, Go, Swift,
        // etc.) place all of these on the same level. JavaScript, however, does something neat
        // that we'd like to copy here - the relational comparison operators ('<', '<=', '>=', '>')
        // are given higher precedence than the equality operators ('==', '!='). This *would* make a
        // lot of sense here, if we didn't provide the relational comparison operators for
        // booleans. Because/if we do, we don't want to have any gotchas for users, so we'll do
        // what everyone else does and lump them all in together.
        Eq, Ne, Lt, Le, Ge, Gt;

        // "Let" expressions have precedence higher than logical AND or OR, so we give them their
        // own binding power, just so they know they're special :)
        Let;

        // Logical OR and AND are given particularly low binding power so that `let` can bind more
        // tightly than them. AND binds more tightly than OR (per precedent set by other
        // languages), and so we finish up the list with the following:
        LogicalAnd;
        LogicalOr;
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExprDelim {
    Comma,
    Semi,
}

impl<'a> Expr<'a> {
    /// Consumes an expression as a prefix of the tokens - assuming that no delimeter occurs within
    /// the binding power.
    ///
    /// This function has a very particular use, made possible by a single, strict assumption that
    /// it makes. For a given set of tokens here, we assume that an expression with the given
    /// minimum binding power occurs before any delimeter, of any kind. If the outer delimeter *is*
    /// a comma, then the binding power must be strictly greater than `Shr` and `Gt` - this is not
    /// checked here.
    ///
    /// Please additionally note that `no_delim` additionally applies to semicolon-delimeted
    /// expressions - because ambiguity only occurs with comma-separated lists of expressions, we
    /// can treat all other cases with this.
    pub fn consume_no_delim(
        tokens: TokenSlice<'a>,
        min_bp: Option<BindingPower>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Expr<'a>, Option<usize>> {
        assert!(min_bp > Some(BindingPower::Shr) && min_bp > Some(BindingPower::Gt));

        // Here, we're doing regular Pratt parsing, because the assumptions made by this function
        // allow us to get rid of any ambiguity that we'd otherwise have.
        //
        // For an intro to Pratt parsing, see this article:
        //     https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

        let mut lhs = Some(Expr::consume_lhs_no_delim(
            tokens,
            allow_structs,
            ends_early,
            containing_token,
            errors,
        )?);
        let mut consumed = lhs.consumed();

        loop {
            let postfix_res = PostfixOp::consume_if_bp_ge(
                &tokens[consumed..],
                min_bp,
                allow_structs,
                ends_early,
                containing_token,
                errors,
            );
            match postfix_res {
                Ok(Err(is_postfix_op)) => match is_postfix_op {
                    true => break,
                    false => (),
                },
                Ok(Ok(op)) => {
                    consumed += op.consumed();

                    lhs = Some(Expr::PostfixOp(PostfixOpExpr {
                        src: &tokens[..consumed],
                        expr: Box::new(lhs.take().unwrap()),
                        op,
                    }));

                    continue;
                }
                Err(None) => return Err(None),
                Err(Some(c)) => return Err(Some(consumed + c)),
            }

            if let Some((left_bp, right_bp, op)) = BinOp::bp(&tokens[consumed..]) {
                if Some(left_bp) < min_bp {
                    break;
                }

                let rhs_start_idx = consumed + op.consumed();
                let rhs_res = Expr::consume_no_delim(
                    &tokens[rhs_start_idx..],
                    right_bp,
                    allow_structs,
                    ends_early,
                    containing_token,
                    errors,
                );

                match rhs_res {
                    Ok(rhs) => {
                        consumed = rhs_start_idx + rhs.consumed();
                        lhs = Some(Expr::BinOp(Box::new(BinOpExpr {
                            src: &tokens[..consumed],
                            lhs: lhs.take().unwrap(),
                            op,
                            rhs,
                        })));
                    }
                    Err(Some(c)) => return Err(Some(c + rhs_start_idx)),
                    Err(None) => return Err(None),
                }

                continue;
            }

            break;
        }

        Ok(lhs.take().unwrap())
    }

    /// A helper function for [`consume_no_delim`](#method.consume_no_delim), documented internally
    fn consume_lhs_no_delim(
        tokens: TokenSlice<'a>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Expr<'a>, Option<usize>> {
        // When looking at the left-hand side of an expression, we're completely ignoring binary
        // and postfix operators.
        //
        // Where normally there would be ambiguity from geneics arguments, we can ignore this here
        // because of the guarantees provided by `consume_no_delim`

        // First, we'll define a helper macro for some of the elements of this function that we
        // pass off elsewhere. Not all calls will fit the format of this macro, but we get enough
        // mileage to make this useful.
        macro_rules! consume {
            ($ty_name:ident, $variant:ident) => {{
                $ty_name::consume(tokens, ends_early, containing_token, errors).map(Expr::$variant)
            }};
        }

        // We'll use the first token to determine how to consume the rest of the expression.
        match tokens.first() {
            // If there is no first token, this is typically an error. If this token tree ended
            // early, however, that error has already been reported - we shouldn't generate a
            // second error from it.
            None if ends_early => Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ExprLhs,
                    found: end_source!(containing_token),
                });

                Err(None)
            }

            // If we find that the first token is a tokenizer error, it *might* not actually be
            // incorrect: an unclosed delimeter error is not actually an error here, because any
            // token tree *might* be a valid expression.
            //
            // So: We'll only produce a second error here if the tokenizer error *also* wouldn't
            // have been a valid expression.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::ExprLhs,
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }

            // And if the token is successful, we'll determine what to match on, based on this.
            Some(Ok(fst_token)) => match &fst_token.kind {
                // The first group is literals - these are fairly simple
                TokenKind::Literal(_, _) => consume!(Literal, Literal),

                // Identifiers are always treated as a path segment. They may contain trailing
                // generics arguments, so we use a dedicated function to handle this.
                TokenKind::Ident(_) => Expr::consume_path_component_no_delim(
                    tokens,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Expr::Named),

                // Token trees (as briefly mentioned above) all have expressions they can be parsed
                // as.
                TokenKind::Tree { delim, inner, .. } => {
                    use Delim::{Curlies, Parens, Squares};

                    // All parsing of token trees returns Result<_, ()>, so we'll map that to mark
                    // the amount we consumed.
                    let res = match delim {
                        // Curly braces are ambiguous, so we have a separate function to handle that
                        Curlies => Expr::parse_curly_block(fst_token, inner, errors, tokens),

                        // Square brackets corresond to array literals and parentheses to tuples, so we
                        // parse both as such.
                        Squares => ArrayLitExpr::parse(fst_token, inner, errors).map(Expr::Array),
                        Parens => TupleExpr::parse(fst_token, inner, errors).map(Expr::Tuple),
                    };

                    res.map_err(|()| Some(1))
                }

                // With those aside, we have prefix operators as our penultimate group. As per
                // 'bnf.md', the following tokens are allowed as prefix operators:
                //   PreifxOp = "!" | "-" | "&" [ "mut" ] | "*"
                // We'll use dedicated function provided by `PrefixOpExpr` for this.
                TokenKind::Punctuation(Punc::Not)
                | TokenKind::Punctuation(Punc::Minus)
                | TokenKind::Punctuation(Punc::And)
                | TokenKind::Punctuation(Punc::Star) => PrefixOpExpr::consume_no_delim(
                    tokens,
                    allow_structs,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Expr::PrefixOp),

                // And finally, we have all of the various keywords that may start an expression:
                TokenKind::Keyword(Kwd::For) => consume!(ForExpr, For),
                TokenKind::Keyword(Kwd::While) => consume!(WhileExpr, While),
                TokenKind::Keyword(Kwd::Do) => consume!(DoWhileExpr, DoWhile),
                TokenKind::Keyword(Kwd::Loop) => consume!(LoopExpr, Loop),
                TokenKind::Keyword(Kwd::If) => consume!(IfExpr, If),
                TokenKind::Keyword(Kwd::Match) => consume!(MatchExpr, Match),
                TokenKind::Keyword(Kwd::Let) => LetExpr::consume_no_delim(
                    tokens,
                    allow_structs,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(|ex| Expr::Let(Box::new(ex))),

                // Otherwise, if we couldn't find any of these, we had an error
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::ExprLhs,
                        found: Source::TokenResult(Ok(fst_token)),
                    });

                    Err(None)
                }
            },
        }
    }

    /// A helper function for [`consume_lhs_no_delim`](#method.consume_lhs_no_delim)
    ///
    /// This consumes a single path component as part of an expression, given the restrictions
    /// provided by [`consume_no_delim`]. We're able to walk though a set of tokens that *might*
    /// constitute generics arguments, where encountering a comma indicates that an opening angle
    /// bracket ("<") is certainly part of generics arguments.
    ///
    /// This function assumes (panicking otherwise) that the first token given is an identifier.
    ///
    /// [`consume_no_delim`]: #method.consume_no_delim
    fn consume_path_component_no_delim(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PathComponent<'a>, Option<usize>> {
        // This function is complex due to the problem it tries to solve: When we see the following
        // tokens
        //   [ Ident, "<", .. ]
        // at the start of the input, we don't immediately know whether the path component ends with
        // the identifier (without generics arguments) or whether the angle bracket gives the start
        // of the generics arguments.
        //
        // Elsewhere (outside the `no_delim` variants of these parsing functions), this hard
        // problem is not entirely dealt with - ambiguity is still left over, and we end up
        // recursively parsing using different assumptions.
        //
        // Thankfully, the assumptions given with `Expr::consume_no_delim` allow us to
        // unambiguously parse path components. This is because of two guarantees:
        //   1. If the outer delimeter is a comma, the expression we're parsing cannot include
        //      comparison operators (i.e. the tokens "<" .. "," must be due to generics)
        //   2. Otherwise, the outer delimeter is not a comma - meaning that any comma we find here
        //      must be generics.
        //
        // There's a few other things we'll note as we get into all of the cases here.

        // To start off with, we'll verify that we were given an identifier to start with.
        let name = {
            let src = tokens[0].as_ref().unwrap();
            let name = match &src.kind {
                TokenKind::Ident(name) => name,
                _ => panic!("expected identifier token as first token, found {:?}", src),
            };

            Ident { src, name }
        };

        // We'll now define a couple helper macros so that we can simply return once we know
        // whether there's generics arguments.
        macro_rules! return_name {
            () => {{
                return Ok(PathComponent {
                    src: &tokens[..1],
                    name,
                    generic_args: None,
                });
            }};
        }

        macro_rules! return_path_component {
            () => {{
                return PathComponent::consume(
                    tokens,
                    // TODO: Give PathComponents a more detailed context so that we know this is
                    // within an expression, not a full `Path`.
                    None,
                    ends_early,
                    containing_token,
                    errors,
                );
            }};
        }

        // Now, if the second token *isn't* "<", we know there aren't any generics arguments here,
        // so we can simply return.
        match tokens.get(1) {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Lt) => (),
                _ => return_name!(),
            },
            _ => return_name!(),
        }

        let mut consumed = 2;

        // At this point, we've consumed `Ident "<"`, and we're expecting either a generics
        // argument or an expression. Generics arguments are any of:
        //   GenericArg = [ Ident ":" ] Type
        //              | [ Ident ":" ] Expr
        //              | "ref" Expr
        // So, we can match through the first couple tokens to determine how to interpret the
        // entire input.

        match tokens.get(consumed) {
            // Unless there was a previous tokenizer error, finding the end of the input after an
            // opening angle-bracket is always an error. We would have expected a generics argument
            // or an expression here.
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericArgOrExpr,
                    found: end_source!(containing_token),
                });

                Err(None)
            }

            // Other tokenizer errors might also be an error here - but only some of them. This
            // isn't too difficult, as any token tree can follow as part of an expression - so we
            // can generate a second error for anything aside from an `UnclosedDelim` error.
            Some(Err(token_tree::Error::UnclosedDelim(_, _))) => Err(None),
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::GenericArgOrExpr,
                    found: Source::TokenResult(Err(*e)),
                });

                Err(None)
            }

            // With no errors here, we continue on with what the first token has given us.
            Some(Ok(t)) => {
                // If we find the "ref" keyword, this must be a generics argument
                if let TokenKind::Keyword(Kwd::Ref) = &t.kind {
                    return_path_component!();
                }

                // If we find an identifier, we'll check whether the next token is a colon - if so,
                // we'd have something like:
                //   `foo<T: `
                // which must be a generics argument.
                match tokens.get(consumed + 1) {
                    Some(Ok(next)) => match &next.kind {
                        TokenKind::Punctuation(Punc::Colon) => return_path_component!(),
                        _ => (),
                    },
                    _ => (),
                }

                // Otherwise, we'll make use of the existing functions for disambiguating between
                // types and expressions.
                let res = TypeOrExpr::consume(
                    &tokens[consumed..],
                    &tokens[1..2],
                    ends_early,
                    containing_token,
                    errors,
                );

                match res {
                    Err(None) => return Err(None),
                    Err(Some(c)) => return Err(Some(consumed + c)),
                    Ok(TypeOrExpr::Type(_)) => return_path_component!(),
                    Ok(TypeOrExpr::Expr(_)) => return_name!(),
                    Ok(TypeOrExpr::Ambiguous { consumed: c, .. }) => consumed += c,
                }

                // And if there's still ambiguity, we look at the next token. At this point, we've
                // consumed a single type or expression. The next token is all we need to determine
                // what to interpret the input as.
                match tokens.get(consumed) {
                    // If we get an error here, we'll return to let this be handled as an
                    // expression, which it will be in most cases.
                    None | Some(Err(_)) => return_name!(),

                    Some(Ok(t)) => match &t.kind {
                        // As we mentioned above, if we know that any input that has
                        //   Ident "<" .. ","
                        // must be from generics arguments
                        TokenKind::Punctuation(Punc::Comma) => return_path_component!(),

                        // Similarly, if we have an input of the form:
                        //   Ident "<" ( Expr | Type ) ">"
                        // we know it must also be a path component.
                        TokenKind::Punctuation(Punc::Gt) => return_path_component!(),

                        // For anything else, we'll treat the original angle-bracket as an
                        // expression because - even though it might be erroneous - it definitely
                        // isn't generics arguments.
                        _ => return_name!(),
                    },
                }
            }
        }
    }

    /// Parses a curly-brace enclosed block as an expression
    ///
    /// This function handles dispatching between `BlockExpr::parse` and `StructFieldsExpr::parse`
    /// depending on the content of the block. In ambiguous cases (e.g. when we have the input
    /// `{ x }`), `Expr::AmbiguousBlock` is returned instead.
    fn parse_curly_block(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
        outer_src: TokenSlice<'a>,
    ) -> Result<Expr<'a>, ()> {
        let kinds = inner
            .iter()
            .take_while(|res| res.is_ok())
            .map(|t| &t.as_ref().unwrap().kind)
            .take(2)
            .collect::<Vec<_>>();

        use TokenKind::Punctuation;

        match &kinds as &[_] {
            // The fully ambiguous case is when there's a single identifier within a
            // curly-brace-enclosed block. That's what we have here.
            [&TokenKind::Ident(name)] => {
                let name = Ident {
                    src: inner[0].as_ref().unwrap(),
                    name,
                };

                Ok(Expr::AmbiguousBlock(AmbiguousBlockExpr { src, name }))
            }

            // If the second token is either a colon or a comma, it must be a struct instantiation
            // that we're parsing. We'll use `StructFieldsExpr::parse` to do so.
            [TokenKind::Ident(_), Punctuation(Punc::Colon)]
            | [TokenKind::Ident(_), Punctuation(Punc::Comma)] => {
                let fields = StructFieldsExpr::parse(inner, false, Some(src), errors)?;

                Ok(Expr::Struct(StructExpr {
                    src: &outer_src[..1],
                    ty_expr: None,
                    fields,
                }))
            }

            // Otherwise, this is *most likely* a block expression (if not, it's invalid).
            // We'll give EOF as the source because it's only used in cases where the token source
            // is None, which we can clearly see is not the case here.
            _ => BlockExpr::parse(outer_src.first(), Source::EOF, errors).map(Expr::Block),
        }
    }
}

impl<'a> PrefixOpExpr<'a> {
    /// Consumes a prefix-operator expression as a prefix of the given tokens
    ///
    /// This function expects the first token to be a prefix operator, and will panic if it is not.
    ///
    /// This makes a recursive call to [`Expr::consume_no_delim`] in order
    fn consume_no_delim(
        tokens: TokenSlice<'a>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PrefixOpExpr<'a>, Option<usize>> {
        // This function is farily simple - we start off by generating the prefix operator, and
        // then parse the rest of the expression.

        // First off, we'll get the prefix operator
        let (op, binding_power) = match tokens.first() {
            None | Some(Err(_)) => panic!("expected a prefix operator, found {:?}", tokens.first()),
            Some(Ok(t)) => {
                macro_rules! op_with_bp {
                    ($kind:ident) => {{
                        (
                            PrefixOp {
                                src: &tokens[..1],
                                kind: PrefixOpKind::$kind,
                            },
                            BindingPower::$kind,
                        )
                    }};
                }

                match &t.kind {
                    // The first three are simple, and given directly by 'bnf.md'
                    TokenKind::Punctuation(Punc::Not) => op_with_bp!(Not),
                    TokenKind::Punctuation(Punc::Minus) => op_with_bp!(Minus),
                    TokenKind::Punctuation(Punc::Star) => op_with_bp!(Deref),
                    // The final one is from the reference operator. It's allowed to be followed by
                    // "mut" to take a mutable reference, so we'll
                    TokenKind::Punctuation(Punc::And) => {
                        let (is_mut, len) = match tokens.get(1) {
                            Some(Ok(t)) => match &t.kind {
                                TokenKind::Keyword(Kwd::Mut) => (true, 2),
                                _ => (false, 1),
                            },
                            _ => (false, 1),
                        };

                        let op = PrefixOp {
                            src: &tokens[..len],
                            kind: PrefixOpKind::Ref { is_mut },
                        };

                        (op, BindingPower::Ref)
                    }
                    _ => panic!("Expected prefix operator, found {:?}", t),
                }
            }
        };

        let rhs_res = Expr::consume_no_delim(
            &tokens[op.consumed()..],
            Some(binding_power),
            allow_structs,
            ends_early,
            containing_token,
            errors,
        );

        match rhs_res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(c + op.consumed())),
            Ok(rhs) => {
                let src = &tokens[..op.consumed() + rhs.consumed()];
                Ok(PrefixOpExpr {
                    src,
                    op,
                    expr: Box::new(rhs),
                })
            }
        }
    }
}

impl<'a> ArrayLitExpr<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ArrayLitExpr<'a>, ()> {
        todo!()
    }
}

impl<'a> TupleExpr<'a> {
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TupleExpr<'a>, ()> {
        todo!()
    }
}

impl<'a> BlockExpr<'a> {
    /// Parses a block expression from the given token
    ///
    /// Because block expressions are always given by the curly braces they're enclosed by, the
    /// single token is expected to be a curly-brace-enclosed block.
    ///
    /// `none_source` indicates the value to use as the source if the token is `None` - this
    /// typically corresponds to the source used for running out of tokens within a token tree.
    pub fn parse(
        token: Option<&'a TokenResult<'a>>,
        none_source: Source<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<BlockExpr<'a>, ()> {
        todo!()
    }
}

impl<'a> LetExpr<'a> {
    /// Consumes a "let" expression, under the assumptions given by [`Expr::consume_no_delim`]
    ///
    /// This function assumes that the starting token is the keyword "let", and will panic if this
    /// condition is not met.
    ///
    /// [`Expr::consume_no_delim`]: struct.Expr.html#consume_no_delim
    fn consume_no_delim(
        tokens: TokenSlice<'a>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<LetExpr<'a>, Option<usize>> {
        // "let" expression parsing is not too complex - the bnf is simply:
        //   LetExpr = "let" Pattern [ ":" Type ] "=" Expr .
        // This function is mainly filled with boilerplate for handling errors and such - a future
        // improvement might be to reduce these, but there's an unfortunate amount of differences
        // between them.

        // To start with, we'll assert that the first token is the keyword "let"
        let let_kwd = match tokens.first() {
            Some(Ok(t)) => match &t.kind {
                TokenKind::Keyword(Kwd::Let) => t,
                k => panic!("Expected keyword 'let', found token kind {:?}", k),
            },
            _ => panic!("Expected keyword 'let', found {:?}", tokens.first()),
        };

        let mut consumed = 1;

        // Next, we have the pattern to bind to
        let pat = Pattern::consume(&tokens[consumed..], ends_early, containing_token, errors)
            .map_err(|cs| cs.map(|c| c + consumed))?;
        consumed += pat.consumed();

        // If we have a ":" token following the pattern, we'll expect a type
        let ty = match tokens.get(consumed) {
            // Tokenizer errors are properly errors here, because we're either expecting a colon
            // (for indincating the type) or an equals for binding the value.
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::LetColonOrEq(LetContext {
                        let_kwd,
                        pat: &tokens[1..consumed],
                    }),
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::LetColonOrEq(LetContext {
                        let_kwd,
                        pat: &tokens[1..consumed],
                    }),
                    found: Source::TokenResult(Err(*e)),
                });

                return Err(None);
            }

            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Eq) => None,
                TokenKind::Punctuation(Punc::Colon) => {
                    consumed += 1;
                    let ty_res = Type::consume(
                        &tokens[consumed..],
                        TypeContext::LetHint(LetContext {
                            let_kwd,
                            pat: &tokens[1..consumed - 1],
                        }),
                        ends_early,
                        containing_token,
                        errors,
                    );

                    match ty_res {
                        Err(Some(c)) => return Err(Some(c + consumed)),
                        Err(None) => return Err(None),
                        Ok(ty) => {
                            consumed += ty.consumed();
                            Some(ty)
                        }
                    }
                }
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::LetColonOrEq(LetContext {
                            let_kwd,
                            pat: &tokens[1..consumed],
                        }),
                        found: Source::TokenResult(Ok(t)),
                    });

                    return Err(None);
                }
            },
        };

        // Now, we'll expect an equals for assigning the value
        match tokens.get(consumed) {
            None if ends_early => return Err(None),
            None => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::LetEq(LetContext {
                        let_kwd,
                        pat: &tokens[1..consumed],
                    }),
                    found: end_source!(containing_token),
                });

                return Err(None);
            }
            Some(Err(e)) => {
                errors.push(Error::Expected {
                    kind: ExpectedKind::LetEq(LetContext {
                        let_kwd,
                        pat: &tokens[1..consumed],
                    }),
                    found: Source::TokenResult(Err(*e)),
                });

                return Err(None);
            }
            Some(Ok(t)) => match &t.kind {
                TokenKind::Punctuation(Punc::Eq) => consumed += 1,
                _ => {
                    errors.push(Error::Expected {
                        kind: ExpectedKind::LetEq(LetContext {
                            let_kwd,
                            pat: &tokens[1..consumed],
                        }),
                        found: Source::TokenResult(Ok(t)),
                    });

                    return Err(None);
                }
            },
        }

        let expr_res = Expr::consume_no_delim(
            &tokens[consumed..],
            Some(BindingPower::Let),
            allow_structs,
            ends_early,
            containing_token,
            errors,
        );

        match expr_res {
            Err(None) => Err(None),
            Err(Some(c)) => Err(Some(c + consumed)),
            Ok(expr) => {
                consumed += expr.consumed();

                Ok(LetExpr {
                    src: &tokens[..consumed],
                    pat,
                    ty,
                    expr,
                })
            }
        }
    }
}

impl<'a> ForExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ForExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> WhileExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<WhileExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> DoWhileExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<DoWhileExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> LoopExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<LoopExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> IfExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<IfExpr<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> MatchExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MatchExpr<'a>, Option<usize>> {
        todo!()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Ident                                                                                        //
// * Path                                                                                         //
//   * PathComponent                                                                              //
// * PrefixOp                                                                                     //
//   * PrefixOpKind                                                                               //
// * BinOp                                                                                        //
//   * BinOpKind                                                                                  //
// * PostfixOp                                                                                    //
//   * PostfixOpKind                                                                              //
// * StructFieldsExpr                                                                             //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A path to an item in scope
///
/// The standard image of a path contains no generic arguments: it is simply a chain of identifiers
/// linked together by dots (`"."`). Note, however, that they *can* have generics arguments at any
/// component. For example, `foo<int>.Bar<String>` is a valid path.
///
/// Because of their usage of generics arguments, certain ambiguities arise within expression
/// parsing - this is not managed by the primary parser provided by this type.
///
/// For reference, the BNF is defined as:
/// ```text
/// Path = Ident [ GenericArgs ] { "." Ident [ GenericArgs ] } .
/// ```
///
/// The helper type [`PathComponent`] is defined as well to manage the token sources for individual
/// elements, where its BNF is:
/// ```text
/// PathComponent = Ident [ GenericArgs ] .
/// ```
///
/// [`PathComponent`]: struct.PathComponent.html
#[derive(Debug)]
pub struct Path<'a> {
    pub(super) src: TokenSlice<'a>,
    components: Vec<PathComponent<'a>>,
}

/// A single component of a type
///
/// For more information, refer to the documentation of [`Path`](struct.Path.html).
#[derive(Debug)]
pub struct PathComponent<'a> {
    pub(super) src: TokenSlice<'a>,
    name: Ident<'a>,
    generic_args: Option<GenericArgs<'a>>,
}

#[derive(Debug)]
pub struct BinOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: BinOpKind,
}

#[derive(Debug)]
pub enum BinOpKind {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Mod,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `^`
    BitXor,
    /// `<<`
    Shl,
    /// `>>`
    Shr,
    /// `&&`
    LogicalAnd,
    /// `||`
    LogicalOr,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Le,
    /// `>=`
    Ge,
    /// `==`
    Eq,
    /// `!=`
    Ne,
}

#[derive(Debug)]
pub struct PostfixOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: PostfixOpKind<'a>,
}

#[derive(Debug)]
pub enum PostfixOpKind<'a> {
    /// `"[" Expr "]"`
    Index(Box<Expr<'a>>),
    /// `"." Ident [ GenericArgs ]`
    Access(PathComponent<'a>),
    /// `"." IntLiteral`
    TupleIndex(IntLiteral<'a>),
    /// `"(" StructFieldsExpr ")"`
    FnCall(/* TODO */),
    /// `"{" StructFieldsExpr "}"`
    NamedStruct(StructFieldsExpr<'a>),
    /// `"~" Type`
    TypeBinding(Box<Type<'a>>),
    /// `"?"`
    Try,
}

#[derive(Debug)]
pub struct StructFieldsExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    fields: Vec<(Ident<'a>, Option<Expr<'a>>)>,
}

impl<'a> Path<'a> {
    /// Consumes a `Path` as a prefix of the given tokens
    ///
    /// Note that this function should not be used where there may be ambiguity with generics
    /// arguments (primarily within expression parsing). Additionally, this function should not be
    /// used if a dot (`"."`) is allowed after a path at the desired position; it will be parsed as
    /// a path separator and will expect a following path component.
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Path<'a>, Option<usize>> {
        // We always require a first element in the path
        let fst = PathComponent::consume(tokens, None, ends_early, containing_token, errors)
            .map_err(|_| None)?;
        let mut consumed = fst.consumed();

        let mut components = vec![fst];

        loop {
            // If we find a path separator token ("."), we'll look for another path component
            match tokens.get(consumed) {
                Some(Ok(t)) => match &t.kind {
                    TokenKind::Punctuation(Punc::Dot) => consumed += 1,
                    _ => break,
                },
                _ => break,
            };

            let next = PathComponent::consume(
                &tokens[consumed..],
                Some(&tokens[..consumed]),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(|_| None)?;
            consumed += next.consumed();
            components.push(next);
        }

        Ok(Path {
            src: &tokens[..consumed],
            components,
        })
    }
}

impl<'a> PathComponent<'a> {
    /// Consumes a single `PathComponent` as a prefix of the given tokens
    ///
    /// This exists solely as a helper function for [`Path::consume`].
    ///
    /// [`Path::consume`]: struct.Path.html#method.consume
    fn consume(
        tokens: TokenSlice<'a>,
        prev_tokens: Option<TokenSlice<'a>>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<PathComponent<'a>, Option<usize>> {
        // Path components are composed of - at most - two pieces: an identifier and optional
        // generic arguments.
        let ctx = PathComponentContext { prev_tokens };

        let name = Ident::parse(
            tokens.first(),
            IdentContext::PathComponent(ctx),
            end_source!(containing_token),
            errors,
        )
        .map_err(|_| None)?;

        let mut consumed = name.consumed();

        let generic_args =
            GenericArgs::try_consume(&tokens[consumed..], ends_early, containing_token, errors)
                .map_err(|_| None)?;

        consumed += generic_args.consumed();

        Ok(PathComponent {
            src: &tokens[..consumed],
            name,
            generic_args,
        })
    }
}

impl<'a> PostfixOp<'a> {
    // success result is Result< "value", "is_postfix" > to give whether the initial token actually
    // was a postfix token - for more context, see how this function is used in `Expr::consume`
    fn consume_if_bp_ge(
        tokens: TokenSlice<'a>,
        min_bp: Option<BindingPower>,
        allow_structs: Option<NoCurlyContext>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Result<PostfixOp<'a>, bool>, Option<usize>> {
        todo!()
    }
}

impl<'a> BinOp<'a> {
    fn bp(tokens: TokenSlice<'a>) -> Option<(BindingPower, Option<BindingPower>, BinOp<'a>)> {
        macro_rules! op {
            // Most operators will only occupy a single token
            ($kind:ident) => {{
                op!($kind, 1)
            }};

            // But some use more, so we provide the second variant here to allow that
            ($kind:ident, $len:expr) => {{
                // We say that the required binding power on the right is one greater than the
                // left, so that the operators are left-associative. Every binary operator we have
                // is left-associative, so we can simply make this a general rule.
                let left_bp = BindingPower::$kind;
                let right_bp = left_bp.inc();
                Some((
                    left_bp,
                    right_bp,
                    BinOp {
                        src: &tokens[..$len],
                        kind: BinOpKind::$kind,
                    },
                ))
            }};
        }

        macro_rules! punc {
            ($($kind:ident),+) => {
                [$(&TokenKind::Punctuation(Punc::$kind),)+ ..]
            };
        }

        let token = tokens.first()?.as_ref().ok()?;

        let mut first_two_kinds = Vec::with_capacity(2);
        first_two_kinds.push(&token.kind);
        match tokens.get(2) {
            Some(Ok(t)) if token.trailing_whitespace.is_empty() => first_two_kinds.push(&t.kind),
            _ => (),
        }

        match &first_two_kinds as &[_] {
            punc!(Plus) => op!(Add),
            punc!(Minus) => op!(Sub),
            punc!(Star) => op!(Mul),
            punc!(Slash) => op!(Div),
            punc!(Percent) => op!(Mod),
            punc!(OrOr) => op!(LogicalOr),
            // We do logical AND before bitwise AND because it's composed of the same tokens
            // Instead of treating AndAnd as a prefix operator (for double reference), we combine
            // two Ands into a single binary operator.
            punc!(And, And) => op!(LogicalAnd, 2),
            punc!(And) => op!(BitAnd),
            punc!(Or) => op!(BitOr),
            punc!(Caret) => op!(BitXor),
            // The same goes for bitshifts
            punc!(Lt, Lt) => op!(Shl, 2),
            punc!(Gt, Gt) => op!(Shr, 2),
            punc!(Lt) => op!(Lt),
            punc!(Gt) => op!(Gt),
            punc!(Le) => op!(Le),
            punc!(Ge) => op!(Ge),
            punc!(EqEq) => op!(Eq),
            punc!(NotEq) => op!(Ne),
            _ => None,
        }
    }
}

impl<'a> StructFieldsExpr<'a> {
    fn parse(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<StructFieldsExpr<'a>, ()> {
        todo!()
    }
}
