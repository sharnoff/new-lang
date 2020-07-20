//! Expression parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
// `Expr` variants                                                                                //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub enum Expr<'a> {
    Access(AccessExpr<'a>),
    TypeBinding(Box<TypeBindExpr<'a>>),
    PrefixOp(PrefixOpExpr<'a>),
    BinOp(Box<BinOpExpr<'a>>),
    PostfixOp(PostfixOpExpr<'a>),
    Let(Box<LetExpr<'a>>),
    FnCall(FnCallExpr<'a>),
    Struct(StructExpr<'a>),
    Array(ArrayLitExpr<'a>),
    Tuple(TupleExpr<'a>),
    Block(BlockExpr<'a>),
    For(ForExpr<'a>),
    While(WhileExpr<'a>),
    DoWhile(DoWhileExpr<'a>),
    Loop(LoopExpr<'a>),
    If(IfExpr<'a>),
    Match(MatchExpr<'a>),
}

#[derive(Debug)]
pub struct AccessExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    host: Box<Expr<'a>>,
    field: Ident<'a>,
}

#[derive(Debug)]
pub struct TypeBindExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    expr: Expr<'a>,
    bind_to: Type<'a>,
}

#[derive(Debug)]
pub struct PrefixOpExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    op: PrefixOp<'a>,
    expr: Box<Expr<'a>>,
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
pub struct LetExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pat: Pattern<'a>,
    ty: Option<Type<'a>>,
    expr: Option<Expr<'a>>,
}

#[derive(Debug)]
pub struct FnCallExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    func: Box<Expr<'a>>,
    generic_args: Option<GenericArgs<'a>>,
    args: StructFieldsExpr<'a>,
}

#[derive(Debug)]
pub struct StructExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    ty_name: Option<Path<'a>>,
    fields: Option<StructFieldsExpr<'a>>,
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types                                                                                   //
// * Ident                                                                                        //
// * StringLiteral                                                                                //
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

#[derive(Debug, Copy, Clone)]
pub struct Ident<'a> {
    pub(super) src: &'a Token<'a>,
    pub name: &'a str,
}

#[derive(Debug, Copy, Clone)]
pub struct StringLiteral<'a> {
    pub(super) src: &'a Token<'a>,
    // NOTE: currently, string literals cannot give this; a minor change to `crate::tokens` is
    // required
    pub value: &'a str,
}

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
pub struct PrefixOp<'a> {
    pub(super) src: TokenSlice<'a>,
    pub kind: PrefixOpKind,
}

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
    And,
    /// `||`
    Or,
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
    pub kind: PostfixOpKind,
}

#[derive(Debug)]
pub enum PostfixOpKind {
    /// `?`
    Try,
}

#[derive(Debug)]
pub struct StructFieldsExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    fields: Vec<(Ident<'a>, Option<Expr<'a>>)>,
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
