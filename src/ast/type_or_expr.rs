//! Parsing for places where we might either have a type *or* an expression

use super::*;
use crate::tokens::LiteralKind;

/// A wrapper type for [`TypeOrExpr`] parse results that might not be ambiguous
///
/// This type should be fairly self-explanatory. It's primarily returned from
/// [`TypeOrExpr::consume`], and more information about this class of types can be found there.
///
/// [`TypeOrExpr`]: enum.TypeOrExpr.html
/// [`TypeOrExpr::consume`]: enum.TypeOrExpr.html#method.consume
#[derive(Debug, Clone)]
pub enum MaybeTypeOrExpr<'a> {
    Type(Type<'a>),
    Expr(Expr<'a>),
    Ambiguous(TypeOrExpr<'a>),
}

/// A local helper type for handling the output of the individual parser functions
///
/// The core functionality that this provides is a method to convey the result. This is because in
/// most cases, if we find that something is *definitely* a type or *definitely* an expression, we
/// don't care about the actual value of that type or expression. In those cases, the entirety of
/// the information needed is the type of disambiguation because the recursive
enum Marker<T> {
    Type,
    Expr,
    Either(T),
}

impl<T> Marker<T> {
    fn map<S>(self, f: impl FnOnce(T) -> S) -> Marker<S> {
        use Marker::*;

        match self {
            Type => Type,
            Expr => Expr,
            Either(t) => Either(f(t)),
        }
    }
}

/// A piece of syntax that may either be a [type] or an [expression]
///
/// ## Definition
///
/// The rest of the documentation here serves to explain why we need this type, but this brief
/// header gives a quick summary of the BNF definition of the syntax for this type:
/// ```text
/// TypeOrExpr = Path                                                 ;; NamedTypeOrExpr
///            | "&" [ "mut" ] TypeOrExpr                             ;; RefTypeOrExpr
///            | "{" [ StructField { "," StructField } [ "," ] ] "}"  ;; StructTypeOrExpr
///            | "(" [ TypeOrExpr  { "," TypeOrExpr  } [ "," ] ] ")"  ;; TupleTypeOrExpr
///            | "[" TypeOrExpr "]" .                                 ;; ArrayTypeOrExpr
///
/// StructField = Ident ":" TypeOrExpr .     ;; Actually named `StructFieldTypeOrExpr`
/// ```
///
/// ## Reasoning
///
/// This only really comes up in parsing generics arguments, but it's absolutely crucial to store
/// that ambiguity somewhere. The primary reason that we need to handle this comes down to allowing
/// expressions and types in the same place in generics arguments. We can see this from the BNF
/// definition:
/// ```text
/// GenericsArg = [ Ident ":" ] Type
///             | [ Ident ":" ] Expr
///             | "ref" Expr .
/// ```
/// Both types and expressions are allowed after `[ Ident ":" ]`, so we must handle this ambiguity.
/// Here's a reference table of the particular ambiguities that generate each variant.
///
/// | Variant | Expression variant               | Type variant                       |
/// |---------|----------------------------------|------------------------------------|
/// | Named   | [`PostfixOp::Access`] (repeated) | [`NamedType`]                      |
/// | Ref     | [`PrefixOp::Ref`]                | [`RefType`] (optional [`MutType`]) |
/// | Tuple   | [`TupleExpr`]                    | [`TupleType`]                      |
/// | Struct  | [`BlockExpr`] (empty), [`StructExpr`] (all fields explicitly named) | [`StructType`] |
/// | Array   | [`ArrayExpr`] (single element)   | [`ArrayType`] (no length)          |
///
/// [type]: ../types/enum.Type.html
/// [expression]: ../expr/enum.Expr.html
#[derive(Debug, Clone)]
pub enum TypeOrExpr<'a> {
    Named(Path<'a>),
    Ref(RefTypeOrExpr<'a>),
    Tuple(TupleTypeOrExpr<'a>),
    Struct(StructTypeOrExpr<'a>),
    Array(ArrayTypeOrExpr<'a>),
}

/// An ambiguous reference type or expression
///
/// This type is represented by the following BNF:
/// ```text
/// RefTypeOrExpr = "&" [ "mut" ] TypeOrExpr .
/// ```
/// For more information, please refer to the documentation of [`TypeOrExpr`](enum.TypeOrExpr.html).
#[derive(Debug, Clone)]
pub struct RefTypeOrExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub ref_token: &'a Token<'a>,
    pub mut_token: Option<&'a Token<'a>>,
    pub value: Box<TypeOrExpr<'a>>,
}

/// An ambiguous tuple type or expression
///
/// This type is represented by the following BNF:
/// ```text
/// TupleTypeOrExpr = "(" [ TypeOrExpr { "," TypeOrExpr } [ "," ] ] ")" .
/// ```
/// For more information, please refer to the documentation of [`TypeOrExpr`](enum.TypeOrExpr.html).
#[derive(Debug, Clone)]
pub struct TupleTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub elements: Vec<TypeOrExpr<'a>>,
    pub poisoned: bool,
}

/// An ambiguous struct type or expression
///
/// This type is represented by the following BNF:
/// ```text
/// StructTypeOrExpr = "{" [ StructFieldTypeOrExpr { "," StructFieldTypeOrExpr } [ "," ] ] "}" .
/// ```
///
/// Please note that - in addition to *struct* types and expressions, this type may also represent
/// an empty block expression (i.e. with type `()` instead of `{}`). This must be respected by any
/// attempts to resolve the syntax of this type.
///
/// For more information, please refer to the documentation of [`TypeOrExpr`](enum.TypeOrExpr.html).
#[derive(Debug, Clone)]
pub struct StructTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub fields: Vec<StructFieldTypeOrExpr<'a>>,
    pub poisoned: bool,
}

/// A helper type for [`StructTypeOrExpr`](struct.StructTypeOrExpr.html)
#[derive(Debug, Clone)]
pub struct StructFieldTypeOrExpr<'a> {
    pub(super) src: TokenSlice<'a>,
    pub name: Ident<'a>,
    pub value: TypeOrExpr<'a>,
}

/// An ambiguous array type or expression
///
/// This type is represented by the following BNF:
/// ```text
/// ArrayTypeOrExpr = "[" TypeOrExpr "]" .
/// ```
///
/// If there was a critical error parsing the inside of the square brackets, the inner value may
/// not be present.
///
/// For more information, please refer to the documentation of [`TypeOrExpr`](enum.TypeOrExpr.html).
#[derive(Debug, Clone)]
pub struct ArrayTypeOrExpr<'a> {
    pub(super) src: &'a Token<'a>,
    pub value: Option<Box<TypeOrExpr<'a>>>,
    pub poisoned: bool,
}

impl<'a> TypeOrExpr<'a> {
    /// Consumes a type or expression as a prefix of the given tokens, subject to the provided set
    /// of expression restrictions
    ///
    /// This function makes no assumptions about its input
    pub fn consume(
        tokens: TokenSlice<'a>,
        expr_delim: ExprDelim,
        restrictions: Restrictions,
        type_ctx: TypeContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<MaybeTypeOrExpr<'a>, Option<usize>> {
        let mut local_errors = Vec::new();
        let marker = TypeOrExpr::marker_consume(
            tokens,
            expr_delim,
            restrictions,
            ends_early,
            containing_token,
            &mut local_errors,
        )?;

        match marker {
            Marker::Either(t) => {
                errors.extend(local_errors);
                Ok(MaybeTypeOrExpr::Ambiguous(t))
            }
            Marker::Expr => {
                return Expr::consume(
                    tokens,
                    expr_delim,
                    restrictions,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(MaybeTypeOrExpr::Expr)
            }
            Marker::Type => {
                return Type::consume(
                    tokens,
                    type_ctx,
                    restrictions,
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(MaybeTypeOrExpr::Type)
            }
        }
    }

    /// A version of [`TypeOrExpr::consume`] that instead returns a [`Marker<TypeOrExpr>`], so that
    /// we avoid double-parsing.
    ///
    /// [`TypeOrExpr::consume`]: #method.consume
    /// [`Marker<TypeOrExpr>`]: enum.Marker.html
    fn marker_consume(
        tokens: TokenSlice<'a>,
        expr_delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Marker<TypeOrExpr<'a>>, Option<usize>> {
        make_expect!(tokens, 0, ends_early, containing_token, errors);

        let maybe_expr;
        let maybe_type;

        let fst_token = expect!((
            Ok(t),
            _ if {
                maybe_expr = Expr::is_starting_token(t);
                maybe_type = Type::is_starting_token(t);
                maybe_expr || maybe_type
            } => t,
            @else(return None) => ExpectedKind::TypeOrExpr,
        ));

        if maybe_expr && !maybe_type {
            return Ok(Marker::Expr);
        } else if maybe_type && !maybe_expr {
            return Ok(Marker::Type);
        }

        let marker = match &fst_token.kind {
            TokenKind::Ident(_) => {
                TypeOrExpr::consume_path(tokens, expr_delim, ends_early, containing_token, errors)?
                    .map(TypeOrExpr::Named)
            }
            TokenKind::Punctuation(Punc::And) => RefTypeOrExpr::consume(
                tokens,
                expr_delim,
                restrictions,
                ends_early,
                containing_token,
                errors,
            )?
            .map(TypeOrExpr::Ref),
            TokenKind::Tree {
                delim: Delim::Parens,
                inner,
                ..
            } => TupleTypeOrExpr::parse(fst_token, inner, errors).map(TypeOrExpr::Tuple),
            TokenKind::Tree {
                delim: Delim::Curlies,
                inner,
                ..
            } => StructTypeOrExpr::parse(fst_token, inner, errors).map(TypeOrExpr::Struct),
            TokenKind::Tree {
                delim: Delim::Squares,
                inner,
                ..
            } => ArrayTypeOrExpr::parse(fst_token, inner, errors).map(TypeOrExpr::Array),

            // We should have had one of the above tokens guaranteed by the original match
            // statement
            k => panic!(
                "expected starting token valid as `TypeOrExpr`, found {:?}",
                k
            ),
        };

        // After parsing the initial piece, if we've already dismabiguated, we'll return that:
        let type_or_expr = match marker {
            Marker::Type => return Ok(Marker::Type),
            Marker::Expr => return Ok(Marker::Expr),
            Marker::Either(t) => t,
        };

        // If we haven't disambiguated, we need to account for the the set of tokens that are
        // allowed to follow this initial ambiguity:
        let consumed = type_or_expr.consumed();
        let next_token = match tokens.get(consumed) {
            None | Some(Err(_)) => return Ok(Marker::Either(type_or_expr)),
            Some(Ok(t)) => t,
        };

        let continue_expr = Expr::can_continue_with(&tokens[consumed..], restrictions);
        let continue_type = type_or_expr.can_continue_type(next_token);

        if !continue_expr && !continue_type {
            return Ok(Marker::Either(type_or_expr));
        } else if continue_expr && !continue_type {
            return Ok(Marker::Expr);
        } else if continue_type && !continue_expr {
            return Ok(Marker::Type);
        }

        // If we get here, we know that both `continue_expr` and `continue_type` are true. This
        // really only applies for a single token: `|`. Pipes can be used to indicate refinements
        // for types *and* as bitwise or for expressions.
        //
        // We don't need to double-check that it's a pipe, because
        // `Refinements::consume_if_not_expr` will panic for us if given invalid input.
        let maybe_refs: Option<Refinements> = Refinements::consume_if_not_expr(
            &tokens[consumed..],
            expr_delim,
            restrictions,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        // If we did have refinements then this must be a type!
        // Otherwise, the pipe must have been an expression
        match maybe_refs {
            Some(_) => return Ok(Marker::Type),
            None => return Ok(Marker::Expr),
        }
    }

    /// Consumes a path as part of a piece of syntax that may be either an expression or a type
    ///
    /// This function assumes that the first token is an identifier, and will panic if this is not
    /// the case. It does not, however, assume that angle brackets *must* constitute generics
    /// arguments.
    fn consume_path(
        tokens: TokenSlice<'a>,
        expr_delim: ExprDelim,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Marker<Path<'a>>, Option<usize>> {
        let base =
            Expr::consume_path_component(tokens, expr_delim, ends_early, containing_token, errors)?;

        let mut consumed = base.consumed();
        let mut components = vec![base];

        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        while let Some(TokenKind::Punctuation(Punc::Dot)) = kind!(tokens)(consumed) {
            consumed += 1;

            // After the dot, we're expecting either an identifier or an integer literal - for
            // field access (or paths) vs. tuple element access
            expect!((
                Ok(_),
                TokenKind::Ident(_) => (),
                TokenKind::Literal(_, LiteralKind::Int) => return Ok(Marker::Expr),
                @else(return Some) => ExpectedKind::TypeOrExprFollowDot,
            ));

            // If we got here, we had an identifier; we'll consume the next component
            let next = Expr::consume_path_component(
                &tokens[consumed..],
                expr_delim,
                ends_early,
                containing_token,
                errors,
            )
            .map_err(p!(Some(c) => Some(c + consumed)))?;

            consumed += next.consumed();
            components.push(next);
        }

        Ok(Marker::Either(Path {
            src: &tokens[..consumed],
            components,
        }))
    }

    /// Returns whether the given token can continue the `TypeOrExpr` given
    ///
    /// This returns true only if the token is a pipe (`|` - for refinements) *and* the would-be
    /// type is a variant that allows trailing refinements (which is true only for named types,
    /// arrays, and references to these types).
    fn can_continue_type(&self, token: &Token) -> bool {
        fn allows_trailing(either: &TypeOrExpr) -> bool {
            match either {
                TypeOrExpr::Named(_) | TypeOrExpr::Array(_) => true,
                TypeOrExpr::Ref(r) => allows_trailing(&r.value),
                _ => false,
            }
        }

        match &token.kind {
            TokenKind::Punctuation(Punc::Or) if allows_trailing(self) => true,
            _ => false,
        }
    }
}

impl<'a> RefTypeOrExpr<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        expr_delim: ExprDelim,
        restrictions: Restrictions,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Marker<RefTypeOrExpr<'a>>, Option<usize>> {
        // Here's the bnf for reference types and reference expressions:
        //   RefType = "&" [ Refinements ] Type .
        //        -> = "&" [ Refinements ] [ [ "!" ] "mut" ] Type .
        //   RefExpr = "&" [ "mut" ] Expr .
        // For the second definition of `RefType`, we've substituted in the definition of `MutType`
        // to additionally highlight the ambiguity with "mut".

        let ref_token = assert_token!(
            tokens.first() => "ampersand (`&`)",
            Ok(t) && TokenKind::Punctuation(Punc::And) => t,
        );

        let mut consumed = 1;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        // From the specification above, we can deduce the set of tokens that are allowed
        // immediately following the reference:
        //   "|"       -> TYPE (implies refinements) (NOTE: May conlfict with closures later!)
        //   "!" "mut" -> TYPE
        //   "!"   t, where t can start an expression -> EXPRESSION
        //   "!"   _   -> Error!
        //   "mut"     -> AMBIGUOUS
        //   t, where t can start an expression or type -> AMBIGUOUS
        //   _         -> Error!
        let mut maybe_expr = false;
        let mut maybe_type = false;

        let mut_token = expect!((
            Ok(t),
            TokenKind::Punctuation(Punc::Or) => return Ok(Marker::Type),
            TokenKind::Punctuation(Punc::Not) => {
                consumed += 1;
                expect!((
                    Ok(snd),
                    TokenKind::Keyword(Kwd::Mut) => return Ok(Marker::Type),
                    _ if Expr::is_starting_token(snd) => return Ok(Marker::Expr),
                    @else(return None) => ExpectedKind::TypeOrExprFollowRefNot,
                ));
            },
            TokenKind::Keyword(Kwd::Mut) => Some(t),
            _ if {
                maybe_expr = Expr::is_starting_token(t);
                maybe_type = Type::is_starting_token(t);
                maybe_expr || maybe_type
            } => None,
            @else(return None) => ExpectedKind::TypeOrExprFollowRef,
        ));

        consumed += 1;

        // We only set the values of `maybe_expr` and `maybe_type` above if we *don't* find the
        // keyword "mut".
        if mut_token.is_some() {
            expect!((
                Ok(t),
                _ if {
                    maybe_expr = Expr::is_starting_token(t);
                    maybe_type = Type::is_starting_token(t);
                    maybe_expr || maybe_type
                } => (),
                @else(return None) => ExpectedKind::TypeOrExpr,
            ));
        }

        debug_assert!(maybe_expr || maybe_type);

        // If there's definitely either an expression or type, we'll indicate as such by returning
        // early.
        if maybe_expr && !maybe_type {
            return Ok(Marker::Expr);
        } else if maybe_type && !maybe_expr {
            return Ok(Marker::Type);
        }

        // Otherwise, we parse as ambiguous and return
        let marker_value = TypeOrExpr::marker_consume(
            &tokens[consumed..],
            expr_delim,
            restrictions,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        match marker_value {
            Marker::Type => Ok(Marker::Type),
            Marker::Expr => Ok(Marker::Expr),
            Marker::Either(value) => {
                consumed += value.consumed();

                Ok(Marker::Either(RefTypeOrExpr {
                    src: &tokens[..consumed],
                    ref_token,
                    mut_token,
                    value: Box::new(value),
                }))
            }
        }
    }
}

impl<'a> TupleTypeOrExpr<'a> {
    /// Parses the entire input as a tuple type or expression
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Marker<TupleTypeOrExpr<'a>> {
        // Tuple types and expressions are both represented by the following BNF:
        //   "(" [ E { "," E } [ "," ] ] ")"
        // for some element `E`. Individually, exprssions have `E = Expr`, and types have
        // `E = [ Vis ] Type`.
        //
        // From this, parsing each element is fairly simple: if we find a visibility modifier,
        // we're definitely looking at a type. Otherwise, we delgate parsing the element to
        // `TypeOrExpr::marker_consume`.

        let ends_early = false;

        let mut consumed = 0;
        let mut elements = Vec::new();
        let mut poisoned = false;

        make_expect!(inner, consumed, ends_early, Some(src), errors);

        while consumed < inner.len() {
            if let Some(_) = Vis::try_consume(&inner[consumed..]) {
                return Marker::Type;
            }

            let res = TypeOrExpr::marker_consume(
                &inner[consumed..],
                ExprDelim::Comma,
                Restrictions::default(),
                ends_early,
                Some(src),
                errors,
            );

            match res {
                Err(Some(c)) => {
                    poisoned = true;
                    consumed += c;
                }
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Ok(Marker::Type) => return Marker::Type,
                Ok(Marker::Expr) => return Marker::Expr,
                Ok(Marker::Either(e)) => {
                    consumed += e.consumed();
                    elements.push(e);
                }
            }

            if consumed < inner.len() {
                expect!((
                    Ok(_),
                    TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                    _ if poisoned => break,
                    @else { poisoned = true; break } => ExpectedKind::TupleTypeOrExprComma,
                ));
            }
        }

        Marker::Either(TupleTypeOrExpr {
            src,
            elements,
            poisoned,
        })
    }
}

impl<'a> StructTypeOrExpr<'a> {
    /// Parses the entire input as a struct type or expression
    ///
    /// Note that block expressions *are* included as able to be parsed here.
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Marker<StructTypeOrExpr<'a>> {
        // Because we need to explicitly account for block expressions, we have a bit of a challenge
        // in parsing here. For convenience, we'll repeat the BNF definitions of each of the
        // relevant syntax constructs.
        //
        // StructType = "{" [ StructTypeField { "," StructTypeField } [ "," ] ] "}" .
        // -> StructTypeField = [ Vis ] Ident ":" Type [ "=" Expr ] .
        //                              ^^^^^ ^^^ ^^^^
        // StructExpr = "{" [ StructFieldExpr { "," StructFieldExpr } [ "," ] ] "}" .
        // -> StructFieldExpr = Ident [ ":" Expr* ] .
        //                      ^^^^^   ^^^ ^^^^
        // BlockExpr = "{" { Stmt } [ Expr ] "}" .
        //   -> Stmt = BigExpr
        //           | Expr ";"
        //             ^^^^ Conflicts through leading identifiers
        //           | Item .
        //             ^^^^ Conflicts via visibility qualifiers
        //
        // So there's essentially two types of conflicts we can run into here:
        //   1. Initial conflicts - i.e. resolving whether it's a block expression or a struct-like
        //      thing.
        //   2. Continual conflicts - ambiguity that can occur for each field in the struct.
        //
        // The first kind is unfortunately complex. We'll go through that in a moment.
        //
        // The second kind, however, is much nicer: if we find a visibility qualifier, it must be a
        // type. An identifier without a trailing colon implies that we have a struct *expression*.
        // Because of the restrictions on parsing struct field expressions (i.e. they cannot contain
        // assignment), if we find `Ident ":" TypeOrExpr "=" ..`, it must a struct type with default
        // values.
        //
        // As it stands, parsing individual fields is handled separately; this function still
        // remains the place where the overarching method is described
        //
        // In any case, with that out of the way, we'll continue. At the start of the block, we're
        // expecting any of:
        //  * Item
        //  * Expr
        //  * [ Vis ] Ident ( "," | ":" | "" )
        // Items may optionally start with visibility qualifiers, but have no way of an identifier
        // following that. Expressions may start with identifiers, but that identifier cannot be
        // followed by commas or colons. Additionally, if we have just `"{" Ident "}"` or if the
        // inner tokens is empty, then we have an `AmbiguousBlockExpr` (but an expression
        // nonetheless).

        macro_rules! return_empty {
            (poisoned = $p:expr) => {{
                return Marker::Either(StructTypeOrExpr {
                    src,
                    fields: Vec::new(),
                    poisoned: $p,
                });
            }};
        }

        let ends_early = false;
        let mut consumed = 0;

        make_expect!(inner, consumed, ends_early, Some(src), errors);

        // First up: If we find a visibility qualifier, we know it's either a block expression
        // starting with an item or a type:
        let start_vis = Vis::try_consume(inner);

        if start_vis.is_some() {
            consumed += start_vis.consumed();

            expect!((
                Ok(t),
                TokenKind::Ident(_) => return Marker::Type,
                _ if Item::can_follow_vis(t) => return Marker::Expr,
                @else { return_empty!(poisoned = true) } => ExpectedKind::StructTypeFieldOrItem,
            ));
        }

        // If there aren't *any* tokens here, we immediately know it's ambiguous (see above note
        // about empty contents)
        if inner.is_empty() {
            return_empty!(poisoned = false);
        }

        // Otherwise, because we didn't find a visibility qualifier, we'll match on the next tokens.
        //
        // From above, we know that we require an identifier *or* any token that may start an
        // expression or item.
        assert!(consumed == 0); // This assertion is just for forwards-compatability with constants here
        expect!((
            Ok(fst),
            TokenKind::Ident(_) => {
                // There's essentially three ways we can interpret this identifier:
                //   1. As the start of an expression
                //   2. As a struct *expression* field name
                //   3. As a struct *type* field name
                // Differentiating between (2) and (3) is fully handled later (in parsing each
                // ambiguous field), so we really only care about the differences between what's
                // allowed to follow (1) vs (2/3):
                //   (1):   Any tokens `ts` where `Expr::can_follow_ident(ts)`
                //   (2/3): Any of: ":", ",", or nothing.
                // With that out of the way, we'll actually do the processing.
                if inner.len() <= 1 {
                    // "{" Ident "}" is an `AmbiguousBlockExpr` -- i.e. an expression
                    return Marker::Expr;
                } else {
                    match kind!(inner)(1) {
                        // Because `inner.len() > 1`, we know this must have been a tokenizer
                        // error; no point generating another error here.
                        None => return_empty!(poisoned = true),
                        // `Ident ":"` is still ambiguous - this is the only case that we'll
                        // continue with
                        Some(TokenKind::Punctuation(Punc::Colon)) => (),
                        // `Ident ","` must be a struct expression
                        Some(TokenKind::Punctuation(Punc::Comma)) => return Marker::Expr,
                        // Discussed above:
                        Some(_) if Expr::can_follow_ident(&inner[1..]) => return Marker::Expr,
                        // And finally, the error case
                        Some(_) => {
                            errors.push(Error::Expected {
                                kind: ExpectedKind::StructTypeOrExprFollowIdent,
                                found: (&inner[1]).into(),
                            });

                            return_empty!(poisoned = true);
                        }
                    }
                }
            },
            _ if Expr::is_starting_token(fst) || Item::is_starting_token(fst) => return Marker::Expr,
            @else { return_empty!(poisoned = true) } => ExpectedKind::StructTypeOrExprInner,
        ));

        // If we get to this point, we have a token list that starts with `Ident ":"`. We'll loop
        // through and collect all of the fields, unless one is clearly a type or expression.

        let mut fields = Vec::new();
        let mut poisoned = false;
        consumed = 0; // reset consumed so we start at the beginning of a field

        while consumed < inner.len() {
            let field_res =
                StructFieldTypeOrExpr::consume(&inner[consumed..], ends_early, Some(src), errors);

            match field_res {
                Ok(Marker::Type) => return Marker::Type,
                Ok(Marker::Expr) => return Marker::Expr,
                Err(None) => {
                    poisoned = true;
                    break;
                }
                Err(Some(c)) => {
                    consumed += c;
                    poisoned = true;
                }
                Ok(Marker::Either(field)) => {
                    consumed += field.consumed();
                    fields.push(field);
                }
            }

            // We expect commas between struct fields, but if we were already poisoned, we might be
            // misinterpreting.
            expect!((
                Ok(_),
                TokenKind::Punctuation(Punc::Comma) => consumed += 1,
                _ if poisoned => break,
                @else { poisoned = true; break } => ExpectedKind::StructTypeOrExprComma,
            ));
        }

        Marker::Either(StructTypeOrExpr {
            src,
            fields,
            poisoned,
        })
    }
}

impl<'a> StructFieldTypeOrExpr<'a> {
    /// Consumes a single field of a struct that may either correspond to a type or an expression
    fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Marker<StructFieldTypeOrExpr<'a>>, Option<usize>> {
        // There's a lot that this function needs to handle that might not be immediately obvious.
        // Because *all* of the syntactical expression available both by struct *types* and struct
        // *expressions* must be correctly parsed here, we end up with a lot more to handle than
        // just the constructs that make it into the definition of `StructFieldTypeOrExpr`.
        //
        // The simplest way to view this is perhaps with a direct comparison of the BNFs that we're
        // parsing (with names altered):
        //   TypeField = [ Vis ] Ident   ":" Type [ "=" Expr ] .
        //   ExprField =         Ident [ ":" Expr* ] .
        // Note that the `Expr*` in the expression's version of the struct field explicitly
        // disallows assignment operations, which allows us to make some of the assumptions that we
        // need in order to efficiently parse this.
        //
        // So: The first thing we need to do is to try to parse a visibility qualifier:
        if Vis::try_consume(tokens).is_some() {
            // If there *was* a visibility qualifier, this must have been a type field:
            return Ok(Marker::Type);
        }

        let mut consumed = 0;
        make_expect!(tokens, consumed, ends_early, containing_token, errors);

        // Otherwise, we're expecting an identifier:
        let name = expect!((
            Ok(src),
            TokenKind::Ident(name) => Ident { src, name },
            @else(return None) => ExpectedKind::StructTypeOrExprFieldNameOrVis,
        ));

        consumed += 1;

        // (Somewhat repeated from within `StructTypeOrExpr::parse`)
        //
        // After the identifier, we're allowed to have any of ":", ",", or the end of the input. If
        // the input ends - or we find "," - the field is for a struct *expression*. Otherwise, it
        // remains ambiguous.
        assert!(consumed == 1);
        if tokens.len() <= consumed {
            return Ok(Marker::Expr);
        }

        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Comma) => return Ok(Marker::Expr),
            TokenKind::Punctuation(Punc::Colon) => consumed += 1,
            @else(return None) => ExpectedKind::StructTypeOrExprFollowFieldIdent,
        ));

        // After the colon, we're expecting a type or expression.
        //
        // From the documentation for `StructExpr`, we can see that the expression cannot include
        // assignment.
        let marker = TypeOrExpr::marker_consume(
            &tokens[consumed..],
            ExprDelim::StructFields,
            Restrictions::default().no_assignment(),
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        let value = match marker {
            Marker::Type => return Ok(Marker::Type),
            Marker::Expr => return Ok(Marker::Expr),
            Marker::Either(t) => {
                consumed += t.consumed();
                t
            }
        };

        // After the `TypeOrExpr`, there's again a couple options. If this were a struct *type*, we
        // could optionally have an equals. Otherwise, we'll assume that this is the end (leaving
        // the caller to handle any errors).
        if let Some(TokenKind::Punctuation(Punc::Eq)) = kind!(tokens)(consumed) {
            return Ok(Marker::Type);
        }

        Ok(Marker::Either(StructFieldTypeOrExpr {
            src: &tokens[..consumed],
            name,
            value,
        }))
    }
}

impl<'a> ArrayTypeOrExpr<'a> {
    /// Parses the entire input as an array type or expression
    fn parse(
        src: &'a Token<'a>,
        inner: TokenSlice<'a>,
        errors: &mut Vec<Error<'a>>,
    ) -> Marker<ArrayTypeOrExpr<'a>> {
        let ends_early = false;

        // The ambiguous overlap between array types and expressions is only a single-element
        // array. We can see this from a comparison of the BNFs:
        //   ArrayType = "["   Type [ ";" Expr ]         "]" .
        //                     ^^^^
        //   ArrayExpr = "[" [ Expr { "," Expr } [ "," ] "]" .
        //                     ^^^^
        // Because the ambiguity only persists when there's a single element, there's a lot of
        // pieces that we need to handle that *aren't reflected in the definition of
        // `ArrayTypeOrExpr`. Thankfully, this function isn't *too* complex, so an inline
        // explanation should suffice.

        // To start with, an empty array is only valid as an expression:
        if inner.is_empty() {
            return Marker::Expr;
        }

        // Otherwise, we *must* parse a `TypeOrExpr`:
        let res = TypeOrExpr::marker_consume(
            inner,
            // We give 'commas' as our delimiter, because it's *possible* for that to be the case
            ExprDelim::Comma,
            Restrictions::default(),
            ends_early,
            Some(src),
            errors,
        );

        let value = match res {
            Ok(Marker::Expr) => return Marker::Expr,
            Ok(Marker::Type) => return Marker::Type,
            Err(_) => {
                return Marker::Either(ArrayTypeOrExpr {
                    src,
                    value: None,
                    poisoned: true,
                })
            }
            Ok(Marker::Either(v)) => v,
        };

        // If that TypeOrExpr was ambiguous AND there aren't more tokens, we have the only
        // ambiguous success case. As we can see from the documentation for this type, the BNF is
        // defined as exactly `"[" TypeOrExpr "]"`, which is what we have here.
        if inner.len() <= value.consumed() {
            return Marker::Either(ArrayTypeOrExpr {
                src,
                value: Some(Box::new(value)),
                poisoned: false,
            });
        }

        // Otherwise, there's only two tokens that are allowed to follow here - they also happen to
        // fully disambiguate here.
        make_expect!(inner, value.consumed(), ends_early, Some(src), errors);
        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Comma) => Marker::Expr,
            // As it stands, only array types can specify the length with a semicolon
            TokenKind::Punctuation(Punc::Semi) => Marker::Type,
            @else { return Marker::Either(ArrayTypeOrExpr {
                src,
                value: Some(Box::new(value)),
                poisoned: true,
            }) } => ExpectedKind::ArrayTypeOrExprCommaOrSemi,
        ))
    }
}
