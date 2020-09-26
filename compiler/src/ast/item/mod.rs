//! `Item` parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;
use crate::files::{FileInfo, Span};
use arc_offset::ArcOffset;

// And all of the submodules here are really just for code organization; we want them all to exist
// (and be documented) under the single `ast::item` namespace.
//
// The contents of *this* module are for all of the individual shared components that don't really
// belong to a *single* item and aren't so significant to warrant their own submodule.
mod const_static;
mod fndecl;
mod genericsparams;
mod implblock;
mod import_use;
mod macrodef;
mod proofstmts;
mod traitdef;
mod typedecl;

pub use self::{
    const_static::*, fndecl::*, genericsparams::*, implblock::*, import_use::*, macrodef::*,
    proofstmts::*, traitdef::*, typedecl::*,
};

#[derive(Debug, Clone, ArcOffset, Consumed)]
pub enum Item {
    Fn(FnDecl),
    Macro(MacroDef),
    Type(TypeDecl),
    Trait(TraitDef),
    Impl(ImplBlock),
    Const(ConstStmt),
    Static(StaticStmt),
    Import(ImportStmt),
    Use(UseStmt),
}

pub type ArcFnItem = ArcOffset<Item, FnDecl>;
pub type ArcMacroItem = ArcOffset<Item, MacroDef>;
pub type ArcTypeItem = ArcOffset<Item, TypeDecl>;
pub type ArcTraitItem = ArcOffset<Item, TraitDef>;
pub type ArcImplItem = ArcOffset<Item, ImplBlock>;
pub type ArcConstItem = ArcOffset<Item, ConstStmt>;
pub type ArcStaticItem = ArcOffset<Item, StaticStmt>;
pub type ArcImportItem = ArcOffset<Item, ImportStmt>;
pub type ArcUseItem = ArcOffset<Item, UseStmt>;

/// A specific enum for handling item parsing failure
///
/// Unlike other constructs, [`Item`]s are very likely to be unable to indicate where to start next
/// if their parsing fails. This type serves to give extra meaning to the error type returned for
/// item parsing, simply by virtue of wrapping the value.
#[derive(Debug, Copy, Clone)]
pub(super) struct ItemParseErr {
    /// The number of tokens that were consumed in the process of parsing the item, before the
    /// error occured.
    pub consumed: usize,
}

/// Visibility qualifiers for [`Item`](enum.Item.html)s
///
/// Currently there is a single variant ("pub") - this may be subject to change in the future.
#[derive(Debug, Clone, Consumed)]
pub enum Vis {
    #[consumed(1)]
    Pub { src: Span },
}

/// A helper type for concrete, possibly bounded types, with optional default values
///
/// This type is purely represented by the following BNF:
/// ```text
/// Field = Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ] .
/// ```
///
/// It is used in multiple places - namely [`const`] and [`static`] statments, [function
/// parameters], and [const generic parameters]. In each of these, the meaning is the same: a field
/// gives a name, the type (or the restrictions on a type), and an optional default value.
///
/// The full set of options expressable by a field are not always valid in all contexts; this is
/// hanlded after parse-time, during validation of the AST.
#[derive(Debug, Clone, Consumed)]
pub struct Field {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub name: Ident,
    #[consumed(@ignore)]
    pub bound_src: Span,
    pub bound: FieldBound,
    #[consumed(value.as_ref().map(|v| v.consumed() + 1).unwrap_or(0))]
    // +1 to account for the leading "+"
    pub value: Option<Expr>,
}

/// The types of bounds on a type for a [`Field`]; A helper type for [`Field`]
///
/// This type is represented simply by the following BNF:
/// ```text
/// FieldBound = ( ":" Type | "::" TypeBound ) .
/// ```
///
/// The source for this type is not stored here, but returned alongside a `FieldBound` in the
/// dedicated [parsing function]. For more information, please refer to the documentation of
/// [`Field`].
///
/// [`Field`]: struct.Field.html
/// [parsing function]: #method.consume
#[derive(Debug, Clone, Consumed)]
pub enum FieldBound {
    #[consumed(_0.consumed() + 1)] // +1 for the leading ":"
    Type(Type),
    #[consumed(_0.consumed() + 1)] // +1 for the leading "::"
    TypeBound(TypeBound),
}

/// Bounds on a type; refinements and trait bounds
///
/// Type bounds are entirely concerned with limiting the class of inputs that may be used as
/// generic type parameters. These are defined by the following BNF production rule:
/// ```text
/// TypeBound = [ Refinements ] Trait { "+" Trait } .
/// ```
/// Note that here, `Trait`s are defined as exactly equal to [`Path`]s.
#[derive(Debug, Clone, Consumed)]
pub struct TypeBound {
    #[consumed(@ignore)]
    pub(super) src: Span,
    pub refinements: Option<Refinements>,

    // we need to factor in the "+" between traits
    #[consumed(traits.consumed() + traits.len() - 1)]
    pub traits: Vec<Path>,
}

impl Item {
    /// Consumes an `Item` as a prefix of the tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Item, ItemParseErr> {
        // Per the BNF, most of the items present can have preceeding proof lines, so we'll consume
        // whatever proof lines might be at the beginning of the list of tokens beforehand. If we
        // do find proof lines, there's a limited set of items that we would be expecting.
        //
        // If we can't find one of the items that accepts proof lines, we'll emit an error and see
        // if there's some other item that we can parse it as (i.e. the user put proof statments
        // where they shouldn't have) - OR if we can't parse another item, we'll try to recover and
        // give the position where parsing can resume.
        //
        // We'll only indicate that parsing must stop completely if one of the given tokens was an
        // error - if this happens, it's very difficult to accurately recover (primarily because
        // tokenizer errors are usually due to mismatched or unclosed delimeters).
        let mut proof_stmts = None;
        let mut consumed = 0;
        if let Some(TokenKind::ProofLines(inner)) = kind!(tokens)(0) {
            let src = tokens[0].as_ref().unwrap();
            proof_stmts = Some(ProofStmts::parse(file, src, inner, errors));
            consumed += 1;
        }

        let proof_stmts_consumed = consumed;
        let has_proof_stmts = consumed != 0;

        // From this point, we'll switch based on the items that we *could* parse.
        //
        // There's a couple that we can only ahve if there weren't proof statements - we'll always
        // check those, though, instead opting for better error messages when they aren't there.
        //
        // We can apply similar logic to visibility qualifiers - again, some `Item`s cannot be
        // preceeded by them, but we'll still check anyways.
        //
        // The full list of `Item`s we can try are given by the following table, which indicates
        // the variants that support proof lines or visibility qualifiers
        //     ┌────────────┬─────────┬───────┐
        //     │ Item type  │ Proof ? │ Vis ? │
        //     ├────────────┼─────────┼───────┤
        //     │ FnDecl     │   Yes   │  Yes  │
        //     │ MacroDef   │   Yes   │  Yes  │
        //     │ TypeDecl   │   Yes   │  Yes  │
        //     │ TraitDef   │   Yes   │  Yes  │
        //     │ ImplBlock  │   No    │  No   │
        //     │ ConstStmt  │   No    │  Yes  │
        //     │ StaticStmt │   Yes   │  Yes  │
        //     │ ImportStmt │   No    │  No   │
        //     │ UseStmt    │   No    │  Yes  │
        //     └────────────┴─────────┴───────┘
        // Because these are essentially all given by leading keywords, we'll just switch based on
        // that - after consuming an optional visibility qualifier. We'll generate an error if the
        // visibility qualifier wasn't allowed.

        let vis = Vis::try_consume(file, &tokens[consumed..]);
        consumed += vis.consumed();

        // We'll get the next token, which *should* be one of a few different keywords. If it isn't, we'll indicate an
        // error and return the number of tokens we've consumed.

        use Kwd::*;

        static ITEM_KWDS: &[Kwd] = &[
            Pure, Fn, Macro, Type, Trait, Impl, Const, Static, Import, Use,
        ];

        make_expect!(file, tokens, consumed, ends_early, containing_token, errors);

        let (fst, kwd) = expect!((
            Ok(fst),
            TokenKind::Keyword(k) if ITEM_KWDS.contains(&k) => (fst, k),
            @else { return Err(ItemParseErr { consumed }) } => ExpectedKind::ItemKwd(ITEM_KWDS),
        ));

        // From this point on, we know what we need to parse as - unless the keyword was "const",
        // which can either be part of a `ConstStmt` or an `FnDecl`.
        //
        // `FnDecl`s must have [ "pure" ] "fn" following "const", and `ConstStmt`s must have an
        // identifier.
        //
        // We'll set up a couple macros to make this a little cleaner. The first is `consume`,
        // which provides a small wrapper around the various associated `consume` functions for
        // certain types. This allows us to make what's going on a little bit more dense.
        macro_rules! consume {
            (
                $base_ty:ident,
                $item_kind:expr
                $(, @tokens: $tokens:expr)?
                $(, @consumed: $consumed:expr)?
                $(, $args:expr)* $(,)?
            ) => {
                $base_ty::consume(
                    file,
                    consume!(@tokens $($tokens)?),
                    consume!(@consumed $($consumed)?),
                    ends_early,
                    containing_token,
                    errors,
                    $($args,)*
                ).map($item_kind)
            };

            (@tokens) => {{ tokens }};
            (@tokens $ts:expr) => {{ $ts }};
            (@consumed) => {{ consumed + 1 }};
            (@consumed $cs:expr) => {{ $cs }};
        }

        // And then we have `disallow` - A helper macro for producing an error if some pieces
        // preceeded an item that weren't allowed there - either a visibility qualifier or proof
        // statements.
        macro_rules! disallow {
            (@Vis, $res:expr, $item_kind:ident) => {
                // Generally, we only want to produce an error if we know that the item itself was
                // successfully parsed - otherwise, we might be misinterpreting what the user meant
                // that item to be (and so this error would be unhelpful).
                if $res.is_ok() {
                    if let Some(vis) = vis {
                        errors.push(Error::VisDisallowedBeforeItem {
                            vis: vis.span(),
                            item_kind: errors::ItemKind::$item_kind,
                        });
                    }
                }
            };

            (@Proof, $res:expr, $item_kind:ident) => {
                if $res.is_ok() && has_proof_stmts {
                    errors.push(Error::ProofStmtsDisallowedBeforeItem {
                        stmts: Source::slice_span(file, &tokens[..proof_stmts_consumed]),
                        item_kind: errors::ItemKind::$item_kind,
                    });
                }
            };
        }

        match kwd {
            Macro => consume!(MacroDef, Item::Macro, proof_stmts, vis),
            Type => consume!(TypeDecl, Item::Type, proof_stmts, vis),
            Trait => consume!(TraitDef, Item::Trait, proof_stmts, vis),
            Impl => {
                let res = ImplBlock::consume(
                    file,
                    &tokens[consumed..],
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Item::Impl);

                disallow!(@Vis, res, ImplBlock);
                disallow!(@Proof, res, ImplBlock);
                res
            }
            Static => consume!(StaticStmt, Item::Static, proof_stmts, vis),
            Import => {
                let res = ImportStmt::consume(
                    file,
                    &tokens[consumed..],
                    ends_early,
                    containing_token,
                    errors,
                )
                .map(Item::Import);

                disallow!(@Vis, res, ImportStmt);
                disallow!(@Proof, res, ImportStmt);
                res
            }
            Use => {
                let res = consume!(UseStmt, Item::Use, vis);
                disallow!(@Proof, res, UseStmt);
                res
            }
            Fn => consume!(
                FnDecl,
                Item::Fn,
                proof_stmts,
                proof_stmts_consumed,
                vis,
                None,
                None
            ),

            // Const is a special case, as given above
            Const => {
                // Mark the 'const' token as already consumed
                consumed += 1;
                let is_const = Some(fst);

                expect!((
                    Ok(snd),
                    // As noted above, this is a constant statement.
                    TokenKind::Ident(_) => {
                        let res = consume!(
                            ConstStmt,
                            Item::Const,
                            @tokens: &tokens[proof_stmts_consumed..],
                            @consumed: consumed - proof_stmts_consumed,
                            vis
                        );

                        disallow!(@Proof, res, Const);
                        res
                    },
                    TokenKind::Keyword(Fn) => consume!(
                        FnDecl,
                        Item::Fn,
                        proof_stmts,
                        proof_stmts_consumed,
                        vis,
                        is_const,
                        None
                    ),
                    TokenKind::Keyword(Pure) => {
                        // If we encounter a "pure", there's unfortunately *one* last check that we
                        // need to do. We *still* need to make sure that the next token is an "fn"
                        // keyword, so we'll do that now. There's a dedicated error for this one as
                        // well.
                        consumed += 1;
                        let is_pure = Some(snd);

                        expect!((
                            Ok(_),
                            TokenKind::Keyword(Fn) => consume!(
                                FnDecl,
                                Item::Fn,
                                proof_stmts,
                                proof_stmts_consumed,
                                vis,
                                is_const,
                                is_pure
                            ),
                            @else { return Err(ItemParseErr { consumed }) } => {
                                ExpectedKind::ConstPureExpectedFn {
                                    before: [Source::token(file, fst), Source::token(file, snd)],
                                }
                            }
                        ))
                    },
                    @else { return Err(ItemParseErr { consumed }) } => {
                        ExpectedKind::ItemAfterConst { before: Source::token(file, fst) }
                    }
                ))
            }

            // "Pure" might also have something left to consume - we'll expect either "const" or
            // "fn" to follow it.
            Pure => {
                consumed += 1;
                let is_pure = Some(fst);

                expect!((
                    Ok(snd),
                    TokenKind::Keyword(Fn) => consume!(
                        FnDecl,
                        Item::Fn,
                        proof_stmts,
                        proof_stmts_consumed,
                        vis,
                        None,
                        is_pure
                    ),
                    TokenKind::Keyword(Const) => {
                        consumed += 1;
                        let is_const = Some(snd);

                        // A token sequence that starts [ "pure", "const", .. ] will be expected to
                        // have an "fn" keyword immediately following.
                        expect!((
                            Ok(_),
                            TokenKind::Keyword(Fn) => consume!(
                                FnDecl,
                                Item::Fn,
                                proof_stmts,
                                proof_stmts_consumed,
                                vis,
                                is_const,
                                is_pure
                            ),
                            @else { return Err(ItemParseErr { consumed }) } => {
                                ExpectedKind::ConstPureExpectedFn {
                                    before: [Source::token(file, fst), Source::token(file, snd)],
                                }
                            }
                        ))
                    },
                    @else { return Err(ItemParseErr { consumed }) } => {
                        ExpectedKind::PureItemExpectedFnDecl { before: Source::token(file, fst) }
                    }
                ))
            }

            // This is an arm of the match statement on the leading keyword that we found - we've
            // already covered all of the keywords that we allowed, so anything else is unreachable
            _ => unreachable!(),
        }
    }

    /// Parses the entire set of tokens as a list of items, additionally returning whether the list
    /// was poisoned (i.e. if some items may have been omitted due to errors).
    pub(super) fn parse_all(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> (Vec<Item>, bool) {
        let mut items = Vec::new();
        let mut consumed = 0;
        let mut poisoned = false;

        while consumed < tokens.len() {
            let res = Item::consume(
                file,
                &tokens[consumed..],
                ends_early,
                containing_token,
                errors,
            );
            match res {
                Ok(item) => {
                    consumed += item.consumed();
                    items.push(item);
                }
                Err(ItemParseErr { consumed: c }) => {
                    poisoned = true;
                    consumed += c.saturating_sub(1);
                    match Item::seek_next_start(&tokens[consumed..]) {
                        None => break,
                        Some(c) => consumed += c,
                    }
                }
            }
        }

        (items, poisoned)
    }

    /// Returns the number of tokens to skip before we start parsing the next item
    pub(super) fn seek_next_start(tokens: TokenSlice) -> Option<usize> {
        let get = |idx: usize| Some(tokens.get(idx)?.as_ref().ok()?);

        let mut prev = get(0)?;

        let mut i = 1;
        loop {
            let cur = get(i)?;
            if Item::is_ending_token(prev) && Item::is_starting_token(cur) {
                break Some(i);
            }
            prev = cur;
            i += 1;
        }
    }

    /// Returns whether the given token may start an item
    pub(super) fn is_starting_token(token: &Token) -> bool {
        // Whether a token starts an item is generally pretty simple. There's a set of keywords
        // that are allowed, along with the optional "#" that might indicate the start of some set
        // of proof lines.
        match &token.kind {
            TokenKind::ProofLines(_) => true,
            TokenKind::Keyword(k) => match k {
                // FnDecl:
                //   ProofStmts Vis [ "const" ] [ "pure" ] "fn" ...
                Kwd::Pub | Kwd::Const | Kwd::Pure | Kwd::Fn
                // MacroDef:
                //   ProofStmts Vis "macro" ...
                | Kwd::Macro
                // TypeDecl
                //   ProofStmts Vis "type" ...
                | Kwd::Type
                // TraitDef
                //   ProofStmts Vis "trait" ...
                | Kwd::Trait
                // ImplBlock
                //   "impl" ...
                | Kwd::Impl
                // ConstStmt:
                //   Vis "const" ...
                // StaticStmt:
                //   ProofStmts Vis "static" ...
                | Kwd::Static
                // ImportStmt
                //   "import" ...
                | Kwd::Import
                // UseStmt
                //   Vis "use" ...
                | Kwd::Use => true,

                // Everything else can't start an item
                _ => false,
            },
            _ => false,
        }
    }

    /// Returns whether the given token may continue an item after the leading visibility
    /// qualifier.
    pub(super) fn can_follow_vis(token: &Token) -> bool {
        use Kwd::*;

        // This is fairly trivial to determine, based on the BNF specification.
        match &token.kind {
            TokenKind::Keyword(k) => match k {
                Const | Pure | Fn | Macro | Type | Trait | Impl | Static => true,
                _ => false,
            },
            _ => false,
        }
    }

    /// Returns whether the given token may end an item
    pub(super) fn is_ending_token(token: &Token) -> bool {
        match &token.kind {
            TokenKind::Tree {
                delim: Delim::Curlies,
                ..
            }
            | TokenKind::Punctuation(Punc::Semi) => true,
            _ => false,
        }
    }
}

impl ItemParseErr {
    /// A convenience function for converting the standard parsing error type into an
    /// `ItemParseErr`
    ///
    /// This returns a function that, when applied, is equivalent to:
    /// ```
    /// fn app(consumed: usize, opt: Option<usize>) -> ItemParseErr {
    ///     ItemParseErr {
    ///         consumed: consumed + opt.unwrap_or(0),
    ///     }
    /// }
    /// ```
    /// This is provided entirely so that some of the handling around these errors can be a little
    /// cleaner.
    fn add(consumed: usize) -> impl Fn(Option<usize>) -> ItemParseErr {
        move |opt| ItemParseErr {
            consumed: consumed + opt.unwrap_or(0),
        }
    }
}

impl Vis {
    /// Attempts to consume a visibility qualifier as a prefix of the given tokens
    ///
    /// If the tokens were unable to be parsed as a visbility qualifier, this will simply return
    /// `None`.
    pub(super) fn try_consume(file: &FileInfo, tokens: TokenSlice) -> Option<Vis> {
        let token = match tokens.first() {
            Some(Ok(t)) => t,
            _ => return None,
        };

        if let TokenKind::Keyword(Kwd::Pub) = token.kind {
            return Some(Vis::Pub {
                src: token.span(file),
            });
        }

        None
    }

    /// Returns the source of the visibility qualifier
    fn span(&self) -> Span {
        match self {
            Vis::Pub { src } => *src,
        }
    }
}

impl Field {
    /// Consumes a `Field` as a prefix of the given tokens
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: FieldContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<Field, Option<usize>> {
        // Fields are represented by the following BNF:
        //   Field = Ident ( ":" Type | "::" TypeBound ) [ "=" Expr ]
        //
        // As such, we're expecting an identifier as our first token:
        let name = Ident::parse(
            file,
            tokens.first(),
            IdentContext::Field(ctx),
            end_source!(file, containing_token),
            errors,
        )
        .map_err(|()| None)?;

        // And after the identifier, we're expecting either `":" Type` or `"::" TypeBound`. We use
        // `FieldBound` to handle this:
        let mut consumed = 1;
        let (bound, bound_src) = FieldBound::consume(
            file,
            &tokens[consumed..],
            ctx,
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += bound.consumed();

        // Finally, if we have an equals, we'll consume a trailing expression
        let mut value = None;
        if let Some(TokenKind::Punctuation(Punc::Eq)) = kind!(tokens)(consumed) {
            consumed += 1;
            let expr_delim = match ctx {
                FieldContext::FnParam | FieldContext::GenericConstParam => ExprDelim::StructFields,
                FieldContext::ConstStmt | FieldContext::StaticStmt => ExprDelim::Nothing,
            };

            let expr = Expr::consume(
                file,
                &tokens[consumed..],
                expr_delim,
                Restrictions::default(),
                ends_early,
                containing_token,
                errors,
            )
            .map_err(p!(Some(c) => Some(c + consumed)))?;

            consumed += expr.consumed();
            value = Some(expr);
        }

        Ok(Field {
            src: Source::slice_span(file, &tokens[..consumed]),
            name,
            bound_src,
            bound,
            value,
        })
    }
}

impl FieldBound {
    /// Consumes a `FieldBound` as a prefix of the given tokens, returning the bound and its source
    /// on success.
    fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ctx: FieldContext,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<(FieldBound, Span), Option<usize>> {
        make_expect!(file, tokens, 0, ends_early, containing_token, errors);

        expect!((
            Ok(_),
            TokenKind::Punctuation(Punc::Colon) => {
                let ty = Type::consume(
                    file,
                    &tokens[1..],
                    TypeContext::FieldBound(ctx),
                    Restrictions::default(),
                    ends_early,
                    containing_token,
                    errors,
                ).map_err(p!(Some(c) => Some(c + 1)))?;

                let src = &tokens[..ty.consumed() + 1];

                Ok((FieldBound::Type(ty), Source::slice_span(file, src)))
            },
            TokenKind::Punctuation(Punc::DoubleColon) => {
                let bound = TypeBound::consume(
                    file,
                    &tokens[1..],
                    ends_early,
                    containing_token,
                    errors,
                ).map_err(p!(Some(c) => Some(c + 1)))?;

                let src = &tokens[..bound.consumed() + 1];

                Ok((FieldBound::TypeBound(bound), Source::slice_span(file, src)))
            },
            @else(return None) => ExpectedKind::FieldBound(ctx),
        ))
    }
}

impl TypeBound {
    /// Consumes a type bound as a prefix of the given tokens
    pub(super) fn consume(
        file: &FileInfo,
        tokens: TokenSlice,
        ends_early: bool,
        containing_token: Option<&Token>,
        errors: &mut Vec<Error>,
    ) -> Result<TypeBound, Option<usize>> {
        // Type bounds may optionally start with refinements, so we'll check for those first
        let refinements = Refinements::try_consume(
            file,
            tokens,
            Restrictions::default(),
            ends_early,
            containing_token,
            errors,
        )?;

        let mut consumed = refinements.consumed();

        // First, we'll expect an initial path, because each type bound is guaranteed to have one:
        let base_path = Path::consume(
            file,
            &tokens[consumed..],
            ends_early,
            containing_token,
            errors,
        )
        .map_err(p!(Some(c) => Some(c + consumed)))?;

        consumed += base_path.consumed();

        let mut traits = vec![base_path];

        // All the while we find `+` tokens, we'll consume more paths as the list of traits
        while let Some(TokenKind::Punctuation(Punc::Plus)) = kind!(tokens)(consumed) {
            consumed += 1;

            let next_trait = Path::consume(
                file,
                &tokens[consumed..],
                ends_early,
                containing_token,
                errors,
            )
            .map_err(p!(Some(c) => Some(c + consumed)))?;

            consumed += next_trait.consumed();
            traits.push(next_trait);
        }

        Ok(TypeBound {
            src: Source::slice_span(file, &tokens[..consumed]),
            refinements,
            traits,
        })
    }
}
