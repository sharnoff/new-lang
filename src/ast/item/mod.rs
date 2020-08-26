//! `Item` parsing

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

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

#[derive(Debug, Clone)]
pub enum Item<'a> {
    Fn(FnDecl<'a>),
    Macro(MacroDef<'a>),
    Type(TypeDecl<'a>),
    Trait(TraitDef<'a>),
    Impl(ImplBlock<'a>),
    Const(ConstStmt<'a>),
    Static(StaticStmt<'a>),
    Import(ImportStmt<'a>),
    Use(UseStmt<'a>),
}

/// Visibility qualifiers for [`Item`](enum.Item.html)s
///
/// Currently there is a single variant ("pub") - this may be subject to change in the future.
#[derive(Debug, Clone)]
pub enum Vis<'a> {
    Pub { src: &'a Token<'a> },
}

#[derive(Debug, Clone)]
pub struct TypeBound<'a> {
    pub(super) src: TokenSlice<'a>,
    pub refinements: Option<Refinements<'a>>,
    pub traits: Vec<Path<'a>>,
}

impl<'a> Item<'a> {
    /// Consumes an `Item` as a prefix of the tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current token tree should immediately stop, and `Some` if parsing may continue, indicating
    /// the number of tokens that were marked as invalid here.
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Item<'a>, Option<usize>> {
        make_getter!(macro_rules! get, tokens, ends_early, errors);

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
        let proof_stmts_res = ProofStmts::try_consume(tokens, ends_early, errors);
        let (proof_stmts, mut consumed) = match proof_stmts_res {
            Ok(ps) => {
                let consumed = ps.consumed();
                (ps, consumed)
            }
            Err(Some(consumed)) => (None, consumed),
            Err(None) => {
                // At this point, an error should have already been added due to this ~ we'll
                // return -- this token tree is probably damaged beyond repair
                return Err(None);
            }
        };

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

        let vis = Vis::try_consume(&tokens[consumed..]);
        consumed += vis.consumed();

        // We'll get the next token, which *should* be one of a few different keywords. If it isn't, we'll indicate an
        // error and return the number of tokens we've consumed.

        use Kwd::*;
        use TokenKind::{Ident, Keyword};

        static ITEM_KWDS: &[Kwd] = &[
            Pure, Fn, Macro, Type, Trait, Impl, Const, Static, Import, Use,
        ];

        let fst = get!(
            consumed,
            Err(e) => Error::ExpectedItemKwd {
                kwds: ITEM_KWDS,
                found: Source::TokenResult(Err(*e)),
            },
            None => Error::ExpectedItemKwd {
                kwds: ITEM_KWDS,
                found: end_source!(containing_token),
            },
        );

        let kwd = match &fst.kind {
            Keyword(k) if ITEM_KWDS.contains(&k) => k,
            _ => {
                errors.push(Error::ExpectedItemKwd {
                    kwds: ITEM_KWDS,
                    found: Source::TokenResult(Ok(fst)),
                });

                return Err(Some(consumed));
            }
        };

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
                            vis: vis.src(),
                            item_kind: errors::ItemKind::$item_kind,
                        });
                    }
                }
            };

            (@Proof, $res:expr, $item_kind:ident) => {
                if $res.is_ok() && has_proof_stmts {
                    errors.push(Error::ProofStmtsDisallowedBeforeItem {
                        stmts: &tokens[..proof_stmts_consumed],
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
                let res = consume!(ImplBlock, Item::Impl);
                disallow!(@Vis, res, ImplBlock);
                disallow!(@Proof, res, ImplBlock);
                res
            }
            Static => consume!(StaticStmt, Item::Static, proof_stmts, vis),
            Import => {
                let res = consume!(ImportStmt, Item::Import);
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

                let snd = get!(
                    consumed,
                    Err(e) => Error::ExpectedAfterItemConst {
                        before: fst,
                        found: Source::TokenResult(Err(*e)),
                    },
                    None => Error::ExpectedAfterItemConst {
                        before: fst,
                        found: end_source!(containing_token),
                    },
                );

                match &snd.kind {
                    // As noted above, this is a constant statement.
                    Ident(_) => {
                        let res = consume!(
                            ConstStmt,
                            Item::Const,
                            @tokens: &tokens[proof_stmts_consumed..],
                            @consumed: consumed - proof_stmts_consumed,
                            vis
                        )
                        .map_err(|opt_cons| match opt_cons {
                            Some(consumed) => Some(proof_stmts_consumed + consumed),
                            None => None,
                        });

                        disallow!(@Proof, res, Const);
                        res
                    }
                    Keyword(Fn) => consume!(
                        FnDecl,
                        Item::Fn,
                        proof_stmts,
                        proof_stmts_consumed,
                        vis,
                        is_const,
                        None
                    ),
                    Keyword(Pure) => {
                        // If we encounter a "pure", there's unfortunately *one* last check that we
                        // need to do. We *still* need to make sure that the next token is an "fn"
                        // keyword, so we'll do that now. There's a dedicated error for this one as
                        // well.
                        consumed += 1;
                        let is_pure = Some(snd);

                        let expected_fn_token = get!(
                            consumed,
                            Err(e) => Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: Source::TokenResult(Err(*e)),
                            },
                            None => Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: end_source!(containing_token),
                            },
                        );

                        if let Keyword(Fn) = expected_fn_token.kind {
                            consume!(
                                FnDecl,
                                Item::Fn,
                                proof_stmts,
                                proof_stmts_consumed,
                                vis,
                                is_const,
                                is_pure
                            )
                        } else {
                            errors.push(Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: Source::TokenResult(Ok(expected_fn_token)),
                            });

                            return Err(Some(consumed));
                        }
                    }
                    _ => {
                        errors.push(Error::ExpectedAfterItemConst {
                            before: fst,
                            found: Source::TokenResult(Ok(snd)),
                        });

                        return Err(Some(consumed));
                    }
                }
            }

            // "Pure" might also have something left to consume - we'll expect either "const" or
            // "fn" to follow it.
            Pure => {
                consumed += 1;
                let is_pure = Some(fst);

                let snd = get!(
                    consumed,
                    Err(e) => Error::PureItemExpectedFnDecl {
                        before: fst,
                        found: Source::TokenResult(Err(*e)),
                    },
                    None => Error::PureItemExpectedFnDecl {
                        before: fst,
                        found: end_source!(containing_token),
                    },
                );

                match &snd.kind {
                    Keyword(Fn) => consume!(
                        FnDecl,
                        Item::Fn,
                        proof_stmts,
                        proof_stmts_consumed,
                        vis,
                        None,
                        is_pure
                    ),
                    Keyword(Const) => {
                        consumed += 1;
                        let is_const = Some(snd);

                        // A token sequence that starts [ "pure", "const", .. ] will be expected to
                        // have an "fn" keyword immediately following.
                        let expected_fn_token = get!(
                            consumed,
                            Err(e) => Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: Source::TokenResult(Err(*e)),
                            },
                            None => Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: end_source!(containing_token),
                            },
                        );

                        if let Keyword(Fn) = expected_fn_token.kind {
                            consume!(
                                FnDecl,
                                Item::Fn,
                                proof_stmts,
                                proof_stmts_consumed,
                                vis,
                                is_const,
                                is_pure
                            )
                        } else {
                            errors.push(Error::ConstPureExpectedFn {
                                before: [fst, snd],
                                found: Source::TokenResult(Ok(expected_fn_token)),
                            });

                            return Err(Some(consumed));
                        }
                    }
                    _ => {
                        errors.push(Error::PureItemExpectedFnDecl {
                            before: fst,
                            found: Source::TokenResult(Ok(snd)),
                        });

                        return Err(Some(consumed));
                    }
                }
            }

            // This is an arm of the match statement on the leading keyword that we found - we've
            // already covered all of the keywords that we allowed, so anything else is unreachable
            _ => unreachable!(),
        }
    }
}

impl<'a> Vis<'a> {
    /// Attempts to consume a visibility qualifier as a prefix of the given tokens
    ///
    /// If the tokens were unable to be parsed as a visbility qualifier, this will simply return
    /// `None`.
    pub(super) fn try_consume(tokens: TokenSlice<'a>) -> Option<Vis<'a>> {
        let token = match tokens.first() {
            Some(Ok(t)) => t,
            _ => return None,
        };

        if let TokenKind::Keyword(Kwd::Pub) = token.kind {
            return Some(Vis::Pub { src: token });
        }

        None
    }

    /// Returns the source backing the visibility qualifier
    fn src(&self) -> Source<'a> {
        match self {
            Vis::Pub { src } => Source::TokenResult(Ok(src)),
        }
    }
}

impl<'a> TypeBound<'a> {
    pub(super) fn consume(
        tokens: TokenSlice<'a>,
        ctx: TypeBoundContext<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<TypeBound<'a>, Option<usize>> {
        todo!()
    }
}
