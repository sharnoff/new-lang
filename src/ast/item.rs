//! Parsing submodule for `Item`s

// We'll just blanket import everything, just as the parent module blanket imports everything from
// this module.
use super::*;

#[derive(Debug)]
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

/// Visibility qualifiers for [`Item`]s
///
/// Currently there is a single variant ("pub") - this may be subject to change in the future.
#[derive(Debug)]
pub enum Vis<'a> {
    Pub { src: &'a Token<'a> },
}

/// A function declaration, independent of where it occurs
///
/// Note that this also includes function declarations that may be part of a trait definition, and
/// so they are allowed here to not have a body. This is left to be validated later, as part of a
/// separate pass.
///
/// Nevertheless, we'll briefly touch on some of the context-specific semantic validity of function
/// delcarations (and what each component signifies).
///
/// The BNF definition for function declarations is:
/// ```text
/// FnDecl = ProofStmts Vis [ "const" ] [ "pure" ] "fn" Ident [ GenericParams ]
///          FnParams [ "->" Type ] ( ";" | BlockExpr ) .
/// ```
/// The first few syntactic elements (`ProofStmts` through `GenericParams`) should be fairly
/// self-explanatory - these work as expected and are valid in any context. After these, the
/// validity of certain components of [`FnParams`] changes depending on the context, but nothing
/// about the enclosing `FnDecl` due to it - for more information, see the documentation about the
/// type. After the parameters, the return type is typically given - this may be omitted if equal
/// to `()`.
///
/// Finally, the implementation may be given or replaced by a semicolon. Body-less functions are
/// only valid inside trait definitions.
///
/// Note also that visibility qualifiers are not allowed within trait definitions; each item takes the
/// visibility of the parent trait.
///
/// [`FnParams`]: struct.FnParams.html
#[derive(Debug)]
pub struct FnDecl<'a> {
    pub(super) src: TokenSlice<'a>,
    vis: Option<Vis<'a>>,
    is_const: Option<&'a Token<'a>>,
    is_pure: Option<&'a Token<'a>>,
    name: (),           // Ident
    generic_params: (), // GenericParams
    params: (),         // FnParams
    return_ty: (),      // Type
    body: (),           // Option<BlockExpr>
}

/// A macro definition
///
/// This feature is a work-in-progress, and so this type has not yet been defined.
#[derive(Debug)]
pub struct MacroDef<'a> {
    placeholder: &'a (),
}

/// A type declaration, independent of where it might occur
///
/// Note that this also includes types declarations that might be part of a trait definition, where
/// there may be bounds on the type (and where they might lack a definition). The checks for
/// whether a type declaration is valid are left for later, as part of a separate pass.
///
/// Nevertheless, we'll briefly touch on some of the context-specific semantic validity of type
/// declarations (and what each component signifies).
///
/// The BNF definition for type declarations is:
/// ```text
/// TypeDecl = ProofStmts Vis "type" Ident [ GenericParams ]
///            [ TypeBound ] ( ";" | [ "=" ] Type [ ";" ] ) .
/// ```
/// In turn, type declarations may have proof statements, visibility qualifiers, and generic
/// parameters - these all function as expected. The final few elements, however are more complex
/// and typically occupy the most visual space. When inside a trait definition, the `TypeBound` is
/// allowed as a method of constraining the set of associated types that are valid - the
/// right-hand-side type is additionally not necessary; providing one instead serves as a default
/// value. When *outside* a trait definition, type bounds are disallowed and the definition must be
/// present.
///
/// Note that visibility qualifiers are not allowed within trait definitions; each item takes the
/// visibility of the parent trait.
#[derive(Debug)]
pub struct TypeDecl<'a> {
    pub(super) src: TokenSlice<'a>,
    name: (),           // Ident
    generic_params: (), // GenericParams
    bound: (),          // Option<TypeBound>
    is_alias: bool,     //
    def: (),            // Option<Type>
}

/// A trait definition
///
/// While these are syntactically allowed within trait definitions, they are not semantically valid
/// in those positions - this is a feature that may be added in the future, but it is not currently
/// planned.
///
/// The BNF for trait definitions is:
/// ```text
/// TraitDef = ProofStmts Vis "trait" Ident [ GenericParams ] [ TypeBound ] ( ImplBody | ";" ) .
/// ```
/// Some of the syntax elements here warrant an explanation; we'll go through those in order.
/// Firstly, while trait definitions may be preceeded by proof statements, there aren't currently
/// any ways in which proof could apply to the contents of a trait definition - in any case, this
/// validation is left for later.
///
/// Beyond the first few elements, traits are defined by their name and whatever generic parameters
/// they take as input. They may also list "super traits" - additional restrictions given by a
/// [`TypeBound`] that all implementors of this trait must also satisfy.
///
/// In the event that the trait has no items in its body, a single semicolon may be used in place
/// of an empty curly-brace block.
///
/// [`TypeBound`]: struct.TypeBound.html
#[derive(Debug)]
pub struct TraitDef<'a> {
    pub(super) src: TokenSlice<'a>,
    proof_stmts: ProofStmts<'a>,
    vis: Option<Vis<'a>>,
    name: (),           // Ident
    generic_params: (), // GenericParams
    super_traits: (),   // Option<TypeBound>
    body: (),           // Option<ImplBody>
}

/// An "impl" block - either as a standalone type or for implementing a trait
///
/// While syntactically allowed as normal items, "impl" blocks are not allowed within trait
/// definitions or other impl blocks.
///
/// The BNF for impl blocks is fairly simple:
/// ```text
/// ImplBlock = "impl" [ Trait "for" ] Type ImplBody .
/// ```
/// Because some of the prefixes that are allowed for other items aren't allowed here (namely:
/// [`ProofStmts`] and [`Vis`]), there are a few steps taken in constructing error messages to be
/// more helpful to the user. In this case, it's done with the error variants
/// [`ProofStmtsDisallowedBeforeItem`] and [`VisDisallowedBeforeItem`].
///
/// Aside from this bit of extra care, the syntax here is mainly so simple because it's built of
/// other pieces. Impl blocks are allowed to provide standalone associated items for a type, or to
/// specifically implement a trait. The rest of the semantics around the validity of type/trait
/// pairs is complex and subject to change, so it will not be discussed here.
///
/// [`ProofStmts`]: struct.ProofStmts.html
/// [`Vis`]: enum.Vis.html
/// [`ProofStmtsDisallowedBeforeItem`]: ../errors/enum.Error.html#variant.ProofStmtsDisallowedBeforeItem
/// [`VisDisallowedBeforeItem`]: ../errors/enum.Error.html#variant.VisDisallowedBeforeItem
#[derive(Debug)]
pub struct ImplBlock<'a> {
    pub(super) src: TokenSlice<'a>,
    trait_impl: (), // Trait
    impl_ty: (),    // Type
    body: (),       // ImplBody
}

/// A `const` statment
///
/// Const statments may appear as an item in any scope - either as an associated `impl` or trait
/// item - or simply as a module-level constant. Only some forms might be valid in each, however.
///
/// The BNF can be defined by either of these equivalent definitions:
/// ```text
/// ConstStmt = Vis "const" Ident ( ":" Type | TypeBound ) [ "=" Expr ] ";" .
///           = Vis "const" StructField ";" .
/// ```
/// The first definition is more accurate to how a `ConstStmt` is represented, whereas the second
/// gives a better idea as to how it is actually parsed.
///
/// Typically, const statements will be of the (simpler) form:
/// ```text
/// Vis "const" Ident ":" Type "=" Expr ";"
/// ```
/// This form is the only form that is semantically valid outside of trait definitions. All of the
/// other variants possible correspond to the particular forms that are allowed within trait
/// definitions.
///
/// More specifically, const statments of each variant take on the following meanings when inside
/// of trait definitions:
/// * If a value is given (with `"=" Expr`), this will be given as a default value that may be
///   overriden by the implementor
/// * If no value is given, implementors must supply one.
/// * Instead of a concrete type, a [`TypeBound`] may be given to give additional freedom to the
///   types that may be used as an associated constant (e.g. `const Foo :: Debug`).
///
/// Finally, it should be noted that visibility qualifiers are invalid within trait definitions (or
/// implementations) as the scoping is given instead by the visibility of the trait.
///
/// [`TypeBound`]: struct.TypeBound.html
#[derive(Debug)]
pub struct ConstStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    vis: Option<Vis<'a>>,
    name: (),     // Ident
    value_ty: (), // Option<Type>
    bound: (),    // Option<TypeBound>
    value: (),    // Option<Expr>
}

/// A `static` statement
///
/// Syntactically, these are identical to [const statements], with one notable exception -
/// because static values may mutate, proof statments *are* allowed here, where they aren't with
/// const statments.
///
/// For further information, refer to the documentation for [const statements].
///
/// [const statements]: struct.ConstStmt.html
#[derive(Debug)]
pub struct StaticStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    proof_stmts: ProofStmts<'a>,
    vis: Option<Vis<'a>>,
    name: (),     // Ident
    value_ty: (), // Option<Type>
    bound: (),    // Option<TypeBound>
    value: (),    // Option<Expr>
}

/// An import statment
///
/// **Note that this feature is a work-in-progress, and so the specifics have not yet been
/// defined.**
///
/// These serve to bring in external libraries as identifiers - for bringing individual items into
/// scope, see [`UseStmt`s].
///
/// The BNF definition for import statmtents is:
/// ```text
/// ImportStmt = "import" StringLiteral [ "~" StringLiteral ] [ "as" Ident ] .
/// ```
///
/// The first string literal gives the source for the library - typically a url. The second string,
/// if provided, indicates the version of the library to use. If left out, the version will be
/// assumed to be identical to whatever is present elsewhere in the local source tree. This is not
/// allowed if there are different versions of the same library in use within the same source tree.
///
/// The final identifier optionally gives a namespace to import the library under. In most cases,
/// this will be automatically determined - in others (typically with names that cannot be
/// converted to an identifier), the user *must* supply an identifier to rename as.
///
/// [`UseStmt`s]: struct.UseStmt.html
#[derive(Debug)]
pub struct ImportStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    source: (),  // StringLiteral
    version: (), // Option<StringLiteral>
    as_name: (), // Ident
}

/// A "use" statment
///
/// These serve to bring individual items into scope. Each item brought into scope requires the
/// type of the item to be explicitly given (e.g. `fn`, `type`, `trait`, etc).
///
/// "Use" statments are not allowed within trait definitions, but are allowed within `impl` blocks,
/// simply as a method of providing items to the local scope - in these cases, they cannot affect
/// how the impl block is viewed from outside.
///
/// The BNF definition is defined in parts - we'll list all three here for completeness:
/// ```text
/// UseStmt = Vis "use" UsePath ";" .
/// UsePath = Path "." "{" UsePath { "," UsePath } [ "," ] "}" .
///         | UseKind Path [ "as" Ident ] .
/// UseKind = "fn" | "macro" | "type" | "trait" | "const" | "static" .
/// ```
/// Multiple items under a single namespace may be brought into scope with curly braces (as seen by
/// the first variant of [`UsePath`]). Items may also be renamed as they are brought into scope.
///
/// [`UsePath`]: enum.UsePath.html
#[derive(Debug)]
pub struct UseStmt<'a> {
    pub(super) src: TokenSlice<'a>,
    vis: Option<Vis<'a>>,
    path: (), // UsePath
}

/// A collection of proof statements, given before an item
///
/// This is provided so that we can track groups of proof statements together, keeping certain
/// attributes (like whether the values have been poisoned) as part of this struct instead of
/// elsewhere.
///
/// For more information on the structure of proof statements, see [`ProofStmt`].
///
/// [`ProofStmt`]: struct.ProofStmt.html
#[derive(Debug)]
pub struct ProofStmts<'a> {
    pub stmts: Vec<ProofStmt<'a>>,
    pub poisoned: bool,
    pub(super) src: TokenSlice<'a>,
}

/// A single proof statment - i.e. a single line starting with `#`
///
/// There are multiple types of the statments possibe; these are given by the `kind` field.
///
/// The BNF for proof statements is:
/// ```text
/// ProofStmts = { "#" ProofStmt "\n" } .
/// ProofStmt = Expr ( "=>" | "<=>" ) Expr
///           | Expr
///           | "invariant" [ StringLiteral ] ":"
///           | "forall" Pattern [ "in" Expr ] ":"
///           | "exists" Pattern [ "in" Expr ] where ":"
/// ```
/// Please note that these are likely to change - the precise syntax here is far from final.
///
/// The first `ProofStmt` variant indicates single- or double-implication between certain
/// conditions, given by expressions. The second simply gives a boolean statement that is always
/// true (or always required). The remaining three should hopefully be relatively clear without
/// further detail.
///
/// These types of statmeents are enumerated in the variants of [`ProofStmtKind`].
///
/// ## Structure
///
/// Broadly speaking, the nesting of proof statements is given by their indentation level; the BNF
/// here accurately describes single lines, but not the tree structure created between them.
///
/// For example, one might write the following:
/// ```text
/// # invariant "foo":
/// #   x > 4
/// # forall y in 0..x:
/// #   exists z where:
/// #       bar(z) = 0
/// ```
/// in which the statement `x > 4` is part of the invariant, and `bar(z) = 0` is part of
/// `exists z where:`, inside `forall y in 0..x`.
///
/// [`ProofStmtKind`]: enum.ProofStmtKind.html
#[derive(Debug)]
pub struct ProofStmt<'a> {
    pub kind: ProofStmtKind<'a>,
    pub(super) src: TokenSlice<'a>,
}

/// The different types of proof statements available
///
/// For information on proof statments, refer to the documentation for [`ProofStmt`].
///
/// [`ProofStmt`]: struct.ProofStmt.html
#[derive(Debug)]
pub enum ProofStmtKind<'a> {
    /// Single implication: `Expr "=>" Expr`
    Implies(Expr<'a>, Expr<'a>),
    /// Double implication: `Expr "<=>" Expr`
    DoubleImplies(Expr<'a>, Expr<'a>),
    /// A single value that is given to be true
    Predicate(Expr<'a>),
    Invariant {
        name: (), // Option<StringLiteral>
        stmts: Vec<ProofStmt<'a>>,
    },
    Forall {
        pattern: (), // Pattern
        iter: (),    // Expr
        stmts: Vec<ProofStmt<'a>>,
    },
    Exists {
        pattern: (), // Pattern
        iter: (),    // Expr
        stmts: Vec<ProofStmt<'a>>,
    },
}

impl<'a> Item<'a> {
    /// Consumes an `Item` as a prefix of the tokens
    ///
    /// In the event of an error, the returned `Option` will be `None` if parsing within the
    /// current block should immediately stop, and `Some` if parsing may continue, indicating the
    /// number of tokens that were marked as invalid here.
    pub(super) fn consume_from(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<Item<'a>, Option<usize>> {
        // A helper macro for use later in this function
        //
        // This simply wraps `tokens.get(..)` so that we can extract a single `&Token` instead of a
        // `&Result<Token, _>`. Error handling is given so that we can explicitly handle the cases
        // of tokenizer errors and running out of tokens separately.
        macro_rules! get {
            ($consumed:expr, Err($e:ident) => $err:expr, None => $none:expr $(,)?) => {
                match tokens.get($consumed) {
                    Some(Ok(t)) => t,
                    Some(Err($e)) => {
                        use token_tree::Error::*;

                        // All of the errors at this point assume that tokenizer errors are due to
                        // delimeters. For future compatability, we'll simply match on all of those
                        // to ensure that this stays the case.
                        //
                        // NOTE: If you come here because this match statement is missing values,
                        // there's other logic that needs to be replaced throughout this function.
                        // DO NOT make this a quick fix.
                        match $e {
                            UnexpectedCloseDelim(_)
                            | MismatchedCloseDelim { .. }
                            | UnclosedDelim(_, _) => (),
                        }

                        errors.push($err);
                        return Err(None);
                    }
                    // If we ran out of tokens but they were limited due to a previous error, we'll
                    // silently ignore it and indicate that this token tree should no longer be
                    // parsed.
                    None if ends_early => return Err(None),
                    // Otherwise, we'll use the error given to us above
                    None => {
                        errors.push($none);
                        return Err(None);
                    }
                }
            }
        }

        // A helper value for providing the source in error cases where we ran out of tokens
        let end_source = match containing_token {
            Some(tt) => Source::EndDelim(tt),
            None => Source::EOF,
        };

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
        let proof_stmts_res = ProofStmts::consume_from(tokens, ends_early, errors);
        let (proof_stmts, mut consumed) = match proof_stmts_res {
            Ok(ps) => {
                let consumed = ps.consumed();
                (ps, consumed)
            }
            Err(Some((ps, consumed))) => (ps, consumed),
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
                found: end_source,
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
            Fn => consume!(FnDecl, Item::Fn, proof_stmts, vis, None, None),

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
                        found: end_source,
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
                    Keyword(Fn) => consume!(FnDecl, Item::Fn, proof_stmts, vis, is_const, None),
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
                                found: end_source,
                            },
                        );

                        if let Keyword(Fn) = expected_fn_token.kind {
                            consume!(FnDecl, Item::Fn, proof_stmts, vis, is_const, is_pure)
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
                        found: end_source,
                    },
                );

                match &snd.kind {
                    Keyword(Fn) => consume!(FnDecl, Item::Fn, proof_stmts, vis, None, is_pure),
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
                                found: end_source,
                            },
                        );

                        if let Keyword(Fn) = expected_fn_token.kind {
                            consume!(FnDecl, Item::Fn, proof_stmts, vis, is_const, is_pure)
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
    fn try_consume(tokens: TokenSlice<'a>) -> Option<Vis<'a>> {
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

impl<'a> FnDecl<'a> {
    /// Consumes a function declaration as a prefix of the given set of tokens
    ///
    /// The index in the tokens where the function's name (given as an identifier) is expected. For
    /// example, given the following set of tokens:
    /// ```text
    /// [ Keyword(Const), Keyword(Fn), Ident("foo"), .. ]
    /// ```
    /// `ident_idx` will be equal to 2. The tokens up to `ident_idx` are guaranteed to be valid for
    /// a function declaration (with the values parsed from them given by the various parameters:
    /// `proof_stmts`, `vis`, `is_const`, and `is_pure`). While it is given that
    /// `tokens[ident_idx - 1]` will be the "fn" keyword, it is not guaranteed that there is an
    /// identifier token at `ident_idx`.
    ///
    /// In the event of an error, this function may either return `None` to indicate that parsing
    /// within the current token tree should not continue, or `Some` to give the number of tokens
    /// that were consumed in parsing here.
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: ProofStmts<'a>,
        vis: Option<Vis<'a>>,
        is_const: Option<&'a Token<'a>>,
        is_pure: Option<&'a Token<'a>>,
    ) -> Result<FnDecl<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> MacroDef<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: ProofStmts<'a>,
        vis: Option<Vis<'a>>,
    ) -> Result<MacroDef<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> TypeDecl<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: ProofStmts<'a>,
        vis: Option<Vis<'a>>,
    ) -> Result<TypeDecl<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> TraitDef<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: ProofStmts<'a>,
        vis: Option<Vis<'a>>,
    ) -> Result<TraitDef<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> ImplBlock<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ImplBlock<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> ConstStmt<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<ConstStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> StaticStmt<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        proof_stmts: ProofStmts<'a>,
        vis: Option<Vis<'a>>,
    ) -> Result<StaticStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> ImportStmt<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ImportStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> UseStmt<'a> {
    fn consume(
        tokens: TokenSlice<'a>,
        ident_idx: usize,
        ends_early: bool,
        containing_token: Option<&'a Token<'a>>,
        errors: &mut Vec<Error<'a>>,
        vis: Option<Vis<'a>>,
    ) -> Result<UseStmt<'a>, Option<usize>> {
        todo!()
    }
}

impl<'a> ProofStmts<'a> {
    /// Consumes multiple `ProofStmt`s as a prefix of the tokens given
    ///
    /// In the event of an error, there are two forms of failure. One may occur when the
    fn consume_from(
        tokens: TokenSlice<'a>,
        ends_early: bool,
        errors: &mut Vec<Error<'a>>,
    ) -> Result<ProofStmts<'a>, Option<(ProofStmts<'a>, usize)>> {
        todo!()
    }
}
