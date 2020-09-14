//! Basic handling of input parsing for the exposed macros

use crate::CRATE_NAME;
use proc_macro2::TokenStream;
use std::convert::TryFrom;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::token;
use syn::{
    parenthesized, Block, FnArg, Ident, ItemFn, ReturnType, Signature, Token, Type, TypePath,
    Visibility,
};

/// The parsed input for the `__make_database` macro
pub struct DatabaseAst {
    pub attr_paren: token::Paren,
    pub attrs: TokenStream,
    pub vis: Visibility,
    pub name: Ident,
    pub singles_paren: token::Paren,
    pub singles: Punctuated<SingleInputSpec, Token![,]>,
    pub idxs_paren: token::Paren,
    pub indexed: Punctuated<IndexedSpec, Token![,]>,
    pub traits_paren: token::Paren,
    pub traits: Punctuated<TraitSpec, Token![,]>,
}

pub struct SingleInputSpec {
    pub vis: Visibility,
    pub name: Ident,
    pub ty: Type,
}

pub struct IndexedSpec {
    pub vis: Visibility,
    pub add_name: Ident,
    pub get_name: Ident,
    pub index: Type,
    pub all_name: Ident,
    pub ty: Type,
}

pub struct TraitSpec {
    pub vis: Visibility,
    pub name: Ident,
    pub fn_name: Ident,
}

/// The parsed input for the parenthesized attribute for the `query` macro
pub struct QueryAttr {
    pub name: Ident,
}

/// The "parsed" value of a query function
pub struct QueryFn {
    pub vis: Visibility,
    pub fn_name: Ident,
    pub fn_args: Punctuated<FnArg, Token![,]>,
    pub fn_out: ReturnType,
    pub body: Box<Block>,
    pub db_type: Type,
    pub key_type: Type,
    pub value_type: Type,
}

impl Parse for DatabaseAst {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attr_paren;
        let singles_paren;
        let idxs_paren;
        let traits_paren;

        Ok(DatabaseAst {
            attr_paren: parenthesized!(attr_paren in input),
            attrs: attr_paren.parse()?,
            vis: input.parse()?,
            name: input.parse()?,
            singles_paren: parenthesized!(singles_paren in input),
            singles: singles_paren.parse_terminated(SingleInputSpec::parse)?,
            idxs_paren: parenthesized!(idxs_paren in input),
            indexed: idxs_paren.parse_terminated(IndexedSpec::parse)?,
            traits_paren: parenthesized!(traits_paren in input),
            traits: traits_paren.parse_terminated(TraitSpec::parse)?,
        })
    }
}

impl Parse for SingleInputSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(SingleInputSpec {
            vis: input.parse()?,
            name: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for IndexedSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(IndexedSpec {
            vis: input.parse()?,
            add_name: input.parse()?,
            get_name: input.parse()?,
            index: input.parse()?,
            all_name: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for TraitSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(TraitSpec {
            vis: input.parse()?,
            name: input.parse()?,
            fn_name: input.parse()?,
        })
    }
}

impl Parse for QueryAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(QueryAttr {
            name: input.parse()?,
        })
    }
}

impl TryFrom<ItemFn> for QueryFn {
    type Error = syn::Error;

    fn try_from(func: ItemFn) -> syn::Result<Self> {
        macro_rules! malformed {
            () => {
                return Err(syn::Error::new_spanned(func, "malformed query function"));
            };
        }

        // The input function must have a signature that looks exactly like:
        //
        //   <Vis> async fn <name>(<db>: Arc< <db_type> >, <job>: <JobId>, <key>: <key_type>)
        //       -> hydra::Result< <value_type> > {
        //      // -- internals --
        //   }
        //
        // If we find anything that doesn't match this, we'll return via `malformed!()`

        // We explicitly match on the entire function signature to ensure that we don't leave
        // anything out.
        let Signature {
            asyncness,
            constness,
            unsafety,
            abi,
            fn_token: _,
            ident: fn_name,
            generics,
            paren_token: _,
            inputs,
            variadic,
            output,
        } = &func.sig;

        let is_immediately_malformed = asyncness.is_none()
            || constness.is_some()
            || unsafety.is_some()
            || abi.is_some()
            || generics.lt_token.is_some()
            || generics.where_clause.is_some()
            || variadic.is_some();

        if is_immediately_malformed {
            malformed!()
        }

        let db_type: Type;
        let key_type: Type;

        use syn::FnArg::Typed; // could also be `Receiver` -- we don't want that.

        let params: Vec<_> = inputs.iter().collect();
        match &params[..] {
            [Typed(db_arg), Typed(_job), Typed(key_arg)] => {
                if !db_arg.attrs.is_empty() || !key_arg.attrs.is_empty() {
                    malformed!()
                }

                db_type = Type::clone(&db_arg.ty);
                key_type = Type::clone(&key_arg.ty);
            }
            _ => malformed!(),
        }

        // The final piece we want to check is the return type:
        //
        // It should be exactly `hydra::Result<T>` for some `T`. If it isn't, we'll give a custom
        // error message (beyond just `malformed!()`) to be a *little* more helpful
        macro_rules! bad_return_type {
            () => {
                return Err(syn::Error::new_spanned(
                    output,
                    "bad return type; must be `hydra::Result<T>` for some `T`",
                ));
            };
        }

        // `value_type` is where we'll put the type corresponding to `T` in the comment above
        let value_type: Type;

        match output {
            ReturnType::Default => bad_return_type!(),
            ReturnType::Type(_, ty) => match &ty as &Type {
                Type::Path(TypePath { qself: None, path }) => {
                    // The path should be exactly `hydra::Result< $value_type >`:
                    if path.leading_colon.is_some() {
                        bad_return_type!();
                    }

                    use syn::GenericArgument;
                    use syn::PathArguments::{self, AngleBracketed};

                    let segments: Vec<_> = path.segments.iter().collect();
                    if segments.len() != 2 {
                        bad_return_type!();
                    }

                    let bad_names = segments[0].ident.to_string() != CRATE_NAME
                        || segments[1].ident.to_string() != "Result";
                    if bad_names {
                        bad_return_type!();
                    }

                    match (&segments[0].arguments, &segments[1].arguments) {
                        (PathArguments::None, AngleBracketed(args)) => {
                            let args: Vec<_> = args.args.iter().collect();
                            match &args[..] {
                                [GenericArgument::Type(ty)] => value_type = ty.clone(),
                                _ => bad_return_type!(),
                            }
                        }
                        _ => bad_return_type!(),
                    }
                }
                _ => bad_return_type!(),
            },
        }

        Ok(QueryFn {
            vis: func.vis,
            fn_name: fn_name.clone(),
            fn_args: func.sig.inputs,
            fn_out: func.sig.output,
            body: func.block,
            db_type,
            key_type,
            value_type,
        })
    }
}
