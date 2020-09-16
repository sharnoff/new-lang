//! Helper procedural macros for AST production in the compiler
//!
//! This is primarily done through the `Consumed` trait, which is actually internal to the
//! `compiler` crate. Ideally, we would have exposed these macros only through a separate `parse`
//! crate, but avoiding circular crate dependencies there would result in the entire compiler being
//! split apart.
//!
//! Currently, this crate only contains a derive macro for implementing `Consume` - it does this
//! purely through symbols, assuming that there's an associated `Consumed` trait in-scope. As such,
//! it's only really suitable for usage within 'compiler/ast'

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parenthesized, parse_macro_input};
use syn::{Attribute, Error, Expr, Fields, Ident, Item, ItemEnum, ItemStruct, Token};

#[proc_macro_derive(Consumed, attributes(consumed))]
pub fn derive_consumed(item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as Item);

    let output = match item {
        Item::Struct(s) => impl_for_struct(s),
        Item::Enum(e) => impl_for_enum(e),
        _ => Error::new(
            Span::call_site(),
            "`Consumed` derives are only supported on structs and enums",
        )
        .to_compile_error(),
    };

    output.into()
}

// Produces the implementation of `consumed` for a struct
fn impl_for_struct(item: ItemStruct) -> TokenStream2 {
    let fields = match item.fields {
        Fields::Named(fs) => fs,
        // We don't support anything other than named structs
        _ => {
            return Error::new(
                item.fields.span(),
                "`Consumed` derives are only available for named struct fields",
            )
            .to_compile_error()
        }
    };

    // We don't allow generics
    if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
        return Error::new(item.generics.span(), "consumed generics are unsupported")
            .to_compile_error();
    }

    let mut errs = Vec::new();
    let mut terms = Vec::new();
    let mut names = Vec::new();

    let mut has_inner = false;
    let name = item.ident;

    for field in fields.named.into_iter() {
        let name = field.ident.clone().unwrap();

        let res = amount_for_field(true, field, |_| name.to_token_stream());

        match res {
            Err(e) => errs.push(e),
            Ok((is_inner, value)) => match is_inner {
                None if has_inner => (),
                None => {
                    terms.push(value);
                    names.push(name);
                }
                Some(false) if has_inner => {
                    errs.push(
                        Error::new(value.span(), "invalid attributes combination")
                            .to_compile_error(),
                    );
                }
                Some(true) if terms.len() >= 1 => {
                    errs.push(
                        Error::new(value.span(), "invalid attibutes combination")
                            .to_compile_error(),
                    );
                }
                Some(is_inner) => {
                    has_inner = is_inner;
                    terms.push(value);
                    names.push(name);
                }
            },
        }
    }

    if !errs.is_empty() {
        return errs.into_iter().collect();
    }

    quote! {
        impl Consumed for #name {
            #[allow(unused_parens)]
            fn consumed(&self) -> usize {
                let #name {
                    #( #names, )*
                } = self;

                #( #terms )+*
            }
        }
    }
}

fn amount_for_field(
    allow_inner_attr: bool,
    field: syn::Field,
    name: impl Fn(&syn::Field) -> TokenStream2,
) -> Result<(Option<bool>, TokenStream2), TokenStream2> {
    let (attr_flags, errs) = collect_attrs(allow_inner_attr, &field.attrs);
    if !errs.is_empty() {
        return Err(errs.iter().map(Error::to_compile_error).collect());
    }

    let field_span = field.span();
    let name = name(&field);

    match &attr_flags[..] {
        [] => Ok((None, quote_spanned!(field_span => #name.consumed()))),
        [AttrFlag(expr, is_inner, span)] => {
            Ok((Some(*is_inner), quote_spanned!(span.clone() => (#expr))))
        }
        _ => Err(Error::new(
            field.span(),
            "cannot have multiple consumed attributes for field",
        )
        .to_compile_error()),
    }
}

fn impl_for_enum(item: ItemEnum) -> TokenStream2 {
    // We don't allow generics
    if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
        return Error::new(item.generics.span(), "consumed generics are unsupported")
            .to_compile_error();
    }

    let name = item.ident;
    let match_arms = item.variants.into_iter().map(enum_match_arm);

    quote! {
        impl Consumed for #name {
            #[allow(unused_parens)]
            fn consumed(&self) -> usize {
                use #name::*;

                let this = self;
                match self {
                    #( #match_arms, )*
                }
            }
        }
    }
}

fn enum_match_arm(variant: syn::Variant) -> TokenStream2 {
    let (attr_flags, errs) = collect_attrs(false, &variant.attrs);
    if !errs.is_empty() {
        return errs.iter().map(Error::to_compile_error).collect();
    }

    let span = variant.span();
    let name = variant.ident;

    let (pat, value) = match variant.fields {
        Fields::Unit => (name.to_token_stream(), None),
        // Named fields are from a struct. The pattern just references each by name
        Fields::Named(fs) => {
            let mut errs = Vec::new();
            let mut names = Vec::new();
            let mut values = Vec::new();
            let mut has_inner = false;

            for field in fs.named {
                let name = field.ident.clone().unwrap();

                match amount_for_field(false, field, |_| name.to_token_stream()) {
                    Err(e) => errs.push(e),
                    Ok((is_inner, value)) => match is_inner {
                        None if has_inner => (),
                        None => {
                            names.push(name);
                            values.push(value);
                        }
                        Some(false) if has_inner => {
                            errs.push(
                                Error::new(value.span(), "invalid attributes combination")
                                    .to_compile_error(),
                            );
                        }
                        Some(true) if values.len() >= 1 => {
                            errs.push(
                                Error::new(value.span(), "invalid attibutes combination")
                                    .to_compile_error(),
                            );
                        }
                        Some(is_inner) => {
                            has_inner = is_inner;
                            values.push(value);
                            names.push(name);
                        }
                    },
                }
            }

            if !errs.is_empty() {
                return errs.into_iter().collect();
            }

            let pat = quote!( #name { #(#names),* });
            let value = quote!( #( #values )+* );

            (pat, Some(value))
        }
        Fields::Unnamed(fs) => {
            let mut errs = Vec::new();
            let mut names = Vec::new();
            let mut values = Vec::new();
            let mut has_inner = false;

            for (i, field) in fs.unnamed.into_iter().enumerate() {
                let name = Ident::new(&format!("_{}", i), field.span());

                match amount_for_field(false, field, |_| name.to_token_stream()) {
                    Err(e) => errs.push(e),
                    Ok((is_inner, value)) => match is_inner {
                        None if has_inner => (),
                        None => {
                            names.push(name);
                            values.push(value);
                        }
                        Some(false) if has_inner => {
                            errs.push(
                                Error::new(value.span(), "invalid attributes combination")
                                    .to_compile_error(),
                            );
                        }
                        Some(true) if values.len() >= 1 => {
                            errs.push(
                                Error::new(value.span(), "invalid attibutes combination")
                                    .to_compile_error(),
                            );
                        }
                        Some(is_inner) => {
                            has_inner = is_inner;
                            values.push(value);
                            names.push(name);
                        }
                    },
                }
            }

            if !errs.is_empty() {
                return errs.into_iter().collect();
            }

            let pat = quote! { #name(#(#names),*) };
            let value = quote! { #( #values )+* };

            (pat, Some(value))
        }
    };

    // If there *was* a flag, we'll use that information to generate the full match arm.
    // -- Otherwise, we'll just use the value we generated ourselves.
    match &attr_flags[..] {
        [] if value.is_some() => quote_spanned!(span => #pat => #value),
        [AttrFlag(expr, false, span)] => quote_spanned!(span.clone() => #pat => #expr),
        [AttrFlag(_, true, span)] => Error::new(
            span.clone(),
            "inner attributes are not allowed for `enum` variants",
        )
        .to_compile_error(),

        // Unit enum variants must have an attribute specified
        [] => Error::new(
            span,
            "unit enum variants must specify consumed value with `#[consumed = <EXPR>]`",
        )
        .to_compile_error(),

        // More than one flag is an error
        _ => Error::new(span, "cannot have multiple consumed attributes for field")
            .to_compile_error(),
    }
}

fn collect_attrs(allow_inner_attr: bool, attrs: &[Attribute]) -> (Vec<AttrFlag>, Vec<Error>) {
    let mut errs = Vec::new();
    let attr_flags: Vec<_> = attrs
        .iter()
        .filter_map(|attr| match AttrFlag::parse(allow_inner_attr, attr)? {
            Ok(flag) => Some(flag),
            Err(e) => {
                errs.push(e);
                None
            }
        })
        .collect();

    (attr_flags, errs)
}

// A single flag, of the form `#[consumed(<EXPR>)]`. The boolean flag indicates if it's an inner
// flag -- i.e. `#![consumed(<EXPR>)]`
struct AttrFlag(Expr, bool, Span);

impl AttrFlag {
    fn parse(allow_inner_attr: bool, attr: &Attribute) -> Option<Result<AttrFlag, Error>> {
        use syn::AttrStyle;

        let span = attr.span();

        let is_inner = match attr.style {
            AttrStyle::Inner(_) if allow_inner_attr => true,
            AttrStyle::Inner(_) => {
                return Some(Err(Error::new(
                    attr.span(),
                    "inner `consumed` attributes are not allowed here",
                )));
            }
            _ => false,
        };

        // And only if the path is strictly `consumed` -- that's our custom name here:
        if attr.path.get_ident().map(|id| id.to_string()) != Some("consumed".into()) {
            return None;
        }

        // Otherwise, we'll expect something of the form:
        //   #[consumed = EXPR]
        // where EXPR is typically a constant but actually can be anything referencing `self`

        match syn::parse2::<AttrInner>(attr.tokens.clone()) {
            Err(e) => Some(Err(e)),
            Ok(inner) => Some(Ok(AttrFlag(inner.0, is_inner, span))),
        }
    }
}

struct AttrInner(Expr);

impl Parse for AttrInner {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        use syn::{ExprLit, Lit, LitInt};

        let content;
        parenthesized!(content in input);

        if content.peek(Token![@]) {
            // If there's an '@', then it should just be @ignore.
            content.parse::<Token![@]>()?;
            let ident: Ident = content.parse()?;
            match &ident.to_string()[..] {
                "ignore" => {
                    let expr = Expr::Lit(ExprLit {
                        attrs: Vec::new(),
                        lit: Lit::Int(LitInt::new("0", ident.span())),
                    });
                    return Ok(AttrInner(expr));
                }
                _ => return Err(Error::new(ident.span(), "expected ident 'ignore'")),
            }
        }

        Ok(AttrInner(content.parse()?))
    }
}
