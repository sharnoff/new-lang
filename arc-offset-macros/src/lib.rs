use syn::{ItemEnum, parse_macro_input, Fields, Error};
use syn::spanned::Spanned;
use quote::{quote, quote_spanned, format_ident};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

#[proc_macro_derive(ArcOffset)]
pub fn derive_arc_offset(tokens: TokenStream) -> TokenStream {
    let item = parse_macro_input!(tokens as ItemEnum);

    let base_ty = &item.ident;
    let vis = &item.vis;
    let helper_name = format_ident!("{}ArcOffset", base_ty);

    let mut variant_names = Vec::new();
    let mut variant_types = Vec::new();
    let mut offset_arms = Vec::new();

    let mut errors = Vec::new();

    for variant in item.variants.into_iter() {
        let name = variant.ident;
        let (fields, fields_span) = match variant.fields {
            Fields::Unnamed(fs) => {
                let span = fs.span();
                (fs.unnamed.into_iter().collect::<Vec<_>>(), span)
            }
            fields => {
                errors.push(Error::new(
                    fields.span(),
                    "deriving `ArcOffset` requires a single unit variant",
                ));
                continue;
            },
        };

        let inner_type = match &fields[..] {
            [field] => &field.ty,
            _ => {
                errors.push(Error::new(
                    fields_span,
                    "deriving `ArcOffset` requires a single unit variant",
                ));
                continue;
            },
        };

        let ty_span = inner_type.span();
        variant_types.push(quote_spanned!(ty_span=> arc_offset::ArcOffset<#base_ty, #inner_type>));
        offset_arms.push(quote_spanned! {
            ty_span=>
            #base_ty::#name(ref t) => {
                use arc_offset::{addr, ArcOffset};

                let src_addr = addr(&this as &Self);
                let target_addr = addr(t as &#inner_type);
                let offset = target_addr - src_addr;

                drop(t);

                unsafe { 
                    #helper_name::#name(ArcOffset::new_unchecked(this, offset))
                }
            },
        });
        variant_names.push(name);
    }

    if !errors.is_empty() {
        return errors.iter().map(Error::to_compile_error).collect::<TokenStream2>().into();
    }

    let output = quote! {
        impl arc_offset::__OffsetHelper for #base_ty {
            type Inner = #helper_name;

            fn arc_offset(this: std::sync::Arc<Self>) -> Self::Inner {
                match &this as &Self {
                    #( #offset_arms )*
                }
            }
        }

        #vis enum #helper_name {
            #( #variant_names(#variant_types), )*
        }
    };

    output.into()
}
