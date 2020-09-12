use heck::SnakeCase;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use std::convert::TryFrom;
use std::sync::atomic::{AtomicU16, Ordering::SeqCst};
use syn::{parse_macro_input, Ident, ItemFn, LitInt};

mod parse;

use parse::{DatabaseAst, QueryAttr, QueryFn};

static CRATE_NAME: &str = "hydra";

/// A macro used by the front-end to pass through values once they've been verified
///
/// This is hidden so that a `macro_rules` version of this same macro can be used to provide the
/// input in a slightly nicer format. For more information, refer to the public `make_database`
/// macro provided in the main crate.
#[proc_macro]
#[doc(hidden)]
pub fn __make_database(input: TokenStream) -> TokenStream {
    let database_input = parse_macro_input!(input as DatabaseAst);
    let single_specs: Vec<_> = database_input.singles.into_iter().collect();
    let trait_specs: Vec<_> = database_input.traits.into_iter().collect();

    let db_type = database_input.name;
    let db_inner_type = format_ident!("Inner{}", db_type);

    let num_query_kind = trait_specs.len();

    // The various pieces that we'll assemble as part of the output
    let mut db_layers = Vec::with_capacity(trait_specs.len());
    let mut field_names = Vec::with_capacity(trait_specs.len());
    let mut trait_impls = Vec::with_capacity(trait_specs.len());
    let mut blocked_pats = Vec::with_capacity(trait_specs.len());
    let mut methods = Vec::new();

    for spec in trait_specs {
        let trait_name = spec.name;
        let method_name = spec.fn_name;
        let vis = spec.vis;

        let field_name = Ident::new(&trait_name.to_string().to_snake_case(), trait_name.span());

        let token = quote!(<hydra::internal::Dummy as #trait_name<#db_type>>::Token);
        let compute = quote!(#token as hydra::internal::Computable<#db_type>);

        let layer = quote!(
            hydra::DBLayer<<#compute>::Key, <#compute>::Value, #db_type, #token>
        );

        trait_impls.push(quote!(
            impl std::convert::AsRef<#layer> for #db_type {
                fn as_ref(&self) -> &#layer {
                    &self.0.#field_name
                }
            }
        ));

        blocked_pats.push(quote!(<#compute>::QUERY_KIND));

        methods.push(quote!(
            #vis fn #method_name(
                &self,
                job: hydra::JobId,
                key: <#compute>::Key,
            ) -> std::sync::Arc<hydra::Result<<#compute>::Value>> {
                self.0.#field_name.get(self, job, key)
            }
        ));

        db_layers.push(layer);
        field_names.push(field_name);
    }

    let mut single_fields = Vec::with_capacity(single_specs.len());
    for field in single_specs {
        let vis = field.vis;
        let name = field.name;
        let field_ty = field.ty;

        single_fields.push(quote!(
            #vis #name: std::sync::RwLock<Option<std::sync::Arc<#field_ty>>>
        ));

        let unset = format!("singular hydra field `{}` has not been set", name);

        methods.push(quote!(
            fn #name(&self) -> std::sync::Arc<#field_ty> {
                self.0.#name.read().unwrap()
                    .as_ref()
                    .expect(#unset)
                    .clone()
            }
        ));

        let set_name = format_ident!("set_{}", name);

        methods.push(quote!(
            fn #set_name(&self, value: #field_ty) {
                let mut guard = self.0.#name.write().unwrap();
                if guard.is_some() {
                    panic!("singular hydra field `{}` has already been set!", stringify!(#name));
                }

                *guard = Some(std::sync::Arc::new(value))
            }
        ));
    }

    let attrs = database_input.attrs;
    let vis = database_input.vis;

    // And finally, we construct the database struct itself
    quote!(
        #attrs
        #[derive(Clone)]
        #vis struct #db_type(std::sync::Arc<#db_inner_type>);

        struct #db_inner_type {
            #( #single_fields, )*

            #( #field_names: #db_layers, )*

            // A helper field to indicate where certain jobs are
            __active_jobs: hydra::internal::JobOwners,
            __executor: std::sync::Arc<hydra::internal::Executor>,
        }

        impl #db_type {
            #( #methods )*
        }

        impl hydra::internal::Runtime for #db_type {
            fn mark_single_blocked(&self, job: &hydra::JobId, by: &hydra::JobId) -> Option<()> {
                use std::sync::Arc;
                use std::ops::Deref;

                let q_kind = self.0.__active_jobs.query_kind(job)?;

                match q_kind {
                    #( #blocked_pats => self.0.#field_names.mark_blocked(job, by), )*
                    _ => panic!("unknown query kind {:?} of {} known", q_kind, #num_query_kind),
                }
            }

            fn executor(&self) -> &hydra::internal::Executor {
                &self.0.__executor
            }
        }

        #( #trait_impls )*
    )
    .into()
}

/// Constructs a wrapper query trait for a given function
#[proc_macro_attribute]
pub fn query(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as QueryAttr);
    let initial_function = parse_macro_input!(item as ItemFn);

    let source_span = initial_function.sig.ident.span();

    let query_fn = match QueryFn::try_from(initial_function) {
        Ok(qf) => qf,
        Err(e) => return e.to_compile_error().into(),
    };

    let QueryFn {
        fn_name: _,
        fn_args,
        fn_out,
        body,
        db_type,
        key_type,
        value_type,
    } = query_fn;

    let name = attr.name;
    let kind_count = LitInt::new(&get_kind_count().to_string(), source_span);

    let token_type = format_ident!("Hydra{}Token", name);

    quote!(
        trait #name<DB> {
            type Token;
        }

        struct #token_type;

        impl #name<#db_type> for hydra::internal::Dummy {
            type Token = #token_type;
        }

        impl hydra::internal::Computable<#db_type> for #token_type {
            type Key = #key_type;
            type Value = #value_type;

            const QUERY_KIND: hydra::internal::QueryKind = hydra::internal::QueryKind(#kind_count);

            fn construct(#fn_args) #fn_out #body
        }
    )
    .into()
}

/// A helper function to get the current kind count value, then increment it
fn get_kind_count() -> u16 {
    static COUNT: AtomicU16 = AtomicU16::new(0);

    COUNT.fetch_add(1, SeqCst)
}
