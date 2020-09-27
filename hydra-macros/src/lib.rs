use heck::SnakeCase;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote};
use std::convert::TryFrom;
use std::sync::atomic::{AtomicU16, Ordering::SeqCst};
use syn::{parse_macro_input, Ident, ItemFn, ItemStruct, LitInt, Type};

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
    let indexed_specs: Vec<_> = database_input.indexed.into_iter().collect();
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
            #vis async fn #method_name(
                &self,
                job: hydra::JobId,
                key: <#compute>::Key,
            ) -> hydra::Result<<#compute>::Value> {
                self.0.#field_name.query(self, job, key).await
            }
        ));

        db_layers.push(layer);
        field_names.push(field_name);
    }

    let mut singles_vis = Vec::with_capacity(single_specs.len());
    let mut singles_names = Vec::with_capacity(single_specs.len());
    let mut singles_types = Vec::with_capacity(single_specs.len());

    for field in single_specs {
        let vis = field.vis;
        let name = field.name;
        let field_ty = field.ty;

        let unset = format!("singular hydra field `{}` has not been set", name);

        methods.push(quote!(
            #vis async fn #name(&self) -> std::sync::Arc<#field_ty> {
                self.0.#name.lock().await
                    .as_ref()
                    .expect(#unset)
                    .clone()
            }
        ));

        let set_name = format_ident!("set_{}", name);

        methods.push(quote!(
            #vis async fn #set_name(&self, value: #field_ty) {
                let mut guard = self.0.#name.lock().await;
                if guard.is_some() {
                    panic!("singular hydra field `{}` has already been set!", stringify!(#name));
                }

                *guard = Some(std::sync::Arc::new(value))
            }
        ));

        singles_vis.push(vis);
        singles_names.push(name);
        singles_types.push(quote!(std::sync::Arc<#field_ty>));
    }

    let mut indexed_field_names = Vec::with_capacity(indexed_specs.len());
    let mut indexed_types = Vec::with_capacity(indexed_specs.len());
    let mut indexers = Vec::with_capacity(indexed_specs.len());

    for spec in indexed_specs {
        let vis = spec.vis;
        let add = spec.add_name;
        let get = spec.get_name;
        let all = spec.all_name;
        let ty = spec.ty;
        let indexer = spec.index;

        let extend = format_ident!("extend_{}", all);

        methods.push(quote!(
            #vis async fn #add(&self, job: &JobId, f: impl FnOnce(#indexer) -> #ty) {
                self.0.#all.push_with(job, f).await
            }

            #vis async fn #get(&self, job: &JobId, idx: #indexer) -> #ty {
                self.0.#all.get_cloned(job, idx).await
            }

            #vis async fn #extend(
                &self,
                job: &JobId,
                values: impl IntoIterator<Item=#ty>
            ) -> std::ops::Range<#indexer> {
                self.0.#all.extend(job, values).await
            }

            #vis async fn #all<'a>(&'a self) -> impl 'a + Iterator<Item = &'a #ty> {
                self.0.#all.iter().await
            }
        ));

        indexed_field_names.push(all);
        indexed_types.push(ty);
        indexers.push(indexer);
    }

    let attrs = database_input.attrs;
    let vis = database_input.vis;

    // And finally, we construct the database struct itself
    quote!(
        #attrs
        #[derive(Clone)]
        #vis struct #db_type(std::sync::Arc<#db_inner_type>);

        struct #db_inner_type {
            #( #singles_names: hydra::tokio::sync::Mutex<Option<#singles_types>>, )*

            #( #indexed_field_names: hydra::Indexed<#indexers, #indexed_types>, )*

            #( #field_names: #db_layers, )*


            // A helper field to indicate which db layers certain jobs are in
            __active_jobs: hydra::internal::JobOwners,
            // The internal executor
            __executor: hydra::internal::Executor,
        }

        impl #db_type {
            #( #methods )*

            /// Constructs a new database, additionally spawning idle executor work threads
            #vis fn new() -> Self {
                use hydra::DBLayer;
                use hydra::internal::{JobOwners, Executor};
                use hydra::tokio::sync::Mutex;

                Self(std::sync::Arc::new(#db_inner_type {
                    #( #singles_names: Mutex::new(None), )*
                    #( #field_names: hydra::DBLayer::new(), )*
                    #( #indexed_field_names: hydra::Indexed::new(), )*

                    __active_jobs: hydra::internal::JobOwners::new(),
                    __executor: hydra::internal::Executor::new(),
                }))
            }
        }

        impl hydra::internal::Runtime for #db_type {
            fn mark_single_blocked<'a>(&'a self, job: &'a hydra::JobId, by: &'a hydra::JobId) ->
                std::pin::Pin<Box<dyn 'a + Send + Sync + ::std::future::Future<Output = Option<()>>>> {
                use std::sync::Arc;
                use hydra::JobId;

                async fn inner(this: &#db_type, job: &JobId, by: &JobId) -> Option<()> {
                    let q_kind = this.0.__active_jobs.query_kind(job).await?;

                    match q_kind {
                        #( #blocked_pats => this.0.#field_names.mark_blocked(job, by).await, )*
                        _ => panic!("unknown query kind {:?} of {} known", q_kind, #num_query_kind),
                    }
                }

                Box::pin(inner(self, job, by))
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
        vis,
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
        #vis trait #name<DB> {
            type Token;
        }

        #[doc(hidden)]
        #vis struct #token_type;

        impl #name<#db_type> for hydra::internal::Dummy {
            type Token = #token_type;
        }

        impl hydra::internal::Computable<#db_type> for #token_type {
            type Key = #key_type;
            type Value = #value_type;

            const QUERY_KIND: hydra::internal::QueryKind = hydra::internal::QueryKind(#kind_count);

            fn construct<'a>(db: #db_type, job: &'a hydra::JobId, key: Self::Key) ->
                    std::pin::Pin<Box<
                        dyn 'a + Send + Sync +
                        ::std::future::Future<Output=hydra::Result<#value_type>>
                    >>
            {
                async fn inner(#fn_args) #fn_out #body

                Box::pin(inner(db, job, key))
            }
        }
    )
    .into()
}

/// Derives `hydra::Index` for a type of the form `<vis> struct <name>(<vis> usize)`
#[proc_macro_derive(Index)]
pub fn derive_index(input: TokenStream) -> TokenStream {
    use syn::Fields;

    let struct_input = parse_macro_input!(input as ItemStruct);
    let name = struct_input.ident;

    macro_rules! malformed {
        () => {{
            return syn::Error::new(
                Span::call_site(),
                "malformed input to derive; expected a tuple struct with `usize` as its only field",
            )
            .to_compile_error()
            .into();
        }};
    }

    match struct_input.fields {
        Fields::Named(_) | Fields::Unit => malformed!(),
        Fields::Unnamed(fs) => {
            let all_fields: Vec<_> = fs.unnamed.into_iter().collect();
            match &all_fields[..] {
                [single] => match &single.ty {
                    Type::Path(p) => {
                        if p.path.segments.len() != 1 {
                            malformed!();
                        } else {
                            let last = p.path.segments.last().unwrap();
                            if last.ident.to_string() != "usize" || !last.arguments.is_empty() {
                                malformed!();
                            }
                        }
                    }
                    _ => malformed!(),
                },
                _ => malformed!(),
            }
        }
    }

    quote!(
        impl hydra::Index for #name {
            fn index<T>(self, vs: &[T]) -> &T {
                &vs[self.0]
            }

            fn from_usize(idx: usize) -> Self {
                Self(idx)
            }
        }
    )
    .into()
}

/// A helper function to get the current kind count value, then increment it
fn get_kind_count() -> u16 {
    static COUNT: AtomicU16 = AtomicU16::new(0);

    COUNT.fetch_add(1, SeqCst)
}
