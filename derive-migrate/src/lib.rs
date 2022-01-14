use std::collections::HashSet;
use proc_macro;
use proc_macro2::{TokenStream, Span};
use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote, DeriveInput, Ident, Generics, AngleBracketedGenericArguments,
    Lifetime, LifetimeDef, GenericArgument, Type, Data, Fields, WhereClause, TypePath,
};
use syn::visit_mut::{self, VisitMut};

#[proc_macro_derive(Migrate)]
pub fn derive_migrate(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;

    let lt1_def = match input.generics.lifetimes().next() {
        Some(def) => def,
        None => {
            return impl_migrate_trivial_generic(&input.ident, &input.generics).into();
        },
    };
    let lt1 = &lt1_def.lifetime;
    let lt2 = Lifetime {
        apostrophe: lt1.apostrophe,
        ident: Ident::new(&format!("{}_new", lt1.ident), lt1.ident.span()),
    };
    let lt2_def = LifetimeDef {
        attrs: lt1_def.attrs.clone(),
        lifetime: lt2.clone(),
        colon_token: lt1_def.colon_token.clone(),
        bounds: lt1_def.bounds.clone(),
    };

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let impl_generics = syn::parse::<Generics>(impl_generics.to_token_stream().into()).unwrap();
    assert!(impl_generics.where_clause.is_none());
    let impl_params = impl_generics.params;

    let ty_generics = syn::parse::<AngleBracketedGenericArguments>(
        ty_generics.to_token_stream().into()).unwrap();
    let ty_args1 = ty_generics.args;
    let mut ty_args2 = ty_args1.clone();
    ty_args2[0] = GenericArgument::Lifetime(lt2.clone());


    let mut where_clause = where_clause.cloned();
    let generic_params = input.generics.type_params().map(|tp| tp.ident.clone())
        .collect::<HashSet<_>>();
    let body = match input.data {
        Data::Struct(ref s) => {
            for f in s.fields.iter() {
                add_migrate_bound(&mut where_clause, &lt1, &lt2, &generic_params, &f.ty);
            }
            let pat = match_fields(quote! { #name }, &s.fields);
            let expr = visit_fields(quote! { #name }, &s.fields);
            quote! {
                let #pat = self;
                #expr
            }
        },
        Data::Enum(ref e) => {
            let cases = e.variants.iter().map(|v| {
                for f in v.fields.iter() {
                    add_migrate_bound(&mut where_clause, &lt1, &lt2, &generic_params, &f.ty);
                }
                let v_name = &v.ident;
                let pat = match_fields(quote! { #name::#v_name }, &v.fields);
                let expr = visit_fields(quote! { #name::#v_name }, &v.fields);
                quote! { #pat => #expr, }
            }).collect::<Vec<_>>();
            quote! { match self { #(#cases)* } }
        },
        Data::Union(_) => {
            panic!("#[derive(Migrate)] is not supported on unions");
        },
    };


    let result = quote! {
        impl<#lt2_def, #impl_params> Migrate<#lt1, #lt2> for #name<#ty_args1> #where_clause {
            type Output = #name<#ty_args2>;
            fn migrate<V: migrate::Visitor<#lt1, #lt2> + ?Sized>(self, v: &mut V) -> Self::Output {
                #body
            }
        }
    };
    //eprintln!("result: {}", result);
    result.into()
}

fn match_fields(name: TokenStream, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(ref fs) => {
            let field_names = fs.named.iter()
                .map(|f| f.ident.clone().expect("named field has no name?"))
                .collect::<Vec<_>>();
            quote! {
                #name { #( #field_names, )* }
            }
        },
        Fields::Unnamed(ref fs) => {
            let field_names = (0 .. fs.unnamed.len())
                .map(|i| Ident::new(&format!("x{}", i), Span::call_site()))
                .collect::<Vec<_>>();
            quote! {
                #name(#( #field_names, )*)
            }
        },
        Fields::Unit => {
            quote! { #name }
        },
    }
}

fn visit_fields(name: TokenStream, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(ref fs) => {
            let field_names = fs.named.iter()
                .map(|f| f.ident.clone().expect("named field has no name?"))
                .collect::<Vec<_>>();
            quote! {
                #name { #( #field_names: v.visit(#field_names), )* }
            }
        },
        Fields::Unnamed(ref fs) => {
            let field_names = (0 .. fs.unnamed.len())
                .map(|i| Ident::new(&format!("x{}", i), Span::call_site()))
                .collect::<Vec<_>>();
            quote! {
                #name(#( v.visit(#field_names), )*)
            }
        },
        Fields::Unit => {
            quote! { #name }
        },
    }
}

fn add_migrate_bound(
    where_clause: &mut Option<WhereClause>,
    lt1: &Lifetime,
    lt2: &Lifetime,
    generic_params: &HashSet<Ident>,
    ty: &Type,
) {
    let mut new_ty = ty.clone();
    struct Visitor<'a> {
        generic_params: &'a HashSet<Ident>,
        old: &'a Lifetime,
        new: &'a Lifetime,
        has_param: bool,
    }
    impl VisitMut for Visitor<'_> {
        fn visit_lifetime_mut(&mut self, i: &mut Lifetime) {
            if i.ident == self.old.ident {
                *i = self.new.clone();
            }
            visit_mut::visit_lifetime_mut(self, i);
        }

        fn visit_type_path_mut(&mut self, i: &mut TypePath) {
            if i.qself.is_none() &&
                    i.path.leading_colon.is_none() &&
                    i.path.segments.len() == 1 &&
                    self.generic_params.contains(&i.path.segments.last().unwrap().ident) {
                self.has_param = true;
            }
            visit_mut::visit_type_path_mut(self, i);
        }
    }
    let mut v = Visitor { generic_params, old: lt1, new: lt2, has_param: false };
    visit_mut::visit_type_mut(&mut v, &mut new_ty);
    if !v.has_param {
        // Only generate a bound if the type mentions a generic parameter.
        return;
    }

    let pred = parse_quote! { #ty: Migrate<#lt1, #lt2, Output = #new_ty> };
    match where_clause {
        Some(ref mut x) => {
            x.predicates.push(pred);
        },
        None => {
            *where_clause = Some(WhereClause {
                where_token: Default::default(),
                predicates: vec![pred].into_iter().collect(),
            });
        },
    }
}

/// Generate a trivial `Migrate` impl for types that don't contain any references.
fn impl_migrate_trivial_generic(name: &Ident, generics: &Generics) -> TokenStream {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let impl_generics = syn::parse::<Generics>(impl_generics.to_token_stream().into()).unwrap();
    assert!(impl_generics.where_clause.is_none());
    let impl_params = impl_generics.params;

    quote! {
        impl<'lt1, 'lt2, #impl_params> Migrate<'lt1, 'lt2> for #name #ty_generics #where_clause {
            type Output = Self;
            fn migrate<V: migrate::Visitor<'lt1, 'lt2> + ?Sized>(self, v: &mut V) -> Self::Output {
                self
            }
        }
    }
}


#[proc_macro]
pub fn impl_migrate_trivial(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ty = parse_macro_input!(input as Type);

    let result = quote! {
        impl<'a, 'b> Migrate<'a, 'b> for #ty {
            type Output = Self;
            fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
                self
            }
        }
    };
    result.into()
}
