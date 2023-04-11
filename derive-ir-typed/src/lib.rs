use std::collections::HashSet;
use proc_macro;
use proc_macro2::{TokenStream, Span};
use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote, DeriveInput, Ident, Generics, AngleBracketedGenericArguments,
    Lifetime, LifetimeDef, GenericArgument, Type, Data, Fields, WhereClause, TypePath, Member,
};
use syn::visit_mut::{self, VisitMut};

#[proc_macro_derive(FromWireList)]
pub fn derive_from_wire_list(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let repr_name = Ident::new(&format!("{}Repr", name), name.span());

    let (_impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let impl_params = &input.generics.params;

    let s = match input.data {
        Data::Struct(ref s) => s,
        _ => panic!("#[derive(FromWireList)] is supported only on structs"),
    };

    let field_names = s.fields.iter().enumerate().map(|(i, f)| {
        match f.ident.clone() {
            Some(ident) => Member::Named(ident),
            None => Member::Unnamed(i.into()),
        }
    }).collect::<Vec<_>>();
    let field_tys = s.fields.iter().map(|f| &f.ty).collect::<Vec<_>>();

    let result = quote! {
        impl<'a, #impl_params> FromWireList<'a> for #name #ty_generics #where_clause {
            fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
                #( <#field_tys as FromWireList<'a>>::expected_num_wires(sizes) + )*
                0
            }

            fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                c: &C,
                sizes: &mut impl Iterator<Item = usize>,
                build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
            ) -> Self::Repr {
                type SelfRepr<'a> = <#name #ty_generics as Repr<'a>>::Repr;

                SelfRepr {
                    #( #field_names: TWire::<#field_tys>::new(
                        <#field_tys as FromWireList<'a>>::build_repr_from_wires(
                            c, sizes, build_wire),
                    ), )*
                }
            }
        }
    };
    //eprintln!("result: {}", result);
    result.into()
}

#[proc_macro_derive(ToWireList)]
pub fn derive_to_wire_list(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let repr_name = Ident::new(&format!("{}Repr", name), name.span());

    let (_impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let impl_params = &input.generics.params;

    let s = match input.data {
        Data::Struct(ref s) => s,
        _ => panic!("#[derive(ToWireList)] is supported only on structs"),
    };

    let field_names = s.fields.iter().enumerate().map(|(i, f)| {
        match f.ident.clone() {
            Some(ident) => Member::Named(ident),
            None => Member::Unnamed(i.into()),
        }
    }).collect::<Vec<_>>();
    let field_tys = s.fields.iter().map(|f| &f.ty).collect::<Vec<_>>();

    let result = quote! {
        impl<'a, #impl_params> ToWireList<'a> for #name #ty_generics #where_clause {
            fn num_wires(x: &Self::Repr) -> usize {
                #( <#field_tys as ToWireList<'a>>::num_wires(&x.#field_names) + )*
                0
            }
            fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                #( <#field_tys as ToWireList<'a>>::for_each_wire(&x.#field_names, |w| f(w)); )*
            }
            fn num_sizes(x: &Self::Repr) -> usize {
                #( <#field_tys as ToWireList<'a>>::num_sizes(&x.#field_names) + )*
                0
            }
            fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
                #( <#field_tys as ToWireList<'a>>::for_each_size(&x.#field_names, |s| f(s)); )*
            }
        }
    };
    //eprintln!("result: {}", result);
    result.into()
}

#[proc_macro_derive(LazySecret)]
pub fn derive_lazy_secret(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let repr_name = Ident::new(&format!("{}Repr", name), name.span());

    let (_impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let impl_params = &input.generics.params;

    let s = match input.data {
        Data::Struct(ref s) => s,
        _ => panic!("#[derive(LazySecret)] is supported only on structs"),
    };

    let field_names = s.fields.iter().enumerate().map(|(i, f)| {
        match f.ident.clone() {
            Some(ident) => Member::Named(ident),
            None => Member::Unnamed(i.into()),
        }
    }).collect::<Vec<_>>();
    let field_tys = s.fields.iter().map(|f| &f.ty).collect::<Vec<_>>();

    let result = quote! {
        impl<'a, #impl_params> LazySecret<'a> for #name #ty_generics #where_clause {
            fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
                #( <#field_tys as LazySecret<'a>>::expected_word_len(sizes) + )*
                0
            }
            fn word_len(&self) -> usize {
                #( <#field_tys as LazySecret<'a>>::word_len(&self.#field_names) + )*
                0
            }
            fn push_words(&self, out: &mut Vec<u32>) {
                #( <#field_tys as LazySecret<'a>>::push_words(&self.#field_names, out); )*
            }
        }
    };
    //eprintln!("result: {}", result);
    result.into()
}
