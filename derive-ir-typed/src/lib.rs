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
