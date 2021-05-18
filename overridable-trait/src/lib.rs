use std::ops::Deref;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Ident, Lifetime, ImplItemMethod, TraitItemMethod, Visibility, FnArg, GenericParam, Signature,
    Attribute,
};
use syn::{parse_macro_input, parse_quote, Token};
use syn::parse::{self, Parse, ParseStream};


mod kw {
    syn::custom_keyword!(lifetime);
    syn::custom_keyword!(overridable);
}


#[derive(Clone)]
struct MethodDef {
    inner: ImplItemMethod,
    overridable: bool,
}

impl Parse for MethodDef {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        // Handle attrs (such as doc comments) that come before the `overridable` keyword.
        let mut attrs = input.call(Attribute::parse_outer)?;
        let overridable = input.parse::<Option<kw::overridable>>()?.is_some();
        let mut inner = input.parse::<ImplItemMethod>()?;
        attrs.extend(inner.attrs);
        inner.attrs = attrs;

        Ok(MethodDef { inner, overridable })
    }
}

impl Deref for MethodDef {
    type Target = ImplItemMethod;
    fn deref(&self) -> &ImplItemMethod {
        &self.inner
    }
}


struct Args {
    lifetime: Lifetime,
    trait_name: Ident,
    struct_name: Ident,
    dyn_name: Ident,
    funcs: Vec<MethodDef>,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<kw::lifetime>()?;
        let lifetime = input.parse()?;
        input.parse::<Token![;]>()?;

        input.parse::<Token![trait]>()?;
        let trait_name = input.parse()?;
        input.parse::<Token![;]>()?;

        input.parse::<Token![struct]>()?;
        let struct_name = input.parse()?;
        input.parse::<Token![;]>()?;

        input.parse::<Token![dyn]>()?;
        let dyn_name = input.parse()?;
        input.parse::<Token![;]>()?;

        let mut funcs = Vec::new();
        while !input.is_empty() {
            funcs.push(input.parse()?);
        }

        Ok(Args {
            lifetime,
            trait_name,
            struct_name,
            dyn_name,
            funcs,
        })
    }
}


fn is_public(vis: &Visibility) -> bool {
    match vis {
        &Visibility::Public(_) => true,
        _ => false,
    }
}

fn has_generics(sig: &Signature) -> bool {
    for param in &sig.generics.params {
        match *param {
            GenericParam::Type(_) => return true,
            GenericParam::Lifetime(_) => {},
            GenericParam::Const(_) => return true,
        }
    }
    false
}


#[proc_macro]
pub fn define_overridable_trait(input: TokenStream) -> TokenStream {
    #[allow(bad_style)]
    let Args {
        lifetime: lt,
        trait_name: Trait,
        struct_name: Struct,
        dyn_name: Dyn,
        funcs,
    } = parse_macro_input!(input as Args);


    let trait_funcs = funcs.iter().filter(|f| is_public(&f.vis)).map(|f| {
        let name = &f.sig.ident;
        let args = f.sig.inputs.iter().filter_map(|arg| match arg {
            &FnArg::Receiver(_) => None,
            &FnArg::Typed(ref pt) => Some(&pt.pat),
        });

        // Functions marked `overridable` dispatch to the same function on `self.inner()`.  All
        // other functions use the provided body by default, usually resulting in one or more calls
        // to overridable functions.
        let body = if f.overridable {
            parse_quote!({
                <Self::Inner as #Trait>::#name(self.inner(), #(#args,)*)
            })
        } else {
            f.block.clone()
        };

        TraitItemMethod {
            attrs: f.attrs.clone(),
            sig: f.sig.clone(),
            default: Some(body),
            semi_token: None,
        }
    }).collect::<Vec<_>>();

    let impl_funcs_private = funcs.iter().filter(|f| !is_public(&f.vis)).map(|f| {
        f.inner.clone()
    }).collect::<Vec<_>>();

    let impl_funcs_public = funcs.iter()
        .filter(|f| is_public(&f.vis) && f.overridable)
        .map(|f| {
            ImplItemMethod {
                vis: Visibility::Inherited,
                .. f.inner.clone()
            }
        }).collect::<Vec<_>>();


    let dyn_trait_funcs = funcs.iter()
        .filter(|f| is_public(&f.vis) && !has_generics(&f.sig))
        .map(|f| {
            TraitItemMethod {
                attrs: f.attrs.clone(),
                sig: f.sig.clone(),
                default: None,
                semi_token: None,
            }
        }).collect::<Vec<_>>();

    let dyn_for_trait_impl_funcs = funcs.iter()
        .filter(|f| is_public(&f.vis) && !has_generics(&f.sig))
        .map(|f| {
            let name = &f.sig.ident;
            let args = f.sig.inputs.iter().filter_map(|arg| match arg {
                &FnArg::Receiver(_) => None,
                &FnArg::Typed(ref pt) => Some(&pt.pat),
            });

            TraitItemMethod {
                attrs: f.attrs.clone(),
                sig: f.sig.clone(),
                default: Some(parse_quote!({
                    <Self as #Trait>::#name(self, #(#args,)*)
                })),
                semi_token: None,
            }
        }).collect::<Vec<_>>();

    let trait_for_dyn_impl_funcs = funcs.iter().filter(|f| is_public(&f.vis)).map(|f| {
        let name = &f.sig.ident;
        let args = f.sig.inputs.iter().filter_map(|arg| match arg {
            &FnArg::Receiver(_) => None,
            &FnArg::Typed(ref pt) => Some(&pt.pat),
        });

        let body = if !has_generics(&f.sig) {
            // Non-generic functions can be dispatched to the inner `dyn #Trait`.
            parse_quote!({
                DynTrait::#name(&self.0, #(#args,)*)
            })
        } else {
            // Generic functions dispatch to inherent methods on `#Dyn`, which the user must define
            // separately.  If the methods are left undefined, this call will dispatch to the trait
            // method, causing infinite recursion.  Unfortunately, `rustc`'s unconditional
            // recursion lint doesn't seem to fire on this code.
            parse_quote!({
                self.#name(#(#args,)*)
            })
        };

        TraitItemMethod {
            attrs: f.attrs.clone(),
            sig: f.sig.clone(),
            default: Some(body),
            semi_token: None,
        }
    }).collect::<Vec<_>>();


    TokenStream::from(quote! {
        pub trait #Trait<#lt> {
            type Inner: #Trait<#lt> + ?Sized;
            fn inner(&self) -> &Self::Inner;
            #(#trait_funcs)*
        }

        impl<#lt> #Struct<#lt> {
            #(#impl_funcs_private)*
        }

        impl<#lt> #Trait<#lt> for #Struct<#lt> {
            type Inner = Self;
            fn inner(&self) -> &Self { self }

            #(#impl_funcs_public)*
        }


        mod __overridable_trait_dyn {
            use super::*;

            trait DynTrait<#lt> {
                #(#dyn_trait_funcs)*
            }

            impl<#lt, T: #Trait<#lt>> DynTrait<#lt> for T {
                #(#dyn_for_trait_impl_funcs)*
            }

            #[repr(transparent)]
            pub struct #Dyn<'a>(dyn DynTrait<'a> + 'a);

            impl<'a> #Dyn<'a> {
                // We isolate the unsafety into this single obviously-correct function so we can be
                // sure the compiler is checking our handling of the tricky `&'x dyn Foo<'y> + 'z`
                // lifetime situation below.
                fn from_raw<'b>(
                    x: &'b (dyn DynTrait<'a> + 'a),
                ) -> &'b #Dyn<'a> {
                    unsafe { mem::transmute(x) }
                }

                pub fn new<C: #Trait<'a> + 'a>(x: &C) -> &#Dyn<'a> {
                    #Dyn::from_raw(x as &dyn DynTrait)
                }
            }

            impl<'a> #Trait<'a> for #Dyn<'a> {
                type Inner = Self;
                fn inner(&self) -> &Self { self }

                #(#trait_for_dyn_impl_funcs)*
            }
        }

        pub use self::__overridable_trait_dyn::#Dyn;
    })
}


