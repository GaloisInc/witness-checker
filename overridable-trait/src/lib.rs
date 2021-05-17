use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Ident, Lifetime, ImplItemMethod, TraitItemMethod, Visibility, FnArg, GenericParam, Signature,
};
use syn::{parse_macro_input, parse_quote, Token};
use syn::parse::{self, Parse, ParseStream};

mod kw {
    syn::custom_keyword!(lifetime);
}

struct Args {
    lifetime: Lifetime,
    trait_name: Ident,
    struct_name: Ident,
    dyn_name: Ident,
    funcs: Vec<ImplItemMethod>,
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

        TraitItemMethod {
            attrs: f.attrs.clone(),
            sig: f.sig.clone(),
            default: Some(parse_quote!({
                <Self::Inner as #Trait>::#name(self.inner(), #(#args,)*)
                //self.inner().#name(#(#args,)*)
            })),
            semi_token: None,
        }
    }).collect::<Vec<_>>();

    let impl_funcs_private = funcs.iter().filter(|f| !is_public(&f.vis)).map(|f| {
        f.clone()
    }).collect::<Vec<_>>();

    let impl_funcs_public = funcs.iter().filter(|f| is_public(&f.vis)).map(|f| {
        ImplItemMethod {
            vis: Visibility::Inherited,
            .. f.clone()
        }
    }).collect::<Vec<_>>();


    let no_inner_impl_funcs = funcs.iter().filter(|f| is_public(&f.vis)).map(|f| {
        let name = &f.sig.ident;
        let args = f.sig.inputs.iter().filter_map(|arg| match arg {
            &FnArg::Receiver(_) => None,
            &FnArg::Typed(ref pt) => Some(&pt.pat),
        });
        ImplItemMethod {
            vis: Visibility::Inherited,
            block: parse_quote!({
                <TT as #Trait>::#name(&self.0, #(#args,)*)
            }),
            .. f.clone()
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
                self.0.#name(#(#args,)*)
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
            type Inner: #Trait<#lt>;
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


        pub enum VoidInner {}
        impl<#lt> #Trait<#lt> for VoidInner {
            type Inner = Self;
            fn inner(&self) -> &VoidInner {
                panic!("called inner() on VoidInner")
            }
        }

        #[repr(transparent)]
        struct NoInner<T>(T);

        // Note the name of the type parameter used here must not conflict with the generics of any
        // of the methods.
        impl<#lt, TT: #Trait<#lt>> #Trait<#lt> for NoInner<TT> {
            type Inner = VoidInner;
            fn inner(&self) -> &VoidInner {
                panic!("called inner() on NoInner<T>")
            }

            #(#no_inner_impl_funcs)*
        }

        impl<'a, T> From<&'a T> for &'a NoInner<T> {
            fn from(x: &'a T) -> &'a NoInner<T> {
                unsafe { std::mem::transmute(x) }
            }
        }


        #[repr(transparent)]
        pub struct #Dyn<'a>(dyn #Trait<'a, Inner=VoidInner> + 'a);

        impl<'a> #Dyn<'a> {
            // We isolate the unsafety into this single obviously-correct function so we can be
            // sure the compiler is checking our handling of the tricky `&'x dyn Foo<'y> + 'z`
            // lifetime situation below.
            fn from_raw<'b>(
                x: &'b (dyn #Trait<'a, Inner=VoidInner> + 'a),
            ) -> &'b #Dyn<'a> {
                unsafe { mem::transmute(x) }
            }
        }

        impl<'a, 'b, C: #Trait<'a> + 'a> From<&'b C> for &'b #Dyn<'a> {
            fn from(x: &'b C) -> &'b #Dyn<'a> {
                let y = <&NoInner<C>>::from(x);
                #Dyn::from_raw(y as &dyn #Trait<Inner=VoidInner>)
            }
        }

        impl<'a> #Trait<'a> for #Dyn<'a> {
            type Inner = VoidInner;
            fn inner(&self) -> &VoidInner {
                panic!("shouldn't use `inner` on Dyn")
            }

            #(#trait_for_dyn_impl_funcs)*
        }
    })
}


