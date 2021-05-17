use proc_macro::TokenStream;
use quote::quote;
use syn::{Ident, Lifetime, ImplItemMethod, TraitItemMethod, Visibility, FnArg, GenericParam};
use syn::{parse_macro_input, parse_quote, Token};
use syn::parse::{self, Parse, ParseStream};

mod kw {
    syn::custom_keyword!(lifetime);
}

struct Args {
    lifetime: Lifetime,
    trait_name: Ident,
    dyn_trait_name: Ident,
    struct_name: Ident,
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

        input.parse::<Token![dyn]>()?;
        input.parse::<Token![trait]>()?;
        let dyn_trait_name = input.parse()?;
        input.parse::<Token![;]>()?;

        input.parse::<Token![struct]>()?;
        let struct_name = input.parse()?;
        input.parse::<Token![;]>()?;

        let mut funcs = Vec::new();
        while !input.is_empty() {
            funcs.push(input.parse()?);
        }

        Ok(Args {
            lifetime,
            trait_name,
            dyn_trait_name,
            struct_name,
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

#[proc_macro]
pub fn define_overridable_trait(input: TokenStream) -> TokenStream {
    let Args {
        lifetime: lt,
        trait_name,
        dyn_trait_name,
        struct_name,
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
                <Self::Inner as #trait_name>::#name(self.inner(), #(#args,)*)
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


    let dyn_funcs = funcs.iter().filter(|f| {
        if !is_public(&f.vis) {
            return false;
        }
        for param in &f.sig.generics.params {
            match *param {
                GenericParam::Type(_) => return false,
                GenericParam::Lifetime(_) => {},
                GenericParam::Const(_) => return false,
            }
        }
        true
    }).collect::<Vec<&_>>();

    let dyn_trait_funcs = dyn_funcs.iter().cloned().map(|f| {
        TraitItemMethod {
            attrs: f.attrs.clone(),
            sig: f.sig.clone(),
            default: None,
            semi_token: Some(Default::default()),
        }
    }).collect::<Vec<_>>();

    let dyn_impl_funcs = dyn_funcs.iter().cloned().map(|f| {
        let name = &f.sig.ident;
        let args = f.sig.inputs.iter().filter_map(|arg| match arg {
            &FnArg::Receiver(_) => None,
            &FnArg::Typed(ref pt) => Some(&pt.pat),
        });
        ImplItemMethod {
            vis: Visibility::Inherited,
            block: parse_quote!({
                <Self as #trait_name>::#name(self, #(#args,)*)
            }),
            .. f.clone()
        }
    }).collect::<Vec<_>>();


    TokenStream::from(quote! {
        #[doc(hidden)]
        mod __overridable_trait {
            use super::*;

            // Dummy trait, taking precedence over the glob-import of super::#dyn_trait_name.
            trait #dyn_trait_name {}

            pub trait #trait_name<#lt> {
                type Inner: #trait_name<#lt>;
                fn inner(&self) -> &Self::Inner;
                #(#trait_funcs)*
            }

            impl<#lt> #struct_name<#lt> {
                #(#impl_funcs_private)*
            }

            impl<#lt> #trait_name<#lt> for #struct_name<#lt> {
                type Inner = Self;
                fn inner(&self) -> &Self { self }

                #(#impl_funcs_public)*
            }
        }

        pub use self::__overridable_trait::#trait_name;

        pub trait #dyn_trait_name<#lt> {
            #(#dyn_trait_funcs)*
        }

        impl<#lt, T: #trait_name<#lt>> #dyn_trait_name<#lt> for T {
            #(#dyn_impl_funcs)*
        }
    })
}


