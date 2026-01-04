use darling::FromMeta;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Item};

use crate::query::OutputEq;

/// Wrapper for parsing a type from attribute: `asset = String` or `asset = Vec<u8>`
#[derive(Debug)]
struct TypeWrapper(syn::Type);

impl FromMeta for TypeWrapper {
    fn from_expr(expr: &syn::Expr) -> darling::Result<Self> {
        // Convert expression to token stream and parse as type
        let tokens = quote! { #expr };
        syn::parse2::<syn::Type>(tokens)
            .map(TypeWrapper)
            .map_err(|e| darling::Error::custom(format!("invalid type: {}", e)))
    }
}

/// Options for the `#[asset_key]` attribute.
#[derive(Debug, FromMeta)]
pub struct AssetKeyAttr {
    /// The asset type this key loads (required).
    asset: TypeWrapper,

    /// Asset equality for early cutoff optimization.
    /// Default: uses PartialEq (`old == new`).
    /// `asset_eq = path`: uses custom function for types without PartialEq.
    #[darling(default)]
    asset_eq: OutputEq,
}

pub fn generate_asset_key(attr: AssetKeyAttr, input: Item) -> Result<TokenStream, Error> {
    let (name, item_tokens) = match &input {
        Item::Struct(s) => (&s.ident, quote! { #s }),
        Item::Enum(e) => (&e.ident, quote! { #e }),
        _ => return Err(Error::new_spanned(input, "expected struct or enum")),
    };

    let asset_ty = &attr.asset.0;

    // Generate asset_eq method
    let asset_eq_impl = match &attr.asset_eq {
        OutputEq::None | OutputEq::PartialEq => quote! {
            fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
                old == new
            }
        },
        OutputEq::Custom(custom_fn) => quote! {
            fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
                #custom_fn(old, new)
            }
        },
    };

    Ok(quote! {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        #item_tokens

        impl ::query_flow::AssetKey for #name {
            type Asset = #asset_ty;

            #asset_eq_impl
        }
    })
}
