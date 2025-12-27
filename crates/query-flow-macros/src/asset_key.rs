use darling::FromMeta;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, ItemStruct};

use crate::query::OutputEq;

/// Named durability levels for assets.
#[derive(Debug, Clone, Copy, Default)]
enum DurabilityAttr {
    #[default]
    Volatile,
    Session,
    Stable,
    Constant,
}

impl FromMeta for DurabilityAttr {
    fn from_string(value: &str) -> darling::Result<Self> {
        Self::parse_str(value)
    }

    fn from_expr(expr: &syn::Expr) -> darling::Result<Self> {
        // Handle identifier like `constant` without quotes
        if let syn::Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                return Self::parse_str(&ident.to_string());
            }
        }
        Err(darling::Error::custom(
            "expected durability level: volatile, session, stable, or constant",
        ))
    }
}

impl DurabilityAttr {
    fn parse_str(value: &str) -> darling::Result<Self> {
        match value.to_lowercase().as_str() {
            "volatile" => Ok(DurabilityAttr::Volatile),
            "session" => Ok(DurabilityAttr::Session),
            "stable" => Ok(DurabilityAttr::Stable),
            "constant" => Ok(DurabilityAttr::Constant),
            _ => Err(darling::Error::unknown_value(value)),
        }
    }
}

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

    /// Durability level. Default: volatile.
    #[darling(default)]
    durability: DurabilityAttr,

    /// Asset equality for early cutoff optimization.
    /// Default: uses PartialEq (`old == new`).
    /// `asset_eq = path`: uses custom function for types without PartialEq.
    #[darling(default)]
    asset_eq: OutputEq,
}

pub fn generate_asset_key(
    attr: AssetKeyAttr,
    input_struct: ItemStruct,
) -> Result<TokenStream, Error> {
    let struct_name = &input_struct.ident;
    let asset_ty = &attr.asset.0;

    // Generate durability method
    let durability_impl = match attr.durability {
        DurabilityAttr::Volatile => quote! {
            fn durability(&self) -> ::query_flow::DurabilityLevel {
                ::query_flow::DurabilityLevel::Volatile
            }
        },
        DurabilityAttr::Session => quote! {
            fn durability(&self) -> ::query_flow::DurabilityLevel {
                ::query_flow::DurabilityLevel::Session
            }
        },
        DurabilityAttr::Stable => quote! {
            fn durability(&self) -> ::query_flow::DurabilityLevel {
                ::query_flow::DurabilityLevel::Stable
            }
        },
        DurabilityAttr::Constant => quote! {
            fn durability(&self) -> ::query_flow::DurabilityLevel {
                ::query_flow::DurabilityLevel::Constant
            }
        },
    };

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
        #input_struct

        impl ::query_flow::AssetKey for #struct_name {
            type Asset = #asset_ty;

            #asset_eq_impl
            #durability_impl
        }
    })
}
