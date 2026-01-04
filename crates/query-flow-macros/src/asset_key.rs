use darling::{ast::NestedMeta, FromMeta};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Ident, Item, ItemStruct};

use crate::query::OutputEq;

/// Wrapper for parsing a type from attribute: `asset = String` or `asset = Vec<u8>`
#[derive(Debug)]
struct TypeWrapper(syn::Type);

/// Wrapper for parsing a list of identifiers: `key(field1, field2)`
#[derive(Debug, Default)]
struct KeyFields(Vec<Ident>);

impl FromMeta for KeyFields {
    fn from_list(items: &[NestedMeta]) -> darling::Result<Self> {
        let mut idents = Vec::new();
        for item in items {
            match item {
                NestedMeta::Meta(syn::Meta::Path(path)) => {
                    if let Some(ident) = path.get_ident() {
                        idents.push(ident.clone());
                    } else {
                        return Err(darling::Error::custom("expected field name").with_span(path));
                    }
                }
                _ => {
                    return Err(darling::Error::custom("expected field name"));
                }
            }
        }
        Ok(KeyFields(idents))
    }
}

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

    /// Fields to use for Hash/PartialEq/Eq.
    /// When specified, only these fields are used for equality/hashing.
    /// This allows other fields (e.g., counters) to be ignored.
    #[darling(default)]
    key: KeyFields,
}

pub fn generate_asset_key(attr: AssetKeyAttr, input: Item) -> Result<TokenStream, Error> {
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

    // Check if key fields are specified
    if attr.key.0.is_empty() {
        // No key fields specified: derive all traits (original behavior)
        let (name, item_tokens) = match &input {
            Item::Struct(s) => (&s.ident, quote! { #s }),
            Item::Enum(e) => (&e.ident, quote! { #e }),
            _ => return Err(Error::new_spanned(input, "expected struct or enum")),
        };

        Ok(quote! {
            #[derive(Clone, Debug, PartialEq, Eq, Hash)]
            #item_tokens

            impl ::query_flow::AssetKey for #name {
                type Asset = #asset_ty;

                #asset_eq_impl
            }
        })
    } else {
        // Key fields specified: generate custom Hash/PartialEq/Eq
        let item_struct = match &input {
            Item::Struct(s) => s,
            Item::Enum(e) => {
                return Err(Error::new_spanned(
                    e,
                    "key() is only supported for structs, not enums",
                ))
            }
            _ => return Err(Error::new_spanned(input, "expected struct")),
        };

        generate_with_key_fields(item_struct, &attr.key.0, asset_ty, asset_eq_impl)
    }
}

fn generate_with_key_fields(
    item_struct: &ItemStruct,
    key_fields: &[Ident],
    asset_ty: &syn::Type,
    asset_eq_impl: TokenStream,
) -> Result<TokenStream, Error> {
    let name = &item_struct.ident;

    // Generate hash statements for each key field
    let hash_stmts: Vec<_> = key_fields
        .iter()
        .map(|field| {
            quote! {
                self.#field.hash(state);
            }
        })
        .collect();

    // Generate equality checks for each key field
    let eq_checks: Vec<_> = key_fields
        .iter()
        .map(|field| {
            quote! {
                self.#field == other.#field
            }
        })
        .collect();

    let eq_expr = if eq_checks.is_empty() {
        quote! { true }
    } else {
        quote! { #(#eq_checks)&&* }
    };

    Ok(quote! {
        #[derive(Clone, Debug)]
        #item_struct

        impl ::std::hash::Hash for #name {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                #(#hash_stmts)*
            }
        }

        impl ::std::cmp::PartialEq for #name {
            fn eq(&self, other: &Self) -> bool {
                #eq_expr
            }
        }

        impl ::std::cmp::Eq for #name {}

        impl ::query_flow::AssetKey for #name {
            type Asset = #asset_ty;

            #asset_eq_impl
        }
    })
}
