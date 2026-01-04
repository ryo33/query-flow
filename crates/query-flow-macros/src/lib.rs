//! Procedural macros for query-flow.
//!
//! This crate provides attribute macros for defining queries and asset keys
//! with minimal boilerplate.
//!
//! # Query Example
//!
//! ```ignore
//! use query_flow::{query, Db, QueryError};
//!
//! #[query]
//! pub fn add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
//!     Ok(a + b)
//! }
//!
//! // Generates:
//! // pub struct Add { pub a: i32, pub b: i32 }
//! // impl Query for Add { ... }
//! ```
//!
//! # Asset Key Example
//!
//! ```ignore
//! use query_flow::asset_key;
//!
//! #[asset_key(asset = String)]
//! pub struct ConfigFile(pub PathBuf);
//!
//! // Generates:
//! // impl AssetKey for ConfigFile { type Asset = String; ... }
//! ```

mod asset_key;
mod query;

use darling::{ast::NestedMeta, FromMeta as _};
use proc_macro::TokenStream;
use syn::{parse_macro_input, Item, ItemFn};

use crate::{
    asset_key::{generate_asset_key, AssetKeyAttr},
    query::{generate_query, QueryAttr},
};

/// Define a query from a function.
///
/// # Attributes
///
/// - `output_eq = path`: Custom equality function (default: PartialEq)
/// - `keys(a, b, ...)`: Specify which params form the cache key
/// - `name = "Name"`: Override generated struct name
///
/// # Example
///
/// ```ignore
/// use query_flow::{query, Db, QueryError};
///
/// // Basic query - all params are keys
/// #[query]
/// fn add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
///     Ok(a + b)
/// }
///
/// // With options
/// #[query(keys(id))]
/// pub fn fetch_user(db: &impl Db, id: u64, include_deleted: bool) -> Result<User, QueryError> {
///     // include_deleted is NOT part of the cache key
///     Ok(load_user(id, include_deleted))
/// }
/// ```
#[proc_macro_attribute]
pub fn query(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr_args = match NestedMeta::parse_meta_list(attr.into()) {
        Ok(v) => v,
        Err(e) => return TokenStream::from(e.to_compile_error()),
    };

    let attr = match QueryAttr::from_list(&attr_args) {
        Ok(v) => v,
        Err(e) => return TokenStream::from(e.write_errors()),
    };

    let input_fn = parse_macro_input!(item as ItemFn);

    match generate_query(attr, input_fn) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Define an asset key type.
///
/// # Attributes
///
/// - `asset = Type`: The asset type this key loads (required)
/// - `asset_eq`: Use PartialEq for asset comparison (default)
/// - `asset_eq = path`: Use custom function for asset comparison
///
/// Durability is specified when calling `resolve_asset()`, not on the type.
///
/// # Example
///
/// ```ignore
/// use query_flow::{asset_key, DurabilityLevel};
/// use std::path::PathBuf;
///
/// #[asset_key(asset = String)]
/// pub struct ConfigFile(pub PathBuf);
///
/// // Custom equality
/// #[asset_key(asset = ImageData, asset_eq = image_bytes_eq)]
/// pub struct TexturePath(pub String);
///
/// // When resolving:
/// runtime.resolve_asset(ConfigFile(path), content, DurabilityLevel::Volatile);
/// ```
#[proc_macro_attribute]
pub fn asset_key(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr_args = match NestedMeta::parse_meta_list(attr.into()) {
        Ok(v) => v,
        Err(e) => return TokenStream::from(e.to_compile_error()),
    };

    let attr = match AssetKeyAttr::from_list(&attr_args) {
        Ok(v) => v,
        Err(e) => return TokenStream::from(e.write_errors()),
    };

    let input = parse_macro_input!(item as Item);

    match generate_asset_key(attr, input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
