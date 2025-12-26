//! Procedural macros for query-flow.
//!
//! This crate provides attribute macros for defining queries and asset keys
//! with minimal boilerplate.
//!
//! # Query Example
//!
//! ```ignore
//! use query_flow::{query, QueryContext, QueryError};
//!
//! #[query]
//! pub fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
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
//! #[asset_key(asset = String, durability = constant)]
//! pub struct BundledAsset(pub PathBuf);
//!
//! // Generates:
//! // impl AssetKey for ConfigFile { type Asset = String; ... }
//! ```

use darling::{ast::NestedMeta, FromMeta};
use heck::ToUpperCamelCase;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, spanned::Spanned, Error, FnArg, Ident, ItemFn, ItemStruct, Pat, PatType,
    ReturnType, Type, Visibility,
};

/// Wrapper for parsing a list of identifiers: `keys(a, b, c)`
#[derive(Debug, Default)]
struct Keys(Vec<Ident>);

impl FromMeta for Keys {
    fn from_list(items: &[NestedMeta]) -> darling::Result<Self> {
        let mut idents = Vec::new();
        for item in items {
            match item {
                NestedMeta::Meta(syn::Meta::Path(path)) => {
                    if let Some(ident) = path.get_ident() {
                        idents.push(ident.clone());
                    } else {
                        return Err(darling::Error::custom("expected identifier").with_span(path));
                    }
                }
                _ => {
                    return Err(darling::Error::custom("expected identifier"));
                }
            }
        }
        Ok(Keys(idents))
    }
}

/// Output equality option: `output_eq` or `output_eq = path`
#[derive(Debug, Default)]
enum OutputEq {
    #[default]
    None,
    /// `output_eq` - use PartialEq
    PartialEq,
    /// `output_eq = path` - use custom function
    Custom(syn::Path),
}

impl FromMeta for OutputEq {
    fn from_word() -> darling::Result<Self> {
        Ok(OutputEq::PartialEq)
    }

    fn from_value(value: &syn::Lit) -> darling::Result<Self> {
        Err(darling::Error::unexpected_lit_type(value))
    }

    fn from_meta(item: &syn::Meta) -> darling::Result<Self> {
        match item {
            syn::Meta::Path(_) => Ok(OutputEq::PartialEq),
            syn::Meta::NameValue(nv) => {
                if let syn::Expr::Path(expr_path) = &nv.value {
                    Ok(OutputEq::Custom(expr_path.path.clone()))
                } else {
                    Err(darling::Error::custom("expected path").with_span(&nv.value))
                }
            }
            syn::Meta::List(_) => Err(darling::Error::unsupported_format("list")),
        }
    }
}

/// Options for the `#[query]` attribute.
#[derive(Debug, Default, FromMeta)]
struct QueryAttr {
    /// Durability level (0-255). Default: 0 (volatile).
    #[darling(default)]
    durability: Option<u8>,

    /// Output equality for early cutoff optimization.
    /// Default: uses PartialEq (`old == new`).
    /// `output_eq = path`: uses custom function for types without PartialEq.
    #[darling(default)]
    output_eq: OutputEq,

    /// Params that form the cache key. Default: all params except ctx.
    #[darling(default)]
    keys: Keys,

    /// Override the generated struct name. Default: PascalCase of function name.
    #[darling(default)]
    name: Option<String>,
}

/// A parsed function parameter.
struct Param {
    name: Ident,
    ty: Type,
}

/// Parsed function information.
struct ParsedFn {
    vis: Visibility,
    name: Ident,
    params: Vec<Param>,
    output_ty: Type,
    body: TokenStream2,
}

/// Define a query from a function.
///
/// # Attributes
///
/// - `durability = N`: Set durability level (0-255, default 0)
/// - `output_eq = path`: Custom equality function (default: PartialEq)
/// - `keys(a, b, ...)`: Specify which params form the cache key
/// - `name = "Name"`: Override generated struct name
///
/// # Example
///
/// ```ignore
/// use query_flow::{query, QueryContext, QueryError};
///
/// // Basic query - all params are keys
/// #[query]
/// fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
///     Ok(a + b)
/// }
///
/// // With options
/// #[query(durability = 2, keys(id))]
/// pub fn fetch_user(ctx: &mut QueryContext, id: u64, include_deleted: bool) -> Result<User, QueryError> {
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

fn generate_query(attr: QueryAttr, input_fn: ItemFn) -> Result<TokenStream2, Error> {
    // Parse the function
    let parsed = parse_function(&input_fn)?;

    // Determine struct name
    let struct_name = match &attr.name {
        Some(name) => format_ident!("{}", name),
        None => format_ident!("{}", parsed.name.to_string().to_upper_camel_case()),
    };

    // Determine which params are keys
    let key_params: Vec<&Param> = if attr.keys.0.is_empty() {
        // Default: all params are keys
        parsed.params.iter().collect()
    } else {
        // Validate that specified keys exist
        for key in &attr.keys.0 {
            if !parsed.params.iter().any(|p| p.name == *key) {
                return Err(Error::new(
                    key.span(),
                    format!("unknown parameter `{}` in keys", key),
                ));
            }
        }
        parsed
            .params
            .iter()
            .filter(|p| attr.keys.0.contains(&p.name))
            .collect()
    };

    // Generate struct definition
    let struct_def = generate_struct(&parsed, &struct_name);

    // Generate Query impl
    let query_impl = generate_query_impl(&parsed, &struct_name, &key_params, &attr)?;

    Ok(quote! {
        #struct_def
        #query_impl
    })
}

fn parse_function(input_fn: &ItemFn) -> Result<ParsedFn, Error> {
    let vis = input_fn.vis.clone();
    let name = input_fn.sig.ident.clone();

    // Check that first param is ctx: &mut QueryContext
    let mut iter = input_fn.sig.inputs.iter();
    let first_param = iter.next().ok_or_else(|| {
        Error::new(
            input_fn.sig.span(),
            "query function must have `ctx: &mut QueryContext` as first parameter",
        )
    })?;

    validate_ctx_param(first_param)?;

    // Parse remaining params
    let mut params = Vec::new();
    for arg in iter {
        match arg {
            FnArg::Typed(pat_type) => {
                let param = parse_param(pat_type)?;
                params.push(param);
            }
            FnArg::Receiver(_) => {
                return Err(Error::new(arg.span(), "query functions cannot have `self`"));
            }
        }
    }

    // Parse return type - must be Result<T, QueryError>
    let output_ty = parse_return_type(&input_fn.sig.output)?;

    // Get function body
    let body = &input_fn.block;
    let body_tokens = quote! { #body };

    Ok(ParsedFn {
        vis,
        name,
        params,
        output_ty,
        body: body_tokens,
    })
}

fn validate_ctx_param(arg: &FnArg) -> Result<(), Error> {
    match arg {
        FnArg::Typed(pat_type) => {
            // Check parameter name is 'ctx'
            if let Pat::Ident(pat_ident) = &*pat_type.pat {
                if pat_ident.ident != "ctx" {
                    return Err(Error::new(
                        pat_ident.ident.span(),
                        "first parameter must be named `ctx`",
                    ));
                }
            }
            // Type checking is complex, we'll trust the user
            Ok(())
        }
        FnArg::Receiver(_) => Err(Error::new(
            arg.span(),
            "first parameter must be `ctx: &mut QueryContext`, not `self`",
        )),
    }
}

fn parse_param(pat_type: &PatType) -> Result<Param, Error> {
    let name = match &*pat_type.pat {
        Pat::Ident(pat_ident) => pat_ident.ident.clone(),
        _ => {
            return Err(Error::new(
                pat_type.pat.span(),
                "expected simple identifier pattern",
            ))
        }
    };

    let ty = (*pat_type.ty).clone();

    Ok(Param { name, ty })
}

fn parse_return_type(ret: &ReturnType) -> Result<Type, Error> {
    match ret {
        ReturnType::Default => Err(Error::new(
            ret.span(),
            "query function must return `Result<T, QueryError>`",
        )),
        ReturnType::Type(_, ty) => {
            // Extract T from Result<T, QueryError>
            // We need to parse the type and extract the first generic arg
            extract_result_ok_type(ty)
        }
    }
}

fn extract_result_ok_type(ty: &Type) -> Result<Type, Error> {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            if segment.ident == "Result" {
                if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                    if let Some(syn::GenericArgument::Type(ok_ty)) = args.args.first() {
                        return Ok(ok_ty.clone());
                    }
                }
            }
        }
    }
    Err(Error::new(
        ty.span(),
        "expected `Result<T, QueryError>` return type",
    ))
}

fn generate_struct(parsed: &ParsedFn, struct_name: &Ident) -> TokenStream2 {
    let vis = &parsed.vis;
    let fields: Vec<_> = parsed
        .params
        .iter()
        .map(|p| {
            let name = &p.name;
            let ty = &p.ty;
            quote! { pub #name: #ty }
        })
        .collect();

    let field_names: Vec<_> = parsed.params.iter().map(|p| &p.name).collect();
    let field_types: Vec<_> = parsed.params.iter().map(|p| &p.ty).collect();

    let new_impl = if parsed.params.is_empty() {
        quote! {
            impl #struct_name {
                /// Create a new query instance.
                #vis fn new() -> Self {
                    Self {}
                }
            }

            impl ::std::default::Default for #struct_name {
                fn default() -> Self {
                    Self::new()
                }
            }
        }
    } else {
        quote! {
            impl #struct_name {
                /// Create a new query instance.
                #vis fn new(#( #field_names: #field_types ),*) -> Self {
                    Self { #( #field_names ),* }
                }
            }
        }
    };

    quote! {
        #[derive(Clone, Debug)]
        #vis struct #struct_name {
            #( #fields ),*
        }

        #new_impl
    }
}

fn generate_query_impl(
    parsed: &ParsedFn,
    struct_name: &Ident,
    key_params: &[&Param],
    attr: &QueryAttr,
) -> Result<TokenStream2, Error> {
    let output_ty = &parsed.output_ty;

    // Generate CacheKey type
    let cache_key_ty = match key_params.len() {
        0 => quote! { () },
        1 => {
            let ty = &key_params[0].ty;
            quote! { #ty }
        }
        _ => {
            let types: Vec<_> = key_params.iter().map(|p| &p.ty).collect();
            quote! { ( #( #types ),* ) }
        }
    };

    // Generate cache_key() body
    let cache_key_body = match key_params.len() {
        0 => quote! { () },
        1 => {
            let name = &key_params[0].name;
            quote! { self.#name.clone() }
        }
        _ => {
            let names: Vec<_> = key_params.iter().map(|p| &p.name).collect();
            quote! { ( #( self.#names.clone() ),* ) }
        }
    };

    // Generate query() body - bind fields to local variables
    let field_bindings: Vec<_> = parsed
        .params
        .iter()
        .map(|p| {
            let name = &p.name;
            quote! { let #name = &self.#name; }
        })
        .collect();

    let fn_body = &parsed.body;

    // Generate optional trait methods
    let durability_impl = attr.durability.map(|d| {
        quote! {
            fn durability(&self) -> u8 {
                #d
            }
        }
    });

    let output_eq_impl = match &attr.output_eq {
        // Default: use PartialEq
        OutputEq::None | OutputEq::PartialEq => quote! {
            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        },
        // `output_eq = path`: use custom function
        OutputEq::Custom(custom_fn) => quote! {
            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                #custom_fn(old, new)
            }
        },
    };

    Ok(quote! {
        impl ::query_flow::Query for #struct_name {
            type CacheKey = #cache_key_ty;
            type Output = #output_ty;

            fn cache_key(&self) -> Self::CacheKey {
                #cache_key_body
            }

            fn query(&self, ctx: &mut ::query_flow::QueryContext) -> ::std::result::Result<Self::Output, ::query_flow::QueryError> {
                #( #field_bindings )*
                #fn_body
            }

            #durability_impl
            #output_eq_impl
        }
    })
}

// ============================================================================
// Asset Key Macro
// ============================================================================

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
        Err(darling::Error::custom("expected durability level: volatile, session, stable, or constant"))
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
struct AssetKeyAttr {
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

/// Define an asset key type.
///
/// # Attributes
///
/// - `asset = Type`: The asset type this key loads (required)
/// - `durability = volatile|session|stable|constant`: Durability level (default: volatile)
/// - `asset_eq`: Use PartialEq for asset comparison (default)
/// - `asset_eq = path`: Use custom function for asset comparison
///
/// # Example
///
/// ```ignore
/// use query_flow::asset_key;
/// use std::path::PathBuf;
///
/// // Default: volatile durability
/// #[asset_key(asset = String)]
/// pub struct ConfigFile(pub PathBuf);
///
/// // Explicit constant durability for bundled assets
/// #[asset_key(asset = String, durability = constant)]
/// pub struct BundledFile(pub PathBuf);
///
/// // Custom equality
/// #[asset_key(asset = ImageData, asset_eq = image_bytes_eq)]
/// pub struct TexturePath(pub String);
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

    let input_struct = parse_macro_input!(item as ItemStruct);

    match generate_asset_key(attr, input_struct) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn generate_asset_key(attr: AssetKeyAttr, input_struct: ItemStruct) -> Result<TokenStream2, Error> {
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
