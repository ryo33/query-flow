use darling::{ast::NestedMeta, FromMeta};
use heck::ToUpperCamelCase as _;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{
    spanned::Spanned as _, Error, FnArg, Ident, ItemFn, Pat, PatType, ReturnType, Type, Visibility,
};

/// Wrapper for parsing a list of identifiers: `keys(a, b, c)`
/// None = not specified (use default), Some(vec) = explicitly specified
#[derive(Debug, Default)]
struct Keys(Option<Vec<Ident>>);

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
        Ok(Keys(Some(idents)))
    }
}

/// Output equality option: `output_eq` or `output_eq = path`
#[derive(Debug, Default)]
pub enum OutputEq {
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
pub struct QueryAttr {
    /// Output equality for early cutoff optimization.
    /// Default: uses PartialEq (`old == new`).
    /// `output_eq = path`: uses custom function for types without PartialEq.
    #[darling(default)]
    output_eq: OutputEq,

    /// Params that form the cache key. Default: all params.
    #[darling(default)]
    keys: Keys,

    /// Override the generated struct name. Default: PascalCase of function name.
    #[darling(default)]
    name: Option<String>,

    /// Singleton query: no cache key, all instances share one cache entry.
    /// Mutually exclusive with `keys`.
    #[darling(default)]
    singleton: bool,
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
}

pub fn generate_query(attr: QueryAttr, input_fn: ItemFn) -> Result<TokenStream, Error> {
    // Parse the function
    let parsed = parse_function(&input_fn)?;

    // Determine struct name
    let struct_name = match &attr.name {
        Some(name) => format_ident!("{}", name),
        None => format_ident!("{}", parsed.name.to_string().to_upper_camel_case()),
    };

    // Validate singleton and keys are mutually exclusive
    if attr.singleton && attr.keys.0.is_some() {
        return Err(Error::new(
            input_fn.sig.span(),
            "`singleton` and `keys` are mutually exclusive",
        ));
    }

    // Determine which params are keys
    let key_params: Vec<&Param> = if attr.singleton {
        // Singleton: no keys, all instances share one cache entry
        vec![]
    } else {
        match &attr.keys.0 {
            None => {
                // Default: all params are keys
                parsed.params.iter().collect()
            }
            Some(keys) if keys.is_empty() => {
                // Empty keys() is an error - use singleton instead
                return Err(Error::new(
                    input_fn.sig.span(),
                    "empty `keys()` is not allowed; use `singleton` for queries with no cache key",
                ));
            }
            Some(keys) => {
                // Validate that specified keys exist
                for key in keys {
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
                    .filter(|p| keys.contains(&p.name))
                    .collect()
            }
        }
    };

    // Generate struct definition (with Hash/Eq based on key_params)
    let struct_def = generate_struct(&parsed, &struct_name, &key_params);

    // Generate Query impl
    let query_impl = generate_query_impl(&parsed, &struct_name, &attr)?;

    Ok(quote! {
        #input_fn
        #struct_def
        #query_impl
    })
}

fn parse_function(input_fn: &ItemFn) -> Result<ParsedFn, Error> {
    let vis = input_fn.vis.clone();
    let name = input_fn.sig.ident.clone();

    // Check that first param is db: &impl Db
    let mut iter = input_fn.sig.inputs.iter();
    let first_param = iter.next().ok_or_else(|| {
        Error::new(
            input_fn.sig.span(),
            "query function must have `db: &impl Db` as first parameter",
        )
    })?;

    validate_db_param(first_param)?;

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

    Ok(ParsedFn {
        vis,
        name,
        params,
        output_ty,
    })
}

fn validate_db_param(arg: &FnArg) -> Result<(), Error> {
    match arg {
        FnArg::Typed(_) => {
            // We accept any name for the db parameter (e.g., db, _db, ctx, etc.)
            // Type checking is complex, we'll trust the user
            Ok(())
        }
        FnArg::Receiver(_) => Err(Error::new(
            arg.span(),
            "first parameter must be `db: &impl Db`, not `self`",
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

/// Extract inner type T from Arc<T>, returns None if not an Arc type.
fn extract_arc_inner(ty: &Type) -> Option<Type> {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            if segment.ident == "Arc" {
                if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                    if let Some(syn::GenericArgument::Type(inner_ty)) = args.args.first() {
                        return Some(inner_ty.clone());
                    }
                }
            }
        }
    }
    None
}

fn generate_struct(parsed: &ParsedFn, struct_name: &Ident, key_params: &[&Param]) -> TokenStream {
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

    // Check if we need custom Hash/Eq implementations (when keys() specifies a subset of fields)
    let all_fields_are_keys = key_params.len() == parsed.params.len()
        && key_params
            .iter()
            .all(|kp| parsed.params.iter().any(|p| p.name == kp.name));

    let hash_eq_impl = if all_fields_are_keys {
        // All fields are keys, use derive
        quote! {}
    } else {
        // Custom keys specified, generate custom Hash/Eq
        let key_names: Vec<_> = key_params.iter().map(|p| &p.name).collect();

        let hash_body = if key_params.is_empty() {
            // No key fields means all instances are equal
            quote! {}
        } else {
            quote! {
                #( self.#key_names.hash(state); )*
            }
        };

        let eq_body = if key_params.is_empty() {
            quote! { true }
        } else {
            let comparisons: Vec<_> = key_params
                .iter()
                .map(|p| {
                    let name = &p.name;
                    quote! { self.#name == other.#name }
                })
                .collect();
            quote! { #( #comparisons )&&* }
        };

        quote! {
            impl ::std::hash::Hash for #struct_name {
                fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                    #hash_body
                }
            }

            impl ::std::cmp::PartialEq for #struct_name {
                fn eq(&self, other: &Self) -> bool {
                    #eq_body
                }
            }

            impl ::std::cmp::Eq for #struct_name {}
        }
    };

    let derives = if all_fields_are_keys {
        quote! { #[derive(Clone, Debug, Hash, PartialEq, Eq)] }
    } else {
        quote! { #[derive(Clone, Debug)] }
    };

    quote! {
        #derives
        #vis struct #struct_name {
            #( #fields ),*
        }

        #new_impl
        #hash_eq_impl
    }
}

fn generate_query_impl(
    parsed: &ParsedFn,
    struct_name: &Ident,
    attr: &QueryAttr,
) -> Result<TokenStream, Error> {
    let output_ty = &parsed.output_ty;

    // Check if the function returns Arc<T> - if so, Output = T and we pass through
    // Otherwise, Output = T and we wrap with Arc::new
    let (actual_output_ty, query_body) = if let Some(inner_ty) = extract_arc_inner(output_ty) {
        // Function returns Arc<T>, so Output = T, pass through directly
        let fn_name = &parsed.name;
        let field_names: Vec<_> = parsed.params.iter().map(|p| &p.name).collect();
        (
            quote! { #inner_ty },
            quote! { #fn_name(db #(,self.#field_names )*) },
        )
    } else {
        // Function returns T, so Output = T, wrap with Arc::new
        let fn_name = &parsed.name;
        let field_names: Vec<_> = parsed.params.iter().map(|p| &p.name).collect();
        (
            quote! { #output_ty },
            quote! { #fn_name(db #(,self.#field_names )*).map(::std::sync::Arc::new) },
        )
    };

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
            type Output = #actual_output_ty;

            fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                #query_body
            }

            #output_eq_impl
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    use syn::ItemFn;

    fn normalize_tokens(tokens: TokenStream) -> String {
        tokens
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn test_query_macro_preserves_attributes() {
        let input_fn: ItemFn = syn::parse_quote! {
            #[allow(unused_variables)]
            #[inline]
            fn my_query(db: &impl Db, x: i32) -> Result<i32, QueryError> {
                let unused = 42;
                Ok(x * 2)
            }
        };

        let attr = QueryAttr::default();
        let output = generate_query(attr, input_fn).unwrap();

        let expected = quote! {
            #[allow(unused_variables)]
            #[inline]
            fn my_query(db: &impl Db, x: i32) -> Result<i32, QueryError> {
                let unused = 42;
                Ok(x * 2)
            }

            #[derive(Clone, Debug, Hash, PartialEq, Eq)]
            struct MyQuery {
                pub x: i32
            }

            impl MyQuery {
                #[doc = r" Create a new query instance."]
                fn new(x: i32) -> Self {
                    Self { x }
                }
            }

            impl ::query_flow::Query for MyQuery {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    my_query(db, self.x).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_without_attributes() {
        let input_fn: ItemFn = syn::parse_quote! {
            fn simple(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
                Ok(a + b)
            }
        };

        let attr = QueryAttr::default();
        let output = generate_query(attr, input_fn).unwrap();

        let expected = quote! {
            fn simple(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
                Ok(a + b)
            }

            #[derive(Clone, Debug, Hash, PartialEq, Eq)]
            struct Simple {
                pub a: i32,
                pub b: i32
            }

            impl Simple {
                #[doc = r" Create a new query instance."]
                fn new(a: i32, b: i32) -> Self {
                    Self { a, b }
                }
            }

            impl ::query_flow::Query for Simple {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    simple(db, self.a, self.b).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_no_params() {
        let input_fn: ItemFn = syn::parse_quote! {
            fn no_params(db: &impl Db) -> Result<i32, QueryError> {
                Ok(42)
            }
        };

        let attr = QueryAttr::default();
        let output = generate_query(attr, input_fn).unwrap();

        let expected = quote! {
            fn no_params(db: &impl Db) -> Result<i32, QueryError> {
                Ok(42)
            }

            #[derive(Clone, Debug, Hash, PartialEq, Eq)]
            struct NoParams {
            }

            impl NoParams {
                #[doc = r" Create a new query instance."]
                fn new() -> Self {
                    Self {}
                }
            }

            impl ::std::default::Default for NoParams {
                fn default() -> Self {
                    Self::new()
                }
            }

            impl ::query_flow::Query for NoParams {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    no_params(db).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_arc_output() {
        let input_fn: ItemFn = syn::parse_quote! {
            fn returns_arc(db: &impl Db, x: i32) -> Result<Arc<String>, QueryError> {
                Ok(Arc::new(x.to_string()))
            }
        };

        let attr = QueryAttr::default();
        let output = generate_query(attr, input_fn).unwrap();

        let expected = quote! {
            fn returns_arc(db: &impl Db, x: i32) -> Result<Arc<String>, QueryError> {
                Ok(Arc::new(x.to_string()))
            }

            #[derive(Clone, Debug, Hash, PartialEq, Eq)]
            struct ReturnsArc {
                pub x: i32
            }

            impl ReturnsArc {
                #[doc = r" Create a new query instance."]
                fn new(x: i32) -> Self {
                    Self { x }
                }
            }

            impl ::query_flow::Query for ReturnsArc {
                type Output = String;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    returns_arc(db, self.x)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_keys_subset() {
        // Test keys(a) with multiple params - only 'a' should be used for Hash/Eq
        let input_fn: ItemFn = syn::parse_quote! {
            fn with_keys(db: &impl Db, a: i32, b: String, c: bool) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("a")])),
            name: None,
            singleton: false,
        };
        let output = generate_query(attr, input_fn).unwrap();

        // Should generate custom Hash/Eq that only uses 'a'
        let expected = quote! {
            fn with_keys(db: &impl Db, a: i32, b: String, c: bool) -> Result<i32, QueryError> {
                Ok(a)
            }

            #[derive(Clone, Debug)]
            struct WithKeys {
                pub a: i32,
                pub b: String,
                pub c: bool
            }

            impl WithKeys {
                #[doc = r" Create a new query instance."]
                fn new(a: i32, b: String, c: bool) -> Self {
                    Self { a, b, c }
                }
            }

            impl ::std::hash::Hash for WithKeys {
                fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                    self.a.hash(state);
                }
            }

            impl ::std::cmp::PartialEq for WithKeys {
                fn eq(&self, other: &Self) -> bool {
                    self.a == other.a
                }
            }

            impl ::std::cmp::Eq for WithKeys {}

            impl ::query_flow::Query for WithKeys {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    with_keys(db, self.a, self.b, self.c).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_keys_multiple() {
        // Test keys(a, c) with three params - only 'a' and 'c' should be used for Hash/Eq
        let input_fn: ItemFn = syn::parse_quote! {
            fn multi_keys(db: &impl Db, a: i32, b: String, c: bool) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("a"), format_ident!("c")])),
            name: None,
            singleton: false,
        };
        let output = generate_query(attr, input_fn).unwrap();

        // Should generate custom Hash/Eq that uses both 'a' and 'c'
        let expected = quote! {
            fn multi_keys(db: &impl Db, a: i32, b: String, c: bool) -> Result<i32, QueryError> {
                Ok(a)
            }

            #[derive(Clone, Debug)]
            struct MultiKeys {
                pub a: i32,
                pub b: String,
                pub c: bool
            }

            impl MultiKeys {
                #[doc = r" Create a new query instance."]
                fn new(a: i32, b: String, c: bool) -> Self {
                    Self { a, b, c }
                }
            }

            impl ::std::hash::Hash for MultiKeys {
                fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                    self.a.hash(state);
                    self.c.hash(state);
                }
            }

            impl ::std::cmp::PartialEq for MultiKeys {
                fn eq(&self, other: &Self) -> bool {
                    self.a == other.a && self.c == other.c
                }
            }

            impl ::std::cmp::Eq for MultiKeys {}

            impl ::query_flow::Query for MultiKeys {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    multi_keys(db, self.a, self.b, self.c).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_keys_all_explicit() {
        // Test keys(a, b) when all params are specified - should use derive, not custom impl
        let input_fn: ItemFn = syn::parse_quote! {
            fn all_keys(db: &impl Db, a: i32, b: String) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("a"), format_ident!("b")])),
            name: None,
            singleton: false,
        };
        let output = generate_query(attr, input_fn).unwrap();

        // When all params are keys, should use derive instead of custom impl
        let expected = quote! {
            fn all_keys(db: &impl Db, a: i32, b: String) -> Result<i32, QueryError> {
                Ok(a)
            }

            #[derive(Clone, Debug, Hash, PartialEq, Eq)]
            struct AllKeys {
                pub a: i32,
                pub b: String
            }

            impl AllKeys {
                #[doc = r" Create a new query instance."]
                fn new(a: i32, b: String) -> Self {
                    Self { a, b }
                }
            }

            impl ::query_flow::Query for AllKeys {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    all_keys(db, self.a, self.b).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_keys_unknown_error() {
        // Test that specifying an unknown key produces an error
        let input_fn: ItemFn = syn::parse_quote! {
            fn bad_keys(db: &impl Db, a: i32) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("unknown")])),
            name: None,
            singleton: false,
        };
        let result = generate_query(attr, input_fn);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("unknown parameter `unknown` in keys"));
    }

    #[test]
    fn test_query_macro_keys_empty_error() {
        // Test empty keys() produces an error
        let input_fn: ItemFn = syn::parse_quote! {
            fn empty_keys(db: &impl Db, a: i32, b: String) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![])),
            name: None,
            singleton: false,
        };
        let result = generate_query(attr, input_fn);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("empty `keys()` is not allowed"));
    }

    #[test]
    fn test_query_macro_singleton() {
        // Test singleton attribute - no cache key, all instances share one entry
        let input_fn: ItemFn = syn::parse_quote! {
            fn singleton_query(db: &impl Db, format: String) -> Result<String, QueryError> {
                Ok(format!("result: {}", format))
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(None),
            name: None,
            singleton: true,
        };
        let output = generate_query(attr, input_fn).unwrap();

        // Should generate custom Hash/Eq with no keys (all instances equal)
        let expected = quote! {
            fn singleton_query(db: &impl Db, format: String) -> Result<String, QueryError> {
                Ok(format!("result: {}", format))
            }

            #[derive(Clone, Debug)]
            struct SingletonQuery {
                pub format: String
            }

            impl SingletonQuery {
                #[doc = r" Create a new query instance."]
                fn new(format: String) -> Self {
                    Self { format }
                }
            }

            impl ::std::hash::Hash for SingletonQuery {
                fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                }
            }

            impl ::std::cmp::PartialEq for SingletonQuery {
                fn eq(&self, other: &Self) -> bool {
                    true
                }
            }

            impl ::std::cmp::Eq for SingletonQuery {}

            impl ::query_flow::Query for SingletonQuery {
                type Output = String;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    singleton_query(db, self.format).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_singleton_keys_mutually_exclusive() {
        // Test that singleton and keys cannot be used together
        let input_fn: ItemFn = syn::parse_quote! {
            fn bad_query(db: &impl Db, a: i32) -> Result<i32, QueryError> {
                Ok(a)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("a")])),
            name: None,
            singleton: true,
        };
        let result = generate_query(attr, input_fn);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("`singleton` and `keys` are mutually exclusive"));
    }
}
