use darling::{ast::NestedMeta, FromMeta};
use heck::ToUpperCamelCase as _;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{
    spanned::Spanned as _, Error, FnArg, Ident, ItemFn, Pat, PatType, ReturnType, Type, Visibility,
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
}

pub fn generate_query(attr: QueryAttr, input_fn: ItemFn) -> Result<TokenStream, Error> {
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
        FnArg::Typed(pat_type) => {
            // Check parameter name is 'db'
            if let Pat::Ident(pat_ident) = &*pat_type.pat {
                if pat_ident.ident != "db" {
                    return Err(Error::new(
                        pat_ident.ident.span(),
                        "first parameter must be named `db`",
                    ));
                }
            }
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

fn generate_struct(parsed: &ParsedFn, struct_name: &Ident) -> TokenStream {
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
) -> Result<TokenStream, Error> {
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
    // Note: For 0 params, we use an empty block which evaluates to ()
    // to avoid clippy::unused_unit warning
    let cache_key_body = match key_params.len() {
        0 => quote! {},
        1 => {
            let name = &key_params[0].name;
            quote! { self.#name.clone() }
        }
        _ => {
            let names: Vec<_> = key_params.iter().map(|p| &p.name).collect();
            quote! { ( #( self.#names.clone() ),* ) }
        }
    };

    // Generate query() body - call the original function
    let fn_name = &parsed.name;
    let field_names: Vec<_> = parsed.params.iter().map(|p| &p.name).collect();

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

            fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<Self::Output, ::query_flow::QueryError> {
                #fn_name(db #(,self.#field_names )*)
            }

            #durability_impl
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

            #[derive(Clone, Debug)]
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
                type CacheKey = i32;
                type Output = i32;

                fn cache_key(&self) -> Self::CacheKey {
                    self.x.clone()
                }

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<Self::Output, ::query_flow::QueryError> {
                    my_query(db, self.x)
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

            #[derive(Clone, Debug)]
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
                type CacheKey = (i32, i32);
                type Output = i32;

                fn cache_key(&self) -> Self::CacheKey {
                    (self.a.clone(), self.b.clone())
                }

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<Self::Output, ::query_flow::QueryError> {
                    simple(db, self.a, self.b)
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

            #[derive(Clone, Debug)]
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
                type CacheKey = ();
                type Output = i32;

                fn cache_key(&self) -> Self::CacheKey {
                    // Empty body - evaluates to () without explicit unit expression
                }

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<Self::Output, ::query_flow::QueryError> {
                    no_params(db)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }
}
