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

/// Debug format option: `debug = "format string"`
#[derive(Debug, Default)]
pub enum DebugFormat {
    #[default]
    Derive,
    Custom(String),
}

impl FromMeta for DebugFormat {
    fn from_string(value: &str) -> darling::Result<Self> {
        Ok(DebugFormat::Custom(value.to_string()))
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

    /// Custom debug format string: `debug = "Fetch({id})"`.
    /// Uses std::fmt syntax: `{field}` for Display, `{field:?}` for Debug.
    #[darling(default)]
    debug: DebugFormat,
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

/// A segment of a parsed debug format string.
#[derive(Debug, PartialEq)]
enum FormatSegment {
    /// Literal text (e.g., "Fetch(" or ")")
    Literal(String),
    /// Field reference with optional format specifier
    /// `{field}` -> Display, `{field:?}` -> Debug, `{field:#?}` -> Pretty Debug
    Field { name: String, specifier: String },
}

/// Parse a format string into segments.
/// Handles `{field}`, `{field:?}`, `{field:#?}`, `{{`, and `}}`.
fn parse_format_string(format: &str) -> Result<Vec<FormatSegment>, String> {
    let mut segments = Vec::new();
    let mut chars = format.chars().peekable();
    let mut current_literal = String::new();

    while let Some(c) = chars.next() {
        match c {
            '{' => {
                // Check for escaped brace
                if chars.peek() == Some(&'{') {
                    chars.next();
                    current_literal.push('{');
                } else {
                    // Flush current literal
                    if !current_literal.is_empty() {
                        segments.push(FormatSegment::Literal(current_literal.clone()));
                        current_literal.clear();
                    }
                    // Parse field reference
                    let mut field_content = String::new();
                    let mut found_close = false;
                    for ch in chars.by_ref() {
                        if ch == '}' {
                            found_close = true;
                            break;
                        }
                        field_content.push(ch);
                    }
                    if !found_close {
                        return Err("unclosed `{` in format string".to_string());
                    }

                    // Parse field name and specifier
                    let (name, specifier) = if let Some(colon_pos) = field_content.find(':') {
                        (
                            field_content[..colon_pos].to_string(),
                            field_content[colon_pos + 1..].to_string(),
                        )
                    } else {
                        (field_content, String::new())
                    };

                    if name.is_empty() {
                        return Err("empty field name in format string".to_string());
                    }

                    segments.push(FormatSegment::Field { name, specifier });
                }
            }
            '}' => {
                // Check for escaped brace
                if chars.peek() == Some(&'}') {
                    chars.next();
                    current_literal.push('}');
                } else {
                    return Err("unmatched `}` in format string".to_string());
                }
            }
            _ => {
                current_literal.push(c);
            }
        }
    }

    // Flush remaining literal
    if !current_literal.is_empty() {
        segments.push(FormatSegment::Literal(current_literal));
    }

    Ok(segments)
}

/// Validate that all field references in segments exist in params.
fn validate_format_fields(segments: &[FormatSegment], params: &[Param]) -> Result<(), Error> {
    for segment in segments {
        if let FormatSegment::Field { name, .. } = segment {
            if !params.iter().any(|p| p.name == name.as_str()) {
                return Err(Error::new(
                    proc_macro2::Span::call_site(),
                    format!("unknown field `{}` in debug format string", name),
                ));
            }
        }
    }
    Ok(())
}

/// Generate a custom Debug impl from the format string.
fn generate_custom_debug(
    struct_name: &Ident,
    format: &str,
    params: &[Param],
) -> Result<TokenStream, Error> {
    let segments =
        parse_format_string(format).map_err(|e| Error::new(proc_macro2::Span::call_site(), e))?;

    validate_format_fields(&segments, params)?;

    // Build the write! format string and arguments
    let mut fmt_string = String::new();
    let mut fmt_args: Vec<TokenStream> = Vec::new();

    for segment in &segments {
        match segment {
            FormatSegment::Literal(text) => {
                // Escape any braces for the write! macro
                for c in text.chars() {
                    if c == '{' {
                        fmt_string.push_str("{{");
                    } else if c == '}' {
                        fmt_string.push_str("}}");
                    } else {
                        fmt_string.push(c);
                    }
                }
            }
            FormatSegment::Field { name, specifier } => {
                let field_ident = format_ident!("{}", name);
                if specifier.is_empty() {
                    // Display formatting
                    fmt_string.push_str("{}");
                    fmt_args.push(quote! { &self.#field_ident });
                } else if specifier == "?" {
                    // Debug formatting
                    fmt_string.push_str("{:?}");
                    fmt_args.push(quote! { &self.#field_ident });
                } else if specifier == "#?" {
                    // Pretty Debug formatting
                    fmt_string.push_str("{:#?}");
                    fmt_args.push(quote! { &self.#field_ident });
                } else {
                    // Pass through other specifiers
                    fmt_string.push('{');
                    fmt_string.push(':');
                    fmt_string.push_str(specifier);
                    fmt_string.push('}');
                    fmt_args.push(quote! { &self.#field_ident });
                }
            }
        }
    }

    Ok(quote! {
        impl ::std::fmt::Debug for #struct_name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                write!(f, #fmt_string #(, #fmt_args)*)
            }
        }
    })
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
    let struct_def = generate_struct(&parsed, &struct_name, &key_params, &attr.debug)?;

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

fn generate_struct(
    parsed: &ParsedFn,
    struct_name: &Ident,
    key_params: &[&Param],
    debug: &DebugFormat,
) -> Result<TokenStream, Error> {
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

    // Determine if we use derive(Debug) or custom Debug impl
    let use_derive_debug = matches!(debug, DebugFormat::Derive);

    let derives = match (all_fields_are_keys, use_derive_debug) {
        (true, true) => quote! { #[derive(Clone, Debug, Hash, PartialEq, Eq)] },
        (true, false) => quote! { #[derive(Clone, Hash, PartialEq, Eq)] },
        (false, true) => quote! { #[derive(Clone, Debug)] },
        (false, false) => quote! { #[derive(Clone)] },
    };

    let custom_debug_impl = match debug {
        DebugFormat::Derive => quote! {},
        DebugFormat::Custom(format) => generate_custom_debug(struct_name, format, &parsed.params)?,
    };

    Ok(quote! {
        #derives
        #vis struct #struct_name {
            #( #fields ),*
        }

        #new_impl
        #hash_eq_impl
        #custom_debug_impl
    })
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
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
            debug: DebugFormat::Derive,
        };
        let result = generate_query(attr, input_fn);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("`singleton` and `keys` are mutually exclusive"));
    }

    #[test]
    fn test_query_macro_custom_debug() {
        // Test custom debug format string
        let input_fn: ItemFn = syn::parse_quote! {
            fn fetch_user(db: &impl Db, id: u64, include_deleted: bool) -> Result<String, QueryError> {
                Ok(format!("user {}", id))
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(None),
            name: None,
            singleton: false,
            debug: DebugFormat::Custom("Fetch({id})".to_string()),
        };
        let output = generate_query(attr, input_fn).unwrap();

        // Should generate custom Debug impl instead of derive
        let expected = quote! {
            fn fetch_user(db: &impl Db, id: u64, include_deleted: bool) -> Result<String, QueryError> {
                Ok(format!("user {}", id))
            }

            #[derive(Clone, Hash, PartialEq, Eq)]
            struct FetchUser {
                pub id: u64,
                pub include_deleted: bool
            }

            impl FetchUser {
                #[doc = r" Create a new query instance."]
                fn new(id: u64, include_deleted: bool) -> Self {
                    Self { id, include_deleted }
                }
            }

            impl ::std::fmt::Debug for FetchUser {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                    write!(f, "Fetch({})", &self.id)
                }
            }

            impl ::query_flow::Query for FetchUser {
                type Output = String;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    fetch_user(db, self.id, self.include_deleted).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_query_macro_debug_unknown_field_error() {
        // Test that referencing an unknown field in debug format produces an error
        let input_fn: ItemFn = syn::parse_quote! {
            fn bad_debug(db: &impl Db, id: u64) -> Result<i32, QueryError> {
                Ok(42)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(None),
            name: None,
            singleton: false,
            debug: DebugFormat::Custom("Query({unknown_field})".to_string()),
        };
        let result = generate_query(attr, input_fn);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("unknown field `unknown_field` in debug format string"));
    }

    #[test]
    fn test_query_macro_debug_with_keys() {
        // Test debug format combined with keys() subset
        let input_fn: ItemFn = syn::parse_quote! {
            fn query_with_both(db: &impl Db, id: u64, opts: String) -> Result<i32, QueryError> {
                Ok(42)
            }
        };

        let attr = QueryAttr {
            output_eq: OutputEq::None,
            keys: Keys(Some(vec![format_ident!("id")])),
            name: None,
            singleton: false,
            debug: DebugFormat::Custom("Query({id:?})".to_string()),
        };
        let output = generate_query(attr, input_fn).unwrap();

        // Should generate custom Hash/Eq (for keys) AND custom Debug (for debug format)
        let expected = quote! {
            fn query_with_both(db: &impl Db, id: u64, opts: String) -> Result<i32, QueryError> {
                Ok(42)
            }

            #[derive(Clone)]
            struct QueryWithBoth {
                pub id: u64,
                pub opts: String
            }

            impl QueryWithBoth {
                #[doc = r" Create a new query instance."]
                fn new(id: u64, opts: String) -> Self {
                    Self { id, opts }
                }
            }

            impl ::std::hash::Hash for QueryWithBoth {
                fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                    self.id.hash(state);
                }
            }

            impl ::std::cmp::PartialEq for QueryWithBoth {
                fn eq(&self, other: &Self) -> bool {
                    self.id == other.id
                }
            }

            impl ::std::cmp::Eq for QueryWithBoth {}

            impl ::std::fmt::Debug for QueryWithBoth {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                    write!(f, "Query({:?})", &self.id)
                }
            }

            impl ::query_flow::Query for QueryWithBoth {
                type Output = i32;

                fn query(self, db: &impl ::query_flow::Db) -> ::std::result::Result<::std::sync::Arc<Self::Output>, ::query_flow::QueryError> {
                    query_with_both(db, self.id, self.opts).map(::std::sync::Arc::new)
                }

                fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                    old == new
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_parse_format_string() {
        // Test the format string parser directly
        let result = parse_format_string("Fetch({id})").unwrap();
        assert_eq!(
            result,
            vec![
                FormatSegment::Literal("Fetch(".to_string()),
                FormatSegment::Field {
                    name: "id".to_string(),
                    specifier: String::new()
                },
                FormatSegment::Literal(")".to_string()),
            ]
        );

        // Test with Debug specifier
        let result = parse_format_string("Query({name:?})").unwrap();
        assert_eq!(
            result,
            vec![
                FormatSegment::Literal("Query(".to_string()),
                FormatSegment::Field {
                    name: "name".to_string(),
                    specifier: "?".to_string()
                },
                FormatSegment::Literal(")".to_string()),
            ]
        );

        // Test with escaped braces
        let result = parse_format_string("{{literal}} {field}").unwrap();
        assert_eq!(
            result,
            vec![
                FormatSegment::Literal("{literal} ".to_string()),
                FormatSegment::Field {
                    name: "field".to_string(),
                    specifier: String::new()
                },
            ]
        );

        // Test error cases
        assert!(parse_format_string("unclosed {brace").is_err());
        assert!(parse_format_string("unmatched }").is_err());
        assert!(parse_format_string("empty {}").is_err());
    }
}
