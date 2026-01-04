use heck::ToUpperCamelCase as _;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{spanned::Spanned as _, Error, FnArg, ItemFn, ReturnType, Type};

/// Parsed function information for asset locator.
struct ParsedLocatorFn {
    name: syn::Ident,
    key_ty: Type,
    asset_ty: Type,
}

pub fn generate_asset_locator(input_fn: ItemFn) -> Result<TokenStream, Error> {
    // Parse the function
    let parsed = parse_locator_function(&input_fn)?;

    // Generate struct name from function name (PascalCase)
    let struct_name = format_ident!("{}", parsed.name.to_string().to_upper_camel_case());

    let key_ty = &parsed.key_ty;
    let asset_ty = &parsed.asset_ty;
    let fn_name = &parsed.name;

    Ok(quote! {
        #input_fn

        struct #struct_name;

        impl ::query_flow::AssetLocator<#key_ty> for #struct_name {
            fn locate(
                &self,
                db: &impl ::query_flow::Db,
                key: &#key_ty,
            ) -> ::std::result::Result<::query_flow::LocateResult<#asset_ty>, ::query_flow::QueryError> {
                #fn_name(db, key)
            }
        }
    })
}

fn parse_locator_function(input_fn: &ItemFn) -> Result<ParsedLocatorFn, Error> {
    let name = input_fn.sig.ident.clone();

    // Parse parameters
    let mut params = input_fn.sig.inputs.iter();

    // First param: db: &impl Db (name is ignored)
    let first_param = params.next().ok_or_else(|| {
        Error::new(
            input_fn.sig.span(),
            "asset locator function must have `db: &impl Db` as first parameter",
        )
    })?;
    validate_db_param(first_param)?;

    // Second param: key: &KeyType
    let second_param = params.next().ok_or_else(|| {
        Error::new(
            input_fn.sig.span(),
            "asset locator function must have `key: &KeyType` as second parameter",
        )
    })?;
    let key_ty = parse_key_param(second_param)?;

    // No more params expected
    if params.next().is_some() {
        return Err(Error::new(
            input_fn.sig.span(),
            "asset locator function should have exactly 2 parameters: (db, key)",
        ));
    }

    // Parse return type: Result<LocateResult<AssetType>, QueryError>
    let asset_ty = parse_locator_return_type(&input_fn.sig.output)?;

    Ok(ParsedLocatorFn {
        name,
        key_ty,
        asset_ty,
    })
}

fn validate_db_param(arg: &FnArg) -> Result<(), Error> {
    match arg {
        FnArg::Typed(_) => {
            // We accept any name for the db parameter
            // Type checking is complex, we trust the user
            Ok(())
        }
        FnArg::Receiver(_) => Err(Error::new(
            arg.span(),
            "first parameter must be `db: &impl Db`, not `self`",
        )),
    }
}

fn parse_key_param(arg: &FnArg) -> Result<Type, Error> {
    match arg {
        FnArg::Typed(pat_type) => {
            // Extract from parameter type (should be &KeyType)
            let ty = &*pat_type.ty;
            if let Type::Reference(ref_ty) = ty {
                Ok((*ref_ty.elem).clone())
            } else {
                Err(Error::new(
                    ty.span(),
                    "key parameter should be a reference type `&KeyType`",
                ))
            }
        }
        FnArg::Receiver(_) => Err(Error::new(
            arg.span(),
            "second parameter must be `key: &KeyType`",
        )),
    }
}

fn parse_locator_return_type(ret: &ReturnType) -> Result<Type, Error> {
    match ret {
        ReturnType::Default => Err(Error::new(
            ret.span(),
            "asset locator must return `Result<LocateResult<AssetType>, QueryError>`",
        )),
        ReturnType::Type(_, ty) => extract_locate_result_asset_type(ty),
    }
}

/// Extract AssetType from Result<LocateResult<AssetType>, QueryError>
fn extract_locate_result_asset_type(ty: &Type) -> Result<Type, Error> {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            if segment.ident == "Result" {
                if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                    if let Some(syn::GenericArgument::Type(ok_ty)) = args.args.first() {
                        // ok_ty should be LocateResult<AssetType>
                        return extract_locate_result_inner(ok_ty);
                    }
                }
            }
        }
    }
    Err(Error::new(
        ty.span(),
        "expected `Result<LocateResult<AssetType>, QueryError>` return type",
    ))
}

/// Extract AssetType from LocateResult<AssetType>
fn extract_locate_result_inner(ty: &Type) -> Result<Type, Error> {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            if segment.ident == "LocateResult" {
                if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                    if let Some(syn::GenericArgument::Type(asset_ty)) = args.args.first() {
                        return Ok(asset_ty.clone());
                    }
                }
            }
        }
    }
    Err(Error::new(
        ty.span(),
        "expected `LocateResult<AssetType>` in return type",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::ItemFn;

    fn normalize_tokens(tokens: TokenStream) -> String {
        tokens
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn test_asset_locator_macro_basic() {
        let input_fn: ItemFn = syn::parse_quote! {
            fn pending_locator(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
                Ok(LocateResult::Pending)
            }
        };

        let output = generate_asset_locator(input_fn).unwrap();

        let expected = quote! {
            fn pending_locator(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
                Ok(LocateResult::Pending)
            }

            struct PendingLocator;

            impl ::query_flow::AssetLocator<ConfigFile> for PendingLocator {
                fn locate(
                    &self,
                    db: &impl ::query_flow::Db,
                    key: &ConfigFile,
                ) -> ::std::result::Result<::query_flow::LocateResult<String>, ::query_flow::QueryError> {
                    pending_locator(db, key)
                }
            }
        };

        assert_eq!(normalize_tokens(output), normalize_tokens(expected));
    }

    #[test]
    fn test_asset_locator_with_generic_asset() {
        let input_fn: ItemFn = syn::parse_quote! {
            fn my_locator(db: &impl Db, key: &MyKey) -> Result<LocateResult<Vec<u8>>, QueryError> {
                Ok(LocateResult::Pending)
            }
        };

        let output = generate_asset_locator(input_fn).unwrap();

        // Should generate struct MyLocator and impl AssetLocator<MyKey>
        let output_str = normalize_tokens(output);
        assert!(output_str.contains("struct MyLocator"));
        assert!(output_str.contains("AssetLocator < MyKey >"));
    }
}
