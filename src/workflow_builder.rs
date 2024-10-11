use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn workflow_builder_impl(_: TokenStream, tokens: TokenStream) -> TokenStream {
    workflow_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn workflow_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let func = input.parse::<syn::ItemFn>()?;
    Ok(quote! {
        #func
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_workflow_builder_impl() {
        let input = quote! {
            fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide(n);
                let even: bool = is_even(n0);
                let selected: Option<i32> = if even {
                    let res: Option<i32> = double(n1);
                    res
                } else {
                    let res: Option<i32> = none();
                    res
                };
                return selected;
            }
        };
        let result = workflow_builder_impl(quote! {}, input).to_string();
        let expected = quote! {}.to_string();
        assert_eq!(result, expected);
    }
}
