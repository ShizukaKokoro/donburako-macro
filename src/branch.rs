use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn branch_impl(tokens: TokenStream) -> TokenStream {
    branch_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn branch_parse(_: ParseStream) -> Result<TokenStream> {
    Ok(quote! {
        take! {
            exec_id | self_.inputs()
                => state: bool
        }
        store!{
            exec_id | &vec![if state { self_.outputs()[0].clone() } else { self_.outputs()[1].clone() }]
                => ()
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_if_parse() {
        let input = quote! {};
        let result = branch_impl(input).to_string();
        let expected = quote! {
            take! {
                exec_id | self_.inputs()
                    => state: bool
            }
            store!{
                exec_id | &vec![if state { self_.outputs()[0].clone() } else { self_.outputs()[1].clone() }]
                    => ()
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
