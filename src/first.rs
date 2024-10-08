use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn first_impl(tokens: TokenStream) -> TokenStream {
    first_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn first_parse(_: ParseStream) -> Result<TokenStream> {
    Ok(quote! {
        for edge in self_.inputs() {
            if let Some(mut con) = op.get_container(edge.clone(), exec_id).await {
                op.add_container(self_.outputs()[0].clone(), exec_id, con).await.unwrap();
                return;
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_first_parse() {
        let input = quote! {};
        let result = first_impl(input).to_string();
        let expected = quote! {
            for edge in self_.inputs() {
                if let Some(mut con) = op.get_container(edge.clone(), exec_id).await {
                    op.add_container(self_.outputs()[0].clone(), exec_id, con).await.unwrap();
                    return;
                }
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
