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
        let mut cons = op.get_container(self_.inputs(), exec_id).await;
        op.add_container(self_.outputs()[0].clone(), exec_id, cons.pop_front().unwrap()).await.unwrap();
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
            let mut cons = op.get_container(self_.inputs(), exec_id).await;
            op.add_container(self_.outputs()[0].clone(), exec_id, cons.pop_front().unwrap()).await.unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
