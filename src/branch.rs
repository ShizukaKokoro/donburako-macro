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
        input! {
            let state: bool;
        }
        let mut con_clone = con.clone_container().unwrap();
        con_clone.store(());
        let mut output_cons = std::collections::VecDeque::new();
        output_cons.push_back(con_clone);
        if state {
            op.add_container(&vec![self_.outputs()[0].clone()], exec_id, output_cons)
                .await
                .unwrap();
        } else {
            op.add_container(&vec![self_.outputs()[1].clone()], exec_id, output_cons)
                .await
                .unwrap();
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
            input! {
                let state: bool;
            }
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store(());
            let mut output_cons = std::collections::VecDeque::new();
            output_cons.push_back(con_clone);
            if state {
                op.add_container(&vec![self_.outputs()[0].clone()], exec_id, output_cons)
                    .await
                    .unwrap();
            } else {
                op.add_container(&vec![self_.outputs()[1].clone()], exec_id, output_cons)
                    .await
                    .unwrap();
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
