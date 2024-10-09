use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Expr, Result};

pub fn output_impl(tokens: TokenStream) -> TokenStream {
    output_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn output_parse(input: ParseStream) -> Result<TokenStream> {
    let mut stmts = Vec::new();
    while !input.is_empty() {
        let stmt: Expr = input.parse()?;
        stmts.push(quote! {
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store(#stmt);
            output_cons.push_back(con_clone);
        });
        let _ = input.parse::<syn::Token![,]>();
    }
    Ok(quote! {
        let mut output_cons = std::collections::VecDeque::new();
        #(#stmts)*
        op.add_container(self_.outputs(), exec_id, output_cons)
            .await
            .unwrap();
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_output_parse() {
        let input = quote! {
            "1 -> 3"
        };
        let result = output_impl(input).to_string();
        let expected = quote! {
            let mut output_cons = std::collections::VecDeque::new();
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("1 -> 3");
            output_cons.push_back(con_clone);
            op.add_container(self_.outputs(), exec_id, output_cons)
                .await
                .unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_output_parse_multi() {
        let input = quote! {
            42, "0 -> 1", "0 -> 2", "0 -> 3"
        };
        let result = output_impl(input).to_string();
        let expected = quote! {
            let mut output_cons = std::collections::VecDeque::new();
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store(42);
            output_cons.push_back(con_clone);
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("0 -> 1");
            output_cons.push_back(con_clone);
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("0 -> 2");
            output_cons.push_back(con_clone);
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("0 -> 3");
            output_cons.push_back(con_clone);
            op.add_container(self_.outputs(), exec_id, output_cons)
                .await
                .unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
