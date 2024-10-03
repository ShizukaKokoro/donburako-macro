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
        let num = stmts.len();
        stmts.push(quote! {
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store(#stmt);
            op.add_container(self_.outputs()[#num].clone(), exec_id, con_clone)
                .await
                .unwrap();
        });
        let _ = input.parse::<syn::Token![,]>();
    }
    Ok(quote! { #(#stmts)* })
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
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("1 -> 3");
            op.add_container(self_.outputs()[0usize].clone(), exec_id, con_clone)
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
            let mut con_clone = con.clone_container().unwrap();
                con_clone.store(42);
                op.add_container(self_.outputs()[0usize].clone(), exec_id, con_clone)
                    .await
                    .unwrap();
                let mut con_clone = con.clone_container().unwrap();
                con_clone.store("0 -> 1");
                op.add_container(self_.outputs()[1usize].clone(), exec_id, con_clone)
                    .await
                    .unwrap();
                let mut con_clone = con.clone_container().unwrap();
                con_clone.store("0 -> 2");
                op.add_container(self_.outputs()[2usize].clone(), exec_id, con_clone)
                    .await
                    .unwrap();
                let mut con_clone = con.clone_container().unwrap();
                con_clone.store("0 -> 3");
                op.add_container(self_.outputs()[3usize].clone(), exec_id, con_clone)
                    .await
                    .unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
