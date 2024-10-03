use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Local, Pat, PatType, Result, Stmt};

pub fn input_impl(tokens: TokenStream) -> TokenStream {
    input_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn input_parse(input: ParseStream) -> Result<TokenStream> {
    let mut stmts = Vec::new();
    while !input.is_empty() {
        let stmt: Stmt = input.parse()?;
        match stmt {
            Stmt::Local(Local { pat, .. }) => match pat {
                Pat::Type(PatType { pat, ty, .. }) => {
                    let pat = pat.clone();
                    let ty = ty.clone();
                    let num = stmts.len();
                    stmts.push(quote! {
                        let mut con = cmap.get_container(self_.inputs()[#num].clone(), exec_id).await.unwrap();
                        let #pat: #ty = con.take().unwrap();
                    });
                }
                _ => return Err(Error::new_spanned(pat, "expected pattern type")),
            },
            _ => return Err(Error::new_spanned(stmt, "expected local statement")),
        }
    }
    Ok(quote! { #(#stmts)* })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_input_parse() {
        let input = quote! {
            let arg_to0: &str;
        };
        let result = input_impl(input).to_string();
        let expected = quote! {
            let mut con = cmap.get_container(&self_.inputs()[0usize]).await.unwrap();
            let arg_to0: &str = con.take().unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_input_parse_multi() {
        let input = quote! {
            let arg_0to1_int: i32;
            let arg_0to1_str: &str;
        };
        let result = input_impl(input).to_string();
        let expected = quote! {
            let mut con = cmap.get_container(&self_.inputs()[0usize]).await.unwrap();
            let arg_0to1_int: i32 = con.take().unwrap();
            let mut con = cmap.get_container(&self_.inputs()[1usize]).await.unwrap();
            let arg_0to1_str: &str = con.take().unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
