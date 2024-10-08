use proc_macro2::TokenStream;
use quote::quote;

pub fn node_func_impl(tokens: TokenStream) -> TokenStream {
    quote! {
        Box::new(|self_, op, exec_id| {
            Box::pin(async move {
                #tokens
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_node_func_parse() {
        let input = quote! {
            input! {
                let n: i32;
            }
            println!("n: {:?}(is_zero)", n);
            let result = n == 0;
            output!(result);
        };
        let expected = quote! {
            Box::new(|self_, op, exec_id| {
                Box::pin(async move {
                    input! {
                        let n: i32;
                    }
                    println!("n: {:?}(is_zero)", n);
                    let result = n == 0;
                    output!(result);
                })
            })
        };
        let result = node_func_impl(input);
        assert_eq!(result.to_string(), expected.to_string());
    }
}
