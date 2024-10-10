use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn input_impl(tokens: TokenStream) -> TokenStream {
    input_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn input_parse(input: ParseStream) -> Result<TokenStream> {
    todo!()
}

pub fn output_impl(tokens: TokenStream) -> TokenStream {
    output_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn output_parse(input: ParseStream) -> Result<TokenStream> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_input_parse() {
        let input = quote! {
            n: i32
        };
        let result = input_parse.parse2(input).unwrap();
        let expected = quote! {
            take! {
                exec_id | self_.inputs()
                    => n: i32
            }
        };
        assert_eq!(result.to_string(), expected.to_string());
    }

    #[test]
    fn test_input_parse_multi() {
        let input = quote! {
            arg_0to1_int: fizz::i32, arg_0to1_str: &str
        };
        let result = input_impl(input).to_string();
        let expected = quote! {
            take! {
                exec_id | self_.inputs()
                    => _: ()
                    => arg_0to1_int: fizz::i32
                    => arg_0to1_str: &str
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_output_parse() {
        let input = quote! {
            n
        };
        let result = output_parse.parse2(input).unwrap();
        let expected = quote! {
            store!{
                exec_id | self_.outputs()
                    => n
            }
        };
        assert_eq!(result.to_string(), expected.to_string());
    }

    #[test]
    fn test_output_parse_multi() {
        let input = quote! {
            42, "hello"
        };
        let result = output_impl(input).to_string();
        let expected = quote! {
            store!{
                exec_id | self_.outputs()
                    => 42
                    => "hello"
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
