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
    let mut stmts = vec![];
    while !input.is_empty() {
        let stmt = if input.peek(syn::Token![_]) {
            let _ = input.parse::<syn::Token![_]>()?;
            syn::Ident::new("_", proc_macro2::Span::call_site())
        } else {
            input.parse::<syn::Ident>()?
        };
        let _ = input.parse::<syn::Token![:]>()?;
        let ty = input.parse::<syn::Type>()?;
        stmts.push(quote! { => #stmt: #ty });
        if input.is_empty() {
            break;
        }
        let _ = input.parse::<syn::Token![,]>()?;
    }

    Ok(quote! {
        take! {
            exec_id | self_.inputs()
                #(#stmts)*
        }
    })
}

pub fn output_impl(tokens: TokenStream) -> TokenStream {
    output_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn output_parse(input: ParseStream) -> Result<TokenStream> {
    let mut stmts = vec![];
    while !input.is_empty() {
        let stmt = input.parse::<syn::Expr>()?;
        stmts.push(quote! { => #stmt });
        if input.is_empty() {
            break;
        }
        let _ = input.parse::<syn::Token![,]>()?;
    }

    Ok(quote! {
        store! {
            exec_id | self_.outputs()
                #(#stmts)*
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

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
            _:(), arg_0to1_int: fizz::i32, arg_0to1_str: &str
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
