use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn take_impl(tokens: TokenStream) -> TokenStream {
    take_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn take_parse(input: ParseStream) -> Result<TokenStream> {
    let mut stmts = Vec::new();
    let id = input.parse::<syn::Ident>()?;
    let _ = input.parse::<syn::Token![|]>()?;
    let from_manage_cnt = input.parse::<syn::Expr>()?;
    let (from, manage_cnt) = match from_manage_cnt {
        syn::Expr::Binary(syn::ExprBinary {
            left, op, right, ..
        }) => {
            if op != syn::BinOp::BitOr(Default::default()) {
                return Err(Error::new_spanned(op, "expected `from | manage_cnt`"));
            }
            let from = left;
            let manage_cnt = right;
            (from.as_ref().clone(), Some(manage_cnt))
        }
        _ => (from_manage_cnt, None),
    };

    while !input.is_empty() {
        let _ = input.parse::<syn::Token![=>]>()?;
        let pat: syn::Ident = if input.peek(syn::Token![_]) {
            let _ = input.parse::<syn::Token![_]>()?;
            syn::Ident::new("_", Span::call_site())
        } else {
            input.parse::<syn::Ident>()?
        };
        let _ = input.parse::<syn::Token![:]>()?;
        let ty = input.parse::<syn::Type>()?;
        stmts.push(quote! {
            con = cons.pop_front().unwrap();
            let #pat: #ty = con.take().unwrap();
        });
    }

    if let Some(manage_cnt) = manage_cnt {
        Ok(quote! {
            let mut cons = op.get_container(#from, #id).await;
            let mut con = donburako::container::Container::default();
            for _ in 0..#manage_cnt {
                con = cons.pop_front().unwrap();
                let _: () = con.take().unwrap();
            }
            #(#stmts)*
        })
    } else {
        Ok(quote! {
            let mut cons = op.get_container(#from, #id).await;
            let mut con = donburako::container::Container::default();
            #(#stmts)*
        })
    }
}

pub fn store_impl(tokens: TokenStream) -> TokenStream {
    store_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn store_parse(input: ParseStream) -> Result<TokenStream> {
    let mut stmts = Vec::new();
    let id = input.parse::<syn::Ident>()?;
    let _ = input.parse::<syn::Token![|]>()?;
    let to = input.parse::<syn::Expr>()?;

    while !input.is_empty() {
        let _ = input.parse::<syn::Token![=>]>()?;
        let stmt: syn::Expr = input.parse()?;
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
        op.add_container(#to, #id, output_cons)
            .await?;
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_take_parse() {
        let input = quote! {
            exec_id | self_.inputs() | self_.manage_cnt()
                => arg_to0: &str
        };
        let result = take_impl(input).to_string();
        let expected = quote! {
            let mut cons = op.get_container(self_.inputs(), exec_id).await;
            let mut con = donburako::container::Container::default();
            for _ in 0..self_.manage_cnt(){
                con = cons.pop_front().unwrap();
                let _: () = con.take().unwrap();
            }
            con = cons.pop_front().unwrap();
            let arg_to0: &str = con.take().unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_take_parse_multi() {
        let input = quote! {
            id | start | 0
                => _: ()
                => arg_0to1_int: fizz::i32
                => arg_0to1_str: &str
        };
        let result = take_impl(input).to_string();
        let expected = quote! {
            let mut cons = op.get_container(start, id).await;
            let mut con = donburako::container::Container::default();
            for _ in 0..0{
                con = cons.pop_front().unwrap();
                let _: () = con.take().unwrap();
            }
            con = cons.pop_front().unwrap();
            let _: () = con.take().unwrap();
            con = cons.pop_front().unwrap();
            let arg_0to1_int: fizz::i32 = con.take().unwrap();
            con = cons.pop_front().unwrap();
            let arg_0to1_str: &str = con.take().unwrap();
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_store_parse() {
        let input = quote! {
            exec_id | self_.outputs()
                => "1 -> 3"
        };
        let result = store_impl(input).to_string();
        let expected = quote! {
            let mut output_cons = std::collections::VecDeque::new();
            let mut con_clone = con.clone_container().unwrap();
            con_clone.store("1 -> 3");
            output_cons.push_back(con_clone);
            op.add_container(self_.outputs(), exec_id, output_cons)
                .await?;
        }
        .to_string();
        assert_eq!(result, expected,);
    }

    #[test]
    fn test_store_parse_multi() {
        let input = quote! {
            id | end
                => 42
                => "0 -> 1"
                => "0 -> 2"
                => "0 -> 3"
        };
        let result = store_impl(input).to_string();
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
            op.add_container(end, id, output_cons)
                .await?;
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
