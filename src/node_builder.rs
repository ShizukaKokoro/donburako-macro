use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn node_builder_impl(_: TokenStream, tokens: TokenStream) -> TokenStream {
    node_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn node_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let func = input.parse::<syn::ItemFn>()?;
    let func_name = &func.sig.ident;
    let struct_name = syn::Ident::new(
        &format!("{}Builder", func_name.to_string().to_case(Case::Pascal)),
        func_name.span(),
    );
    Ok(quote! {
        struct #struct_name {
            outputs: Vec<Arc<Edge>>,
            func: Box<AsyncFn>,
            is_blocking: bool,
            choice: Choice,
            name: &'static str,
        }
        impl donburako::node::NodeBuilder for #struct_name {
            fn new() -> Self {
                todo!()
            }
            fn outputs(&self) -> &Vec<Arc<Edge>> {
                &self.outputs
            }
            fn build(self, inputs: Vec<Arc<Edge>>) -> Node {
                Node::new(
                    inputs,
                    self.outputs,
                    self.func,
                    self.is_blocking,
                    self.name,
                    self.choice,
                )
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_node_builder_impl() {
        let input = quote! {
            fn divide(n: i32) -> (i32, i32) {
                return (n, n);
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct DivideBuilder {
                outputs: Vec<Arc<Edge>>,
                func: Box<AsyncFn>,
                is_blocking: bool,
                choice: Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for DivideBuilder {
                fn new() -> Self {
                    DivideNode {
                        outputs: vec![Arc::new(Edge::new::<i32>()), Arc::new(Edge::new::<i32>())],
                        func: node_func! {
                            input!(n: i32);
                            output!(n, n);
                        },
                        is_blocking: false,
                        choice: Choice::All,
                        name: "divide",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec<Arc<Edge>>) -> Node {
                    Node::new(
                        inputs,
                        self.outputs,
                        self.func,
                        self.is_blocking,
                        self.name,
                        self.choice,
                    )
                }
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
