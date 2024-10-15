use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn select_builder_impl(tokens: TokenStream) -> TokenStream {
    select_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn select_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let ty = input.parse::<syn::Type>()?;
    let mut name = format!("select_{}", quote!(#ty));
    name.retain(|c| !c.is_whitespace());
    Ok(quote! {
        {
        struct SelectBuilder {
            outputs: Vec<Arc<donburako::edge::Edge>>,
            func: Box<dyn for<'a> Fn(
                &'a donburako::node::Node,
                &'a donburako::operator::Operator,
                donburako::operator::ExecutorId,
            ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
            + Send
            + Sync>,
            is_blocking: bool,
            choice: donburako::node::Choice,
            name: &'static str,
        }
        impl donburako::node::NodeBuilder for SelectBuilder {
            fn new() -> Self {
                SelectBuilder {
                    outputs: vec![Arc::new(donburako::edge::Edge::new::<#ty>())],
                    func: node_func! {
                        let cons = op.get_container(self_.inputs(), exec_id).await;
                        op.add_container(self_.outputs(), exec_id, cons).await.unwrap();
                    },
                    is_blocking: false,
                    choice: donburako::node::Choice::Any,
                    name: #name,
                }
            }
            fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                &self.outputs
            }
            fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                for edge in inputs.iter().skip(manage_cnt) {
                    if !edge.check_type::<#ty>() {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
                    }
                }

                Ok(std::sync::Arc::new(donburako::node::Node::new(
                    inputs,
                    manage_cnt,
                    self.outputs,
                    self.func,
                    self.is_blocking,
                    self.name,
                    self.choice,
                )))
            }
        }
        SelectBuilder::new()
    }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_select_builderparse() {
        let input = quote! {Option<i32>};
        let result = select_builder_impl(input).to_string();
        let expected = quote! {
            {
                struct SelectBuilder {
                    outputs: Vec<Arc<donburako::edge::Edge>>,
                    func: Box<dyn for<'a> Fn(
                        &'a donburako::node::Node,
                        &'a donburako::operator::Operator,
                        donburako::operator::ExecutorId,
                    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
                    + Send
                    + Sync>,
                    is_blocking: bool,
                    choice: donburako::node::Choice,
                    name: &'static str,
                }
                impl donburako::node::NodeBuilder for SelectBuilder {
                    fn new() -> Self {
                        SelectBuilder {
                            outputs: vec![Arc::new(donburako::edge::Edge::new::<Option <i32> >())],
                            func: node_func! {
                                let cons = op.get_container(self_.inputs(), exec_id).await;
                                op.add_container(self_.outputs(), exec_id, cons).await.unwrap();
                            },
                            is_blocking: false,
                            choice: donburako::node::Choice::Any,
                            name: "select_Option<i32>",
                        }
                    }
                    fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                        &self.outputs
                    }
                    fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                        for edge in inputs.iter().skip(manage_cnt) {
                            if !edge.check_type::< Option < i32 > >() {
                                return Err(donburako::node::NodeError::EdgeTypeMismatch);
                            }
                        }

                        Ok(std::sync::Arc::new(donburako::node::Node::new(
                            inputs,
                            manage_cnt,
                            self.outputs,
                            self.func,
                            self.is_blocking,
                            self.name,
                            self.choice,
                        )))
                    }
                }
                SelectBuilder::new()
            }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
