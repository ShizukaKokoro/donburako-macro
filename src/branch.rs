use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn branch_builder_impl(tokens: TokenStream) -> TokenStream {
    branch_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn branch_builder_parse(_: ParseStream) -> Result<TokenStream> {
    Ok(quote! {
        {
        struct BranchBuilder {
            outputs: Vec<Arc<donburako::edge::Edge>>,
            func: Box<dyn for<'a> Fn(
                &'a Node,
                &'a donburako::operator::Operator,
                donburako::operator::ExecutorId,
            ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
            + Send
            + Sync>,
            is_blocking: bool,
            choice: donburako::node::Choice,
            name: &'static str,
        }
        impl donburako::node::NodeBuilder for BranchBuilder {
            fn new() -> Self {
                BranchBuilder {
                    outputs: vec![Arc::new(donburako::edge::Edge::new::<()>()), Arc::new(donburako::edge::Edge::new::<()>())],
                    func: node_func! {
                        take! {
                            exec_id | self_.inputs()
                                => state: bool
                        }
                        store!{
                            exec_id | &vec![if state { self_.outputs()[0].clone() } else { self_.outputs()[1].clone() }]
                                => ()
                        }
                    },
                    is_blocking: false,
                    choice: donburako::node::Choice::All,
                    name: "branch",
                }
            }
            fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                &self.outputs
            }
            fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                if let Some(edge) = inputs.get(manage_cnt) {
                    if !edge.check_type::<bool>() {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
                    }
                } else {
                    return Err(donburako::node::NodeError::EdgeTypeMismatch);
                }

                Ok(std::sync::Arc::new(Node::new(
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
        BranchBuilder::new()
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
        let result = branch_builder_impl(input).to_string();
        let expected = quote! {
            {
            struct BranchBuilder {
                outputs: Vec<Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a Node,
                    &'a donburako::operator::Operator,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for BranchBuilder {
                fn new() -> Self {
                    BranchBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::<()>()), Arc::new(donburako::edge::Edge::new::<()>())],
                        func: node_func! {
                            take! {
                                exec_id | self_.inputs()
                                    => state: bool
                            }
                            store!{
                                exec_id | &vec![if state { self_.outputs()[0].clone() } else { self_.outputs()[1].clone() }]
                                    => ()
                            }
                        },
                        is_blocking: false,
                        choice: donburako::node::Choice::All,
                        name: "branch",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt) {
                        if !edge.check_type::<bool>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
                    }

                    Ok(std::sync::Arc::new(Node::new(
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
            BranchBuilder::new()
        }
        }
        .to_string();
        assert_eq!(result, expected,);
    }
}
