use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{parse_quote, Error, Result};

pub fn branch_builder_impl(tokens: TokenStream) -> TokenStream {
    branch_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn branch_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let true_cnt = input.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
    let _ = input.parse::<syn::Token![,]>()?;
    let false_cnt = input.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
    let branch_cnt = true_cnt + false_cnt;
    if branch_cnt < 2 {
        return Err(Error::new_spanned(
            branch_cnt,
            "branch count must be greater than or equal to 2",
        ));
    }
    let outputs = (0..branch_cnt)
        .map(|_| quote! {Arc::new(donburako::edge::Edge::new::<()>())})
        .collect::<Vec<_>>();
    let true_output: Vec<TokenStream> = (0..true_cnt).map(|_| parse_quote!( => ())).collect();
    let false_output: Vec<TokenStream> = (0..false_cnt).map(|_| parse_quote!( => ())).collect();
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
            true_cnt: usize,
            false_cnt: usize,
        }
        impl donburako::node::NodeBuilder for BranchBuilder {
            fn new() -> Self {
                BranchBuilder {
                    outputs: vec![#( #outputs ),*],
                    func: node_func! {
                        take! {
                            exec_id | self_.inputs()
                                => state: bool
                        }
                        if state {
                            store!{
                                exec_id | &self_.outputs()[..#true_cnt]
                                    #( #true_output )*
                            }
                        } else {
                            store!{
                                exec_id | &self_.outputs()[#true_cnt..]
                                    #( #false_output )*
                            }
                        }
                    },
                    is_blocking: false,
                    choice: donburako::node::Choice::All,
                    name: "branch",
                    true_cnt: #true_cnt,
                    false_cnt: #false_cnt,
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
        let input = quote! {1, 2};
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
                true_cnt: usize,
                false_cnt: usize,
            }
            impl donburako::node::NodeBuilder for BranchBuilder {
                fn new() -> Self {
                    BranchBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::<()>()), Arc::new(donburako::edge::Edge::new::<()>()), Arc::new(donburako::edge::Edge::new::<()>())],
                        func: node_func! {
                            take! {
                                exec_id | self_.inputs()
                                    => state: bool
                            }
                            if state {
                                store!{
                                    exec_id | &self_.outputs()[..1usize]
                                        => ()
                                }
                            } else {
                                store!{
                                    exec_id | &self_.outputs()[1usize..]
                                        => ()
                                        => ()
                                }
                            }
                        },
                        is_blocking: false,
                        choice: donburako::node::Choice::All,
                        name: "branch",
                        true_cnt: 1usize,
                        false_cnt: 2usize,
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
