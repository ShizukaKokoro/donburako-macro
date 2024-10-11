use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn workflow_builder_impl(_: TokenStream, tokens: TokenStream) -> TokenStream {
    workflow_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn workflow_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let func = input.parse::<syn::ItemFn>()?;
    let func_name = &func.sig.ident;
    let func_name_workflow = syn::Ident::new(&format!("{}_workflow", func_name), func_name.span());
    let func_name_str = func_name.to_string();

    let mut node_names: Vec<syn::Ident> = Vec::new();
    let mut input_nodes: Vec<syn::Ident> = Vec::new();
    let mut output_nodes: Vec<syn::Ident> = Vec::new();

    let (node_var_names, add_nodes) = {
        let mut node_var_names = Vec::new();
        let mut add_nodes = Vec::new();
        for name in node_names.iter() {
            let builder_name = syn::Ident::new(&format!("{}Builder", name), name.span());
            let node_name = syn::Ident::new(&format!("node_{}", name), name.span());
            node_var_names.push(quote! {
                let #node_name = #builder_name::new();
            });
            add_nodes.push(quote! {
                .add_node(#node_name)?
            });
        }
        (node_var_names, add_nodes)
    };
    Ok(quote! {
        fn #func_name_workflow() -> Result<
            (
                donburako::workflow::WorkflowId,
                donburako::workflow::WorkflowBuilder,
                Vec<std::sync::Arc<donburako::edge::Edge>>,
                Vec<std::sync::Arc<donburako::edge::Edge>>,
            ),
            Box<dyn std::error::Error>,
        > {
            let wf_id = WorkflowId::new(#func_name_str);
            {
                #(#node_var_names)*
            }

            let builder = WorkflowBuilder::default()
                #(#add_nodes)*
                ;
            Ok((wf_id, builder, vec![#(#input_nodes),*], vec![#(#output_nodes),*]))
        }
        #func
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_workflow_builder_impl() {
        let input = quote! {
            fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide(n);
                let even: bool = is_even(n0);
                let selected: Option<i32> = if even {
                    let res: Option<i32> = double(n1);
                    res
                } else {
                    let res: Option<i32> = none();
                    res
                };
                return selected;
            }
        };
        let result = workflow_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            fn func_map_workflow() -> Result<
                (
                    donburako::workflow::WorkflowId,
                    donburako::workflow::WorkflowBuilder,
                    Vec<std::sync::Arc<donburako::edge::Edge>>,
                    Vec<std::sync::Arc<donburako::edge::Edge>>,
                ),
                Box<dyn std::error::Error>,
            > {
                let wf_id = WorkflowId::new("func_map");

                let node_divide2 = Divide2Builder::new();
                let node_is_even = IsEvenBuilder::new();
                let node_double = DoubleBuilder::new();
                let node_none = NoneBuilder::new();
                let node_branch = branch_builder!();
                let node_select = select_builder!(Option<i32>);

                let edge_n = Arc::new(Edge::new::<i32>());
                let edge_n0 = node_divide2.outputs()[0].clone();
                let edge_n1 = node_divide2.outputs()[1].clone();
                let edge_even = node_is_even.outputs()[0].clone();
                let edge_true = node_branch.outputs()[0].clone();
                let edge_false = node_branch.outputs()[1].clone();
                let edge_double = node_double.outputs()[0].clone();
                let edge_none = node_none.outputs()[0].clone();
                let edge_select = node_select.outputs()[0].clone();

                let node_divide2 = node_divide2.build(vec![edge_n.clone()], 0)?;
                let node_is_even = node_is_even.build(vec![edge_n0.clone()], 0)?;
                let node_branch = node_branch.build(vec![edge_even.clone()], 0)?;
                let node_double = node_double.build(vec![edge_true.clone(), edge_n1.clone()], 1)?;
                let node_none = node_none.build(vec![edge_false.clone()], 1)?;
                let node_select = node_select.build(vec![edge_double.clone(), edge_none.clone()], 0)?;

                let builder = WorkflowBuilder::default()
                    .add_node(node_divide2)?
                    .add_node(node_is_even)?
                    .add_node(node_branch)?
                    .add_node(node_double)?
                    .add_node(node_none)?
                    .add_node(node_select)?;

                Ok((wf_id, builder, vec![edge_n], vec![edge_select]))
            }
            fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide2(n);
                let even: bool = is_even(n0);
                let selected: Option<i32> = if even {
                    let res: Option<i32> = double(n1);
                    res
                } else {
                    let res: Option<i32> = none();
                    res
                };
                return selected;
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
