use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Error, Result};

#[derive(Debug, Default)]
struct StmtVisitor {
    pub err: Option<Error>,
    pub node_var_let: Vec<TokenStream>,
    pub add_nodes: Vec<TokenStream>,
    pub branch_cnt: usize,
    pub select_cnt: usize,
}
impl StmtVisitor {
    fn inner_visit_stmt(&mut self, stmts: &[syn::Stmt]) {
        for (i, stmt) in stmts.iter().enumerate() {
            if i == stmts.len() - 1 {
                match stmt {
                    syn::Stmt::Local(syn::Local {
                        init: Some(local_init),
                        ..
                    }) => {
                        self.visit_local_init(local_init);
                    }
                    syn::Stmt::Expr(expr, _) => {}
                    _ => {
                        self.err = Some(Error::new(stmt.span(), "Invalid statement"));
                    }
                }
            } else {
                self.visit_stmt(stmt);
            }
        }
    }
}
impl<'ast> Visit<'ast> for StmtVisitor {
    fn visit_expr_call(&mut self, expr_call: &'ast syn::ExprCall) {
        let mut path = match expr_call.func.as_ref() {
            syn::Expr::Path(syn::ExprPath { path, .. }) => path.clone(),
            _ => {
                self.err = Some(Error::new(expr_call.span(), "Invalid function call"));
                return;
            }
        };
        let node_var = syn::Ident::new(
            &format!("node_{}", path.segments.last().unwrap().ident),
            path.segments.last().unwrap().ident.span(),
        );
        let name = path.segments.last().unwrap().ident.to_string();
        let builder_name = syn::Ident::new(
            &format!("{}Builder", name.to_string().to_case(Case::Pascal)),
            name.span(),
        );
        path.segments.last_mut().unwrap().ident = builder_name;
        self.node_var_let.push(quote! {
            let #node_var = #path::new();
        });
        self.add_nodes.push(quote! {
            .add_node(#node_var)?
        });
    }

    fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
        let branch_name =
            syn::Ident::new(&format!("node_branch_{}", self.branch_cnt), expr_if.span());
        self.node_var_let.push(quote! {
            let #branch_name = branch_builder!();
        });
        self.add_nodes.push(quote! {
            .add_node(#branch_name)?
        });
        self.branch_cnt += 1;
        let syn::ExprIf {
            cond,
            then_branch,
            else_branch,
            ..
        } = expr_if;
        self.inner_visit_stmt(&then_branch.stmts);
        if let Some((_, else_expr)) = else_branch {
            match else_expr.as_ref() {
                syn::Expr::Block(block) => {
                    self.inner_visit_stmt(&block.block.stmts);
                }
                _ => {
                    self.err = Some(Error::new(else_expr.span(), "Invalid expression"));
                }
            }
        }
    }

    fn visit_local_init(&mut self, local_init: &'ast syn::LocalInit) {
        match local_init.expr.as_ref() {
            syn::Expr::Await(expr_await) => match expr_await.base.as_ref() {
                syn::Expr::Call(expr_call) => {
                    self.visit_expr_call(expr_call);
                }
                _ => {
                    self.err = Some(Error::new(expr_await.base.span(), "Invalid expression"));
                }
            },
            syn::Expr::Call(expr_call) => {
                self.visit_expr_call(expr_call);
            }
            syn::Expr::If(expr_if) => {
                self.visit_expr_if(expr_if);
            }
            _ => {
                self.err = Some(Error::new(local_init.expr.span(), "Invalid expression"));
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
        match stmt {
            syn::Stmt::Local(syn::Local {
                pat,
                init: Some(local_init),
                ..
            }) => {
                if let syn::Expr::If(_) = local_init.expr.as_ref() {
                    let ty = match pat {
                        syn::Pat::Type(syn::PatType { ty, .. }) => ty.clone(),
                        _ => {
                            self.err = Some(Error::new(pat.span(), "Invalid pattern"));
                            return;
                        }
                    };
                    let select_name = syn::Ident::new(
                        &format!("node_select_{}", self.select_cnt),
                        local_init.expr.span(),
                    );
                    self.node_var_let.push(quote! {
                        let #select_name = select_builder!(#ty);
                    });
                    self.add_nodes.push(quote! {
                        .add_node(#select_name)?
                    });
                }
                self.visit_local_init(local_init);
            }
            syn::Stmt::Expr(
                syn::Expr::Return(syn::ExprReturn {
                    expr: Some(expr), ..
                }),
                _,
            ) => {}
            _ => {
                self.err = Some(Error::new(stmt.span(), "Invalid statement"));
            }
        }
    }
}

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
    let func_args = Vec::from_iter(func.sig.inputs.iter().map(|arg| {
        if let syn::FnArg::Typed(pat) = arg {
            match pat.pat.as_ref() {
                syn::Pat::Ident(ident) => return (ident.ident.clone(), pat.ty.clone()),
                _ => panic!("Invalid function argument"),
            }
        }
        panic!("Invalid function argument");
    }));

    let mut visitor = StmtVisitor::default();
    visitor.visit_block(&func.block);
    if let Some(err) = visitor.err {
        return Err(err);
    }

    let node_var_let = visitor.node_var_let;
    let add_nodes = visitor.add_nodes;

    let (input_edge_exprs, input_edges) = {
        let mut input_edge_exprs = Vec::new();
        let mut input_edges = Vec::new();
        for (name, arg) in func_args {
            let edge_name = syn::Ident::new(&format!("edge_{}", name), name.span());
            input_edge_exprs.push(quote! {
                let #edge_name = Arc::new(Edge::new::<#arg>());
            });
            input_edges.push(quote! { #edge_name });
        }
        (input_edge_exprs, input_edges)
    };
    let output_edges: Vec<syn::Ident> = Vec::new();

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
            #(#node_var_let)*
            #(#input_edge_exprs)*

            let builder = WorkflowBuilder::default()
                #(#add_nodes)*
                ;
            Ok((wf_id, builder, vec![#(#input_edges),*], vec![#(#output_edges),*]))
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
            async fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide2(n).await;
                let even = some::is_even(n0);
                let selected: Option<i32> = if even {
                    let res = double(n1);
                    res
                } else {
                    let res = none();
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
                let node_is_even = some::IsEvenBuilder::new();
                let node_select_0 = select_builder!(Option<i32>);
                let node_branch_0 = branch_builder!();
                let node_double = DoubleBuilder::new();
                let node_none = NoneBuilder::new();

                let edge_n = Arc::new(Edge::new::<i32>());
                let edge_n0 = node_divide2.outputs()[0].clone();
                let edge_n1 = node_divide2.outputs()[1].clone();
                let edge_even = node_is_even.outputs()[0].clone();
                let edge_true = node_branch_0.outputs()[0].clone();
                let edge_false = node_branch_0.outputs()[1].clone();
                let edge_double = node_double.outputs()[0].clone();
                let edge_none = node_none.outputs()[0].clone();
                let edge_select = node_select_0.outputs()[0].clone();

                let node_divide2 = node_divide2.build(vec![edge_n.clone()], 0)?;
                let node_is_even = node_is_even.build(vec![edge_n0.clone()], 0)?;
                let node_select_0 = node_select_0.build(vec![edge_double.clone(), edge_none.clone()], 0)?;
                let node_branch_0 = node_branch_0.build(vec![edge_even.clone()], 0)?;
                let node_double = node_double.build(vec![edge_true.clone(), edge_n1.clone()], 1)?;
                let node_none = node_none.build(vec![edge_false.clone()], 1)?;

                let builder = WorkflowBuilder::default()
                    .add_node(node_divide2)?
                    .add_node(node_is_even)?
                    .add_node(node_select_0)?
                    .add_node(node_branch_0)?
                    .add_node(node_double)?
                    .add_node(node_none)?;

                Ok((wf_id, builder, vec![edge_n], vec![edge_select]))
            }
            async fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide2(n).await;
                let even = some::is_even(n0);
                let selected: Option<i32> = if even {
                    let res = double(n1);
                    res
                } else {
                    let res = none();
                    res
                };
                return selected;
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
