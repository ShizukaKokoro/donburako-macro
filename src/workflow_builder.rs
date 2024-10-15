use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::{HashSet, VecDeque};
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{parse_quote, Error, Result};

fn get_vars_from_pat(pat: &syn::Pat, allow_tuple: bool) -> Result<Vec<syn::Ident>> {
    let mut vars = Vec::new();
    match pat {
        syn::Pat::Ident(syn::PatIdent { ident, .. }) => {
            vars.push(ident.clone());
        }
        syn::Pat::Tuple(syn::PatTuple { elems, .. }) => {
            if !allow_tuple {
                return Err(Error::new(pat.span(), "Invalid tuple pattern"));
            }
            for elem in elems.iter() {
                vars.extend(get_vars_from_pat(elem, true)?);
            }
        }
        syn::Pat::Type(syn::PatType { pat, .. }) => {
            vars.extend(get_vars_from_pat(pat, allow_tuple)?);
        }
        _ => {
            return Err(Error::new(pat.span(), "Invalid pattern"));
        }
    }
    Ok(vars)
}

fn get_types_from_type(ty: &syn::Type, allow_tuple: bool) -> Result<Vec<syn::TypePath>> {
    let mut types = Vec::new();
    match ty {
        syn::Type::Path(path) => {
            types.push(path.clone());
        }
        syn::Type::Tuple(syn::TypeTuple { elems, .. }) => {
            if !allow_tuple {
                return Err(Error::new(ty.span(), "Invalid tuple type"));
            }
            for elem in elems.iter() {
                types.extend(get_types_from_type(elem, true)?);
            }
        }
        _ => {
            return Err(Error::new(ty.span(), "Invalid type"));
        }
    }
    Ok(types)
}

fn node_name(ident: &syn::Ident) -> syn::Ident {
    syn::Ident::new(&format!("node_{}", ident), ident.span())
}

fn builder_name(path: &mut syn::Path) {
    let last = path.segments.last_mut().unwrap();
    last.ident = syn::Ident::new(
        &format!("{}Builder", last.ident.to_string().to_case(Case::Pascal)),
        last.ident.span(),
    );
}

fn edge_name(ident: &syn::Ident) -> syn::Ident {
    syn::Ident::new(&format!("edge_{}", ident), ident.span())
}

#[derive(Debug, Default)]
struct ManageQueue(Vec<VecDeque<syn::Ident>>);
impl ManageQueue {
    fn push(&mut self, edges: VecDeque<syn::Ident>) {
        self.0.push(edges);
    }

    fn pop(&mut self) -> Option<syn::Ident> {
        if let Some(edges) = self.0.first_mut() {
            if let Some(edge) = edges.pop_front() {
                return Some(edge);
            }
        }
        None
    }

    fn clear(&mut self) {
        let _ = self.0.pop();
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Debug)]
struct StmtVisitor {
    pub err: Option<Error>,
    pub node_names: Vec<(syn::Ident, Vec<syn::Ident>, usize)>, // (ノードの名前, エッジの名前, 管理エッジの数)
    pub builder_paths: Vec<TokenStream>,
    pub edge_map: HashSet<syn::Ident>,
    pub edge_idents: Vec<(syn::Ident, usize, usize)>, // (エッジの名前, ノードのインデックス, その番号)
    pub tmp_vars: Vec<syn::Ident>,
    pub branch_cnt: usize,
    pub tmp_manage_edges: ManageQueue,
    pub tmp_select: Option<usize>,
    pub output_edge: Vec<syn::Ident>,
}
impl StmtVisitor {
    fn new(start_edge: Vec<syn::Ident>) -> Result<Self> {
        let mut edge_map = HashSet::new();
        for edge in start_edge.iter() {
            if !edge_map.insert(edge.clone()) {
                return Err(Error::new(edge.span(), "Variable name is duplicated"));
            }
        }
        Ok(Self {
            err: None,
            node_names: Vec::new(),
            builder_paths: Vec::new(),
            edge_map,
            edge_idents: Vec::new(),
            tmp_vars: Vec::new(),
            branch_cnt: 0,
            tmp_manage_edges: ManageQueue::default(),
            tmp_select: None,
            output_edge: Vec::new(),
        })
    }
}
impl<'ast> Visit<'ast> for StmtVisitor {
    fn visit_expr_await(&mut self, expr_await: &'ast syn::ExprAwait) {
        match expr_await.base.as_ref() {
            syn::Expr::Call(expr_call) => {
                self.visit_expr_call(expr_call);
            }
            _ => {
                self.err = Some(Error::new(
                    expr_await.span(),
                    "Await expression must be a call expression",
                ));
            }
        }
    }

    fn visit_expr_call(&mut self, expr_call: &'ast syn::ExprCall) {
        match expr_call.func.as_ref().clone() {
            syn::Expr::Path(mut expr_path) => {
                let ident = expr_path.path.segments.last().unwrap().ident.clone();
                let node_idx = self.node_names.len();
                for (i, ident) in self.tmp_vars.iter().enumerate() {
                    let edge_name_ident = edge_name(ident);
                    if !self.edge_map.insert(edge_name_ident.clone()) {
                        self.err = Some(Error::new(
                            edge_name_ident.span(),
                            "Variable name is duplicated",
                        ));
                        return;
                    }
                    self.edge_idents
                        .push((edge_name_ident.clone(), node_idx, i));
                }
                let mut edge_vec = Vec::new();
                if let Some(manage) = self.tmp_manage_edges.pop() {
                    edge_vec.push(manage);
                }
                let manage_cnt = edge_vec.len();
                for arg in expr_call.args.iter() {
                    if let syn::Expr::Path(expr_path) = arg {
                        if let Some(ident) = expr_path.path.get_ident() {
                            let edge_name_ident = edge_name(ident);
                            if !self.edge_map.remove(&edge_name_ident) {
                                self.err = Some(Error::new(
                                    edge_name_ident.span(),
                                    "Variable name is not found. It may be undefined or moved",
                                ));
                                return;
                            }
                            edge_vec.push(edge_name(ident));
                        } else {
                            self.err = Some(Error::new(
                                arg.span(),
                                "Call expression argument must be an identifier",
                            ));
                            return;
                        }
                    } else {
                        self.err = Some(Error::new(
                            arg.span(),
                            "Call expression argument must be a path expression",
                        ));
                        return;
                    }
                }
                self.node_names
                    .push((node_name(&ident), edge_vec, manage_cnt));
                builder_name(&mut expr_path.path);
                self.builder_paths.push(parse_quote! { #expr_path::new() });
            }
            _ => {
                self.err = Some(Error::new(
                    expr_call.span(),
                    "Call expression must be a path expression",
                ));
            }
        }
    }

    fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
        let ident = self.tmp_vars.pop().unwrap();
        self.tmp_vars.clear();
        let node_idx = self.node_names.len();
        self.tmp_select = Some(node_idx);
        let edge_name_indent = edge_name(&ident);
        if !self.edge_map.insert(edge_name_indent.clone()) {
            self.err = Some(Error::new(
                edge_name_indent.span(),
                "Variable name is duplicated",
            ));
            return;
        }
        self.edge_idents.push((edge_name_indent, node_idx, 0));
        self.node_names.push((node_name(&ident), vec![], 0));
        if let syn::ExprIf {
            cond,
            then_branch,
            else_branch: Some((_, expr)),
            ..
        } = expr_if
        {
            let node_idx = self.node_names.len();
            let edge_vars = match cond.as_ref() {
                syn::Expr::Path(expr_path) => {
                    if let Some(ident) = expr_path.path.get_ident() {
                        vec![edge_name(ident)]
                    } else {
                        self.err = Some(Error::new(
                            cond.span(),
                            "If expression condition must be an identifier",
                        ));
                        return;
                    }
                }
                _ => {
                    self.err = Some(Error::new(
                        cond.span(),
                        "If expression condition must be a path expression",
                    ));
                    return;
                }
            };
            self.node_names.push((
                syn::Ident::new(&format!("node_branch_{}", self.branch_cnt), cond.span()),
                edge_vars,
                self.tmp_manage_edges.len(),
            ));

            let true_cnt = then_branch.stmts.len() - 1;
            let false_cnt = match expr.as_ref() {
                syn::Expr::Block(expr_block) => expr_block.block.stmts.len(),
                _ => 0,
            } - 1;

            let true_edges: VecDeque<_> = (0..true_cnt)
                .map(|i| {
                    syn::Ident::new(&format!("edge_true_{}_{}", self.branch_cnt, i), cond.span())
                })
                .collect();
            let false_edges: VecDeque<_> = (0..false_cnt)
                .map(|i| {
                    syn::Ident::new(
                        &format!("edge_false_{}_{}", self.branch_cnt, i),
                        cond.span(),
                    )
                })
                .collect();

            for (i, edge) in true_edges.iter().chain(false_edges.iter()).enumerate() {
                if !self.edge_map.insert(edge.clone()) {
                    self.err = Some(Error::new(ident.span(), "Variable name is duplicated"));
                    return;
                }
                self.edge_idents.push((edge.clone(), node_idx, i));
            }

            self.builder_paths
                .push(parse_quote! { branch_builder!(#true_cnt, #false_cnt) });

            self.tmp_manage_edges.push(true_edges);
            self.visit_block(then_branch);
            self.tmp_manage_edges.clear();
            self.tmp_manage_edges.push(false_edges);
            if let syn::Expr::If(expr_if_) = expr.as_ref() {
                self.visit_expr_if(expr_if_);
            } else if let syn::Expr::Block(expr_block) = expr.as_ref() {
                self.visit_block(&expr_block.block);
            }
            self.tmp_manage_edges.clear();
            return;
        }
        self.err = Some(Error::new(
            expr_if.span(),
            "If expression must have an else branch",
        ));
    }

    fn visit_expr_return(&mut self, expr_return: &'ast syn::ExprReturn) {
        if !self.output_edge.is_empty() {
            self.err = Some(Error::new(
                expr_return.span(),
                "Return expression must be only once",
            ));
            return;
        }
        if expr_return.expr.is_none() {
            self.err = Some(Error::new(
                expr_return.span(),
                "Return expression must have an expression",
            ));
            return;
        }
        let expr_return = expr_return.expr.as_ref().unwrap().as_ref();
        if let syn::Expr::Path(syn::ExprPath { path, .. }) = expr_return {
            if let Some(ident) = path.get_ident() {
                self.output_edge.push(ident.clone());
            }
        } else {
            self.err = Some(Error::new(
                expr_return.span(),
                "Return expression must be a path expression",
            ));
        }
    }

    fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
        match stmt {
            syn::Stmt::Local(syn::Local {
                pat,
                init: Some(syn::LocalInit { expr, .. }),
                ..
            }) => {
                let allow_tuple = !matches!(expr.as_ref(), syn::Expr::If(_));
                let vars = get_vars_from_pat(pat, allow_tuple).unwrap();
                self.tmp_vars = vars;
                match expr.as_ref() {
                    syn::Expr::Await(expr_await) => self.visit_expr_await(expr_await),
                    syn::Expr::Call(expr_call) => self.visit_expr_call(expr_call),
                    syn::Expr::If(expr_if) => {
                        if self.tmp_manage_edges.len() > 0 {
                            self.err = Some(Error::new(
                                expr.span(),
                                "Nested if statement is not supported yet",
                            ));
                        }
                        match pat {
                            syn::Pat::Type(syn::PatType { ty, .. }) => {
                                let ty = get_types_from_type(ty, false).unwrap().pop().unwrap();
                                self.builder_paths
                                    .push(parse_quote! { select_builder!(#ty) });
                            }
                            _ => {
                                self.err = Some(Error::new(
                                    pat.span(),
                                    "Local variable of if statement must be an identifier",
                                ));
                                return;
                            }
                        };
                        self.visit_expr_if(expr_if);
                    }
                    _ => {
                        self.err = Some(Error::new(
                            expr.span(),
                            "Statement must be await, call, or if expression",
                        ));
                    }
                }
            }
            syn::Stmt::Expr(expr, _) => match expr {
                syn::Expr::Path(syn::ExprPath { path, .. }) => {
                    if let Some(select_idx) = self.tmp_select {
                        if let Some(ident) = path.get_ident() {
                            self.node_names[select_idx].1.push(edge_name(ident));
                        } else {
                            self.err = Some(Error::new(
                                expr.span(),
                                "End of if statement must be a local variable",
                            ));
                        }
                    } else {
                        self.err = Some(Error::new(
                            expr.span(),
                            "End of if statement must be require a local variable",
                        ));
                    }
                }
                syn::Expr::Return(expr_return) => self.visit_expr_return(expr_return),
                _ => {
                    self.err = Some(Error::new(
                        expr.span(),
                        "Statement must be a return expression, if it is an expression",
                    ));
                }
            },
            _ => {
                self.err = Some(Error::new(
                    stmt.span(),
                    "Statement must be a local variable or return",
                ));
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
    let func_vis = &func.vis;

    let (start_edge_exprs, start_edges): (Vec<_>, Vec<syn::Ident>) = {
        let mut start_edge_exprs = Vec::new();
        let mut start_edges = Vec::new();
        for (name, arg) in func_args {
            let edge_name = syn::Ident::new(&format!("edge_{}", name), name.span());
            start_edge_exprs.push(quote! {
                let #edge_name = Arc::new(donburako::edge::Edge::new::<#arg>());
            });
            start_edges.push(edge_name);
        }
        (start_edge_exprs, start_edges)
    };

    let mut visitor = StmtVisitor::new(start_edges.clone()).unwrap();
    visitor.visit_block(&func.block);
    if let Some(err) = visitor.err {
        return Err(err);
    }
    assert_eq!(visitor.tmp_manage_edges.len(), 0);

    let mut node_var_let: Vec<TokenStream> = Vec::new();
    let mut build_nodes: Vec<TokenStream> = Vec::new();
    let mut add_nodes: Vec<TokenStream> = Vec::new();
    for ((node_name, edge_vec, manage_cnt), path) in
        visitor.node_names.iter().zip(visitor.builder_paths.iter())
    {
        node_var_let.push(quote! {
            let #node_name = #path;
        });
        build_nodes.push(quote! {
            let #node_name = #node_name.build(vec![#(#edge_vec.clone()),*], #manage_cnt)?;
        });
        add_nodes.push(quote! {
            .add_node(#node_name)?
        });
    }

    let mut edge_exprs: Vec<TokenStream> = Vec::new();
    let mut node_output_asserts: Vec<TokenStream> = Vec::new();
    let mut cnt = 0usize;
    let mut pre = None;
    for (edge_name, node_idx, edge_idx) in visitor.edge_idents.iter() {
        let node_name = &visitor.node_names[*node_idx].0;
        if pre.is_none() {
            cnt = 0;
            pre = Some(node_name.clone());
        } else if pre.as_ref().unwrap() != node_name {
            node_output_asserts.push(quote! {
                assert_eq!(#pre.outputs().len(), #cnt);
            });
            cnt = 0;
            pre = Some(node_name.clone());
        }
        edge_exprs.push(quote! {
            let #edge_name = #node_name.outputs()[#edge_idx].clone();
        });
        cnt += 1;
    }
    node_output_asserts.push(quote! {
        assert_eq!(#pre.outputs().len(), #cnt);
    });

    let end_edges: Vec<syn::Ident> = visitor.output_edge.iter().map(edge_name).collect();

    Ok(quote! {
        #func_vis fn #func_name_workflow() -> Result<
            (
                donburako::workflow::WorkflowId,
                donburako::workflow::WorkflowBuilder,
                Vec<std::sync::Arc<donburako::edge::Edge>>,
                Vec<std::sync::Arc<donburako::edge::Edge>>,
            ),
            Box<dyn std::error::Error>,
        > {
            let wf_id = donburako::workflow::WorkflowId::new(#func_name_str);
            #(#node_var_let)*
            #(#start_edge_exprs)*
            #(#edge_exprs)*
            #(#node_output_asserts)*
            #(#build_nodes)*
            let builder = donburako::workflow::WorkflowBuilder::default()
                #(#add_nodes)*
                ;
            Ok((wf_id, builder, vec![#(#start_edges),*], vec![#(#end_edges),*]))
        }
        #func
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use syn::parse_quote;

    #[test]
    fn test_get_vars_from_pat_ident() {
        let input = syn::parse_quote! {
            n
        };
        let result = get_vars_from_pat(&input, true).unwrap();
        let expected = vec![syn::Ident::new("n", input.span())];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_get_vars_from_pat_tuple() {
        let input = syn::parse_quote! {
            (n0, n1)
        };
        let result = get_vars_from_pat(&input, true).unwrap();
        let expected = vec![
            syn::Ident::new("n0", input.span()),
            syn::Ident::new("n1", input.span()),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_get_vars_from_pat_type() {
        let input: syn::Pat = syn::Pat::Type(parse_quote!(n: i32));
        let result = get_vars_from_pat(&input, true).unwrap();
        let expected = vec![syn::Ident::new("n", input.span())];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_get_vars_from_pat_type_tuple() {
        let input = syn::Pat::Type(parse_quote! {
            (n0, n1): (i32, i32)
        });
        let result = get_vars_from_pat(&input, true).unwrap();
        let expected = vec![
            syn::Ident::new("n0", input.span()),
            syn::Ident::new("n1", input.span()),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_get_types_from_type_path() {
        let input = syn::parse_quote! {
            i32
        };
        let result = get_types_from_type(&input, true).unwrap();
        let expected = vec![syn::parse_quote! { i32 }];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_get_types_from_type_tuple() {
        let input = syn::parse_quote! {
            (i32, i32)
        };
        let result = get_types_from_type(&input, true).unwrap();
        let expected = vec![syn::parse_quote! { i32 }, syn::parse_quote! { i32 }];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_builder_impl() {
        let input = quote! {
            async fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide2(n).await;
                let even = some::is_even(n0);
                let select: Option<i32> = if even {
                    let double = double(n1);
                    double
                } else {
                    let none = none();
                    none
                };
                return select;
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
                let wf_id = donburako::workflow::WorkflowId::new("func_map");

                let node_divide2 = Divide2Builder::new();
                let node_is_even = some::IsEvenBuilder::new();
                let node_select = select_builder!(Option<i32>);
                let node_branch_0 = branch_builder!(1usize, 1usize);
                let node_double = DoubleBuilder::new();
                let node_none = NoneBuilder::new();

                let edge_n = Arc::new(donburako::edge::Edge::new::<i32>());
                let edge_n0 = node_divide2.outputs()[0usize].clone();
                let edge_n1 = node_divide2.outputs()[1usize].clone();
                let edge_even = node_is_even.outputs()[0usize].clone();
                let edge_select = node_select.outputs()[0usize].clone();
                let edge_true_0_0 = node_branch_0.outputs()[0usize].clone();
                let edge_false_0_0 = node_branch_0.outputs()[1usize].clone();
                let edge_double = node_double.outputs()[0usize].clone();
                let edge_none = node_none.outputs()[0usize].clone();

                assert_eq!(node_divide2.outputs().len(), 2usize);
                assert_eq!(node_is_even.outputs().len(), 1usize);
                assert_eq!(node_select.outputs().len(), 1usize);
                assert_eq!(node_branch_0.outputs().len(), 2usize);
                assert_eq!(node_double.outputs().len(), 1usize);
                assert_eq!(node_none.outputs().len(), 1usize);

                let node_divide2 = node_divide2.build(vec![edge_n.clone()], 0usize)?;
                let node_is_even = node_is_even.build(vec![edge_n0.clone()], 0usize)?;
                let node_select = node_select.build(vec![edge_double.clone(), edge_none.clone()], 0usize)?;
                let node_branch_0 = node_branch_0.build(vec![edge_even.clone()], 0usize)?;
                let node_double = node_double.build(vec![edge_true_0_0.clone(), edge_n1.clone()], 1usize)?;
                let node_none = node_none.build(vec![edge_false_0_0.clone()], 1usize)?;

                let builder = donburako::workflow::WorkflowBuilder::default()
                    .add_node(node_divide2)?
                    .add_node(node_is_even)?
                    .add_node(node_select)?
                    .add_node(node_branch_0)?
                    .add_node(node_double)?
                    .add_node(node_none)?;

                Ok((wf_id, builder, vec![edge_n], vec![edge_select]))
            }
            async fn func_map(n: i32) -> Option<i32> {
                let (n0, n1) = divide2(n).await;
                let even = some::is_even(n0);
                let select: Option<i32> = if even {
                    let double = double(n1);
                    double
                } else {
                    let none = none();
                    none
                };
                return select;
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_builder_parse() {
        let input = quote! {
            fn sum(n: i32) -> i32 {
                let (n0, n1, n2) = divide3(n);
                let is_zero = is_zero(n0);
                let selected: i32 = if is_zero {
                    let zero = zero();
                    zero
                } else {
                    let sub = sub(n1);
                    let rec = rec(sub);
                    let add = add(n2, rec);
                    add
                };
                return selected;
            }
        };
        let result = workflow_builder_parse.parse2(input).unwrap().to_string();
        let expected = quote! {
            fn sum_workflow() -> Result<
                (
                    donburako::workflow::WorkflowId,
                    donburako::workflow::WorkflowBuilder,
                    Vec<std::sync::Arc<donburako::edge::Edge>>,
                    Vec<std::sync::Arc<donburako::edge::Edge>>,
                ),
                Box<dyn std::error::Error>,
            > {
                let wf_id = donburako::workflow::WorkflowId::new("sum");

                let node_divide3 = Divide3Builder::new();
                let node_is_zero = IsZeroBuilder::new();
                let node_selected = select_builder!(i32);
                let node_branch_0 = branch_builder!(1usize, 3usize);
                let node_zero = ZeroBuilder::new();
                let node_sub = SubBuilder::new();
                let node_rec = RecBuilder::new();
                let node_add = AddBuilder::new();

                let edge_n = Arc::new(donburako::edge::Edge::new::<i32>());
                let edge_n0 = node_divide3.outputs()[0usize].clone();
                let edge_n1 = node_divide3.outputs()[1usize].clone();
                let edge_n2 = node_divide3.outputs()[2usize].clone();
                let edge_is_zero = node_is_zero.outputs()[0usize].clone();
                let edge_selected = node_selected.outputs()[0usize].clone();
                let edge_true_0_0 = node_branch_0.outputs()[0usize].clone();
                let edge_false_0_0 = node_branch_0.outputs()[1usize].clone();
                let edge_false_0_1 = node_branch_0.outputs()[2usize].clone();
                let edge_false_0_2 = node_branch_0.outputs()[3usize].clone();
                let edge_zero = node_zero.outputs()[0usize].clone();
                let edge_sub = node_sub.outputs()[0usize].clone();
                let edge_rec = node_rec.outputs()[0usize].clone();
                let edge_add = node_add.outputs()[0usize].clone();

                assert_eq!(node_divide3.outputs().len(), 3usize);
                assert_eq!(node_is_zero.outputs().len(), 1usize);
                assert_eq!(node_selected.outputs().len(), 1usize);
                assert_eq!(node_branch_0.outputs().len(), 4usize);
                assert_eq!(node_zero.outputs().len(), 1usize);
                assert_eq!(node_sub.outputs().len(), 1usize);
                assert_eq!(node_rec.outputs().len(), 1usize);
                assert_eq!(node_add.outputs().len(), 1usize);

                let node_divide3 = node_divide3.build(vec![edge_n.clone()], 0usize)?;
                let node_is_zero = node_is_zero.build(vec![edge_n0.clone()], 0usize)?;
                let node_selected = node_selected.build(vec![edge_zero.clone(), edge_add.clone()], 0usize)?;
                let node_branch_0 = node_branch_0.build(vec![edge_is_zero.clone()], 0usize)?;
                let node_zero = node_zero.build(vec![edge_true_0_0.clone()], 1usize)?;
                let node_sub = node_sub.build(vec![edge_false_0_0.clone(), edge_n1.clone()], 1usize)?;
                let node_rec = node_rec.build(vec![edge_false_0_1.clone(), edge_sub.clone()], 1usize)?;
                let node_add =
                    node_add.build(vec![edge_false_0_2.clone(), edge_n2.clone(), edge_rec.clone()], 1usize)?;

                let builder = donburako::workflow::WorkflowBuilder::default()
                    .add_node(node_divide3)?
                    .add_node(node_is_zero)?
                    .add_node(node_selected)?
                    .add_node(node_branch_0)?
                    .add_node(node_zero)?
                    .add_node(node_sub)?
                    .add_node(node_rec)?
                    .add_node(node_add)?;

                Ok((wf_id, builder, vec![edge_n], vec![edge_selected]))
            }
            fn sum(n: i32) -> i32 {
                let (n0, n1, n2) = divide3(n);
                let is_zero = is_zero(n0);
                let selected: i32 = if is_zero {
                    let zero = zero();
                    zero
                } else {
                    let sub = sub(n1);
                    let rec = rec(sub);
                    let add = add(n2, rec);
                    add
                };
                return selected;
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
