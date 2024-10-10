use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{parse_quote, Error, Result};

pub fn workflow_impl(tokens: TokenStream) -> TokenStream {
    workflow_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn workflow_parse(input: ParseStream) -> Result<TokenStream> {
    let init_expr = input.parse::<syn::Expr>()?;
    let _ = input.parse::<syn::Token![;]>()?;
    let mut for_block = input.parse::<syn::ExprForLoop>()?;
    let let_stmt = for_block.body.stmts.first().unwrap();
    let (wf_name, args, rtns): (syn::Ident, Vec<syn::Ident>, Vec<syn::Pat>) = {
        match let_stmt {
            syn::Stmt::Local(local) => {
                let (wf_name, args) = if let Some(local_init) = &local.init {
                    let wf_name = match local_init.expr.as_ref() {
                        syn::Expr::Call(call) => match call.func.as_ref() {
                            syn::Expr::Path(path) => {
                                let wf_name = path.path.segments.first().unwrap().ident.clone();
                                wf_name
                            }
                            _ => {
                                return Err(Error::new(
                                    local.span(),
                                    "expected initialization with function call",
                                ))
                            }
                        },
                        _ => {
                            return Err(Error::new(
                                local.span(),
                                "expected initialization with function call",
                            ))
                        }
                    };
                    let args = match local_init.expr.as_ref() {
                        syn::Expr::Call(call) => {
                            let args = call.args.clone();
                            let mut arg_vec = Vec::new();
                            for arg in args.iter() {
                                match arg {
                                    syn::Expr::Path(path) => {
                                        let arg_name =
                                            path.path.segments.first().unwrap().ident.clone();
                                        arg_vec.push(arg_name);
                                    }
                                    _ => {
                                        return Err(Error::new(
                                            local.span(),
                                            "expected initialization with function call",
                                        ))
                                    }
                                }
                            }
                            arg_vec
                        }
                        _ => {
                            return Err(Error::new(
                                local.span(),
                                "expected initialization with function call",
                            ))
                        }
                    };
                    (wf_name, args)
                } else {
                    return Err(Error::new(local.span(), "initialization is required"));
                };

                let mut rtns = vec![];
                match &local.pat {
                    syn::Pat::Type(pat_type) => match pat_type.pat.as_ref() {
                        syn::Pat::Ident(ident) => {
                            let ty = pat_type.ty.as_ref();
                            rtns.push(syn::Pat::Type(syn::PatType {
                                attrs: vec![],
                                pat: Box::new(syn::Pat::Ident(ident.clone())),
                                colon_token: syn::Token![:](ident.span()),
                                ty: Box::new(ty.clone()),
                            }))
                        }
                        syn::Pat::Tuple(tuple) => {
                            let ty = pat_type.ty.as_ref();
                            match ty {
                                syn::Type::Tuple(tuple_ty) => {
                                    for (pat, ty) in tuple.elems.iter().zip(tuple_ty.elems.iter()) {
                                        rtns.push(syn::Pat::Type(syn::PatType {
                                            attrs: vec![],
                                            pat: Box::new(pat.clone()),
                                            colon_token: syn::Token![:](pat.span()),
                                            ty: Box::new(ty.clone()),
                                        }));
                                    }
                                }
                                _ => {
                                    return Err(Error::new(let_stmt.span(), "expected tuple type"))
                                }
                            }
                        }
                        _ => return Err(Error::new(let_stmt.span(), "expected let statement")),
                    },
                    _ => return Err(Error::new(let_stmt.span(), "expected let statement")),
                }
                (wf_name, args, rtns)
            }
            _ => return Err(Error::new(let_stmt.span(), "expected let statement")),
        }
    };
    let wf_name = wf_name.to_string();
    for_block.body.stmts = vec![
        parse_quote!(let id = donburako::operator::ExecutorId::default();),
        parse_quote!(let (tx, rx) = tokio::sync::oneshot::channel();),
        parse_quote!(op.start_workflow(id, wf_id, Some(tx)).await;),
        parse_quote!(exec_ids.push((id, rx));),
        parse_quote!(store!{id | start => #(#args),*};),
    ];
    Ok(quote! {
        let wf_id = donburako::workflow::WorkflowId::new(#wf_name);
        #init_expr;
        let mut exec_ids = Vec::new();
        let (start, end) = op.get_start_end_edges(&wf_id);
        #for_block
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_workflow_impl_rec() {
        let input = quote! {
            let mut result = None;
            for _ in [()] {
                let rec: i32 = sum(n);
                result = Some(rec);
                if result.is_some() {
                    break;
                }
            }
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("sum");
            let mut result = None;
            let mut exec_ids = Vec::new();
            let (start, end) = op.get_start_end_edges(&wf_id);

            for _ in [()] {
                let id = donburako::operator::ExecutorId::default();
                let (tx, rx) = tokio::sync::oneshot::channel();
                op.start_workflow(id, wf_id, Some(tx)).await;
                exec_ids.push((id, rx));
                store!{
                    id | start
                        => n
                }
            }

            let mut flag = false;
            for (id, rx) in exec_ids {
                if flag {
                    op.finish_workflow_by_execute_id(id).await;
                    continue;
                }
                rx.await.unwrap();
                take!{
                    id | end
                        => rec: i32
                }
                result = Some(rec);
                if result.is_some() {
                    flag = true;
                }
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_impl_map() {
        let input = quote! {
            let mut result = Vec::new();
            for item in list {
                let (res, f): (i32, bool) = func_map(item);
                result.push(res);
            }
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("func_map");
            let mut result = Vec::new();
            let mut exec_ids = Vec::new();
            let (start, end) = op.get_start_end_edges(&wf_id);
            for item in list {
                let id = donburako::operator::ExecutorId::default();
                let (tx, rx) = tokio::sync::oneshot::channel();
                op.start_workflow(id, wf_id, Some(tx)).await;
                exec_ids.push((id, rx));
                store!{
                    id | start
                        => item
                }
            }

            let mut flag = false;
            for (id, rx) in exec_ids {
                if flag {
                    op.finish_workflow_by_execute_id(id).await;
                    continue;
                }
                rx.await.unwrap();
                take!{
                    id | end
                        => res: i32
                        => f: bool
                }
                result.push(res);
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_impl_filter() {
        let input = quote! {
            let mut result = Vec::new();
            for item in list {
                let res: Option<i32> = func_map(item);
                if let Some(res) = res {
                    result.push(res);
                }
            }
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("func_map");
            let mut result = Vec::new();
            let mut exec_ids = Vec::new();
            let (start, end) = op.get_start_end_edges(&wf_id);
            for item in list {
                let id = donburako::operator::ExecutorId::default();
                let (tx, rx) = tokio::sync::oneshot::channel();
                op.start_workflow(id, wf_id, Some(tx)).await;
                exec_ids.push((id, rx));
                store!{
                    id | start
                        => item
                }
            }

            let mut flag = false;
            for (id, rx) in exec_ids {
                if flag {
                    op.finish_workflow_by_execute_id(id).await;
                    continue;
                }
                rx.await.unwrap();
                take!{
                    id | end
                        => res: Option<i32>
                }
                if let Some(res) = res {
                    result.push(res);
                }
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_impl_take() {
        let input = quote! {
            let mut result = Vec::new();
            for (item1, item2) in list {
                let res: i32 = func_map(item1, item2);
                result.push(res);
                if result.len() == 3 {
                    break;
                }
            }
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("func_map");
            let mut result = Vec::new();
            let mut exec_ids = Vec::new();
            let (start, end) = op.get_start_end_edges(&wf_id);
            for (item1, item2) in list {
                let id = donburako::operator::ExecutorId::default();
                let (tx, rx) = tokio::sync::oneshot::channel();
                op.start_workflow(id, wf_id, Some(tx)).await;
                exec_ids.push((id, rx));
                store!{
                    id | start
                        => item1
                        => item2
                }
            }

            let mut flag = false;
            for (id, rx) in exec_ids {
                if flag {
                    op.finish_workflow_by_execute_id(id).await;
                    continue;
                }
                rx.await.unwrap();
                take!{
                    id | end
                        => res: i32
                }
                result.push(res);
                if result.len() == 3 {
                    flag = true;
                }
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_workflow_impl_fold() {
        let input = quote! {
            let mut result = 0;
            for item in list {
                let res: Option<i32> = func_map(item);
                if let Some(res) = res {
                    result += res;
                }
                if result.len() == 3 {
                    break;
                }
            }
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("func_map");
            let mut result = 0;
            let mut exec_ids = Vec::new();
            let (start, end) = op.get_start_end_edges(&wf_id);
            for item in list {
                let id = donburako::operator::ExecutorId::default();
                let (tx, rx) = tokio::sync::oneshot::channel();
                op.start_workflow(id, wf_id, Some(tx)).await;
                exec_ids.push((id, rx));
                store!{
                    id | start
                        => item
                }
            }

            let mut flag = false;
            for (id, rx) in exec_ids {
                if flag {
                    op.finish_workflow_by_execute_id(id).await;
                    continue;
                }
                rx.await.unwrap();
                take!{
                    id | end
                        => res: Option<i32>
                }
                if let Some(res) = res {
                    result += res;
                }
                if result.len() == 3 {
                    flag = true;
                }
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
