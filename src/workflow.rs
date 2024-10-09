use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::{Error, Result};

pub fn workflow_impl(tokens: TokenStream) -> TokenStream {
    workflow_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn workflow_parse(input: ParseStream) -> Result<TokenStream> {
    let id = input.parse::<syn::LitStr>()?;
    Ok(quote! {
        let wf_id = donburako::workflow::WorkflowId::new(#id);
        let (start, end) = op.get_start_end_edges(&wf_id);
        let id = donburako::operator::ExecutorId::default();
        let (tx, rx) = tokio::sync::oneshot::channel();
        op.start_workflow(id, wf_id, Some(tx)).await;
        let mut cons = op.get_container(self_.inputs(), exec_id).await;
        for (i, edge) in start.iter().enumerate() {
            let con = cons.pop_front().unwrap();
            op.add_container(edge.clone(), id, con).await.unwrap();
        }
        rx.await.unwrap();
        let mut cons = op.get_container(end, id).await;
        for (i, edge) in end.iter().enumerate() {
            let con = cons.pop_front().unwrap();
            op.add_container(self_.outputs()[i].clone(), exec_id, con)
                .await
                .unwrap();
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_workflow_impl() {
        let input = quote! {
            "sum"
        };
        let result = workflow_impl(input).to_string();
        let expected = quote! {
            let wf_id = donburako::workflow::WorkflowId::new("sum");
            let (start, end) = op.get_start_end_edges(&wf_id);
            let id = donburako::operator::ExecutorId::default();
            let (tx, rx) = tokio::sync::oneshot::channel();
            op.start_workflow(id, wf_id, Some(tx)).await;
            let mut cons = op.get_container(self_.inputs(), exec_id).await;
            for (i, edge) in start.iter().enumerate() {
                let con = cons.pop_front().unwrap();
                op.add_container(edge.clone(), id, con).await.unwrap();
            }
            rx.await.unwrap();
            let mut cons = op.get_container(end, id).await;
            for (i, edge) in end.iter().enumerate() {
                let con = cons.pop_front().unwrap();
                op.add_container(self_.outputs()[i].clone(), exec_id, con)
                    .await
                    .unwrap();
        }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
