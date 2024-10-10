use convert_case::{Case, Casing};
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{parse_quote, Error, Result};

fn convert_return_to_output(stmts: &mut Vec<syn::Stmt>, output_count: usize) -> Result<()> {
    for stmt in stmts {
        if let syn::Stmt::Expr(syn::Expr::Return(ret), _) = stmt {
            if let Some(expr) = ret.expr.as_mut() {
                match expr.as_mut() {
                    syn::Expr::Path(path) => {
                        if path.path.segments.len() != 1 {
                            return Err(Error::new(path.span(), "expected one path segment"));
                        }
                        if let Some(ident) = path.path.get_ident() {
                            *stmt = parse_quote! {
                                output!(#ident);
                            }
                        }
                    }
                    syn::Expr::Tuple(tuple) => {
                        if tuple.elems.len() != output_count {
                            return Err(Error::new(
                                tuple.span(),
                                format!("return statement must have {} expressions", output_count),
                            ));
                        }
                        *stmt = parse_quote! {
                            output!#tuple;
                        }
                    }
                    _ => return Err(Error::new(expr.span(), "return statement must be a tuple")),
                }
            } else {
                return Err(Error::new(
                    Span::call_site(),
                    "return statement must have an expression",
                ));
            }
        }
    }
    Ok(())
}

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
    let func_args = {
        let mut args = vec![];
        for arg in func.sig.inputs.iter() {
            if let syn::FnArg::Typed(pat) = arg {
                args.push(pat.clone());
            }
        }
        args
    };
    let func_rtn_types = {
        let mut rtn_types = vec![];
        if let syn::ReturnType::Type(_, ty) = &func.sig.output {
            match &**ty {
                syn::Type::Path(path) => {
                    rtn_types.push(path.clone());
                }
                syn::Type::Tuple(tuple) => {
                    for elem in tuple.elems.iter() {
                        if let syn::Type::Path(path) = elem {
                            if let Some(ident) = path.path.get_ident() {
                                rtn_types.push(syn::TypePath {
                                    qself: None,
                                    path: syn::Path::from(ident.clone()),
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        rtn_types
    };
    let mut func_stmts = func.block.stmts.clone();
    // 再帰的に return を探して、それを output! に変換する(func_rtn_types との数のチェックを行う)
    convert_return_to_output(&mut func_stmts, func_rtn_types.len())?;
    let func_name_str = func_name.to_string();
    Ok(quote! {
        struct #struct_name {
            outputs: Vec<Arc<Edge>>,
            func: Box<dyn for<'a> Fn(
                &'a Node,
                &'a donburako::operator::Operator,
                donburako::operator::ExecutorId,
            ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
            + Send
            + Sync>,
            is_blocking: bool,
            choice: Choice,
            name: &'static str,
        }
        impl donburako::node::NodeBuilder for #struct_name {
            fn new() -> Self {
                #struct_name {
                    outputs: vec![
                        #(
                            Arc::new(Edge::new::<#func_rtn_types>())
                        ),*
                    ],
                    func: node_func! {
                        input!(#(#func_args),*);
                        #(#func_stmts)*
                    },
                    is_blocking: false,
                    choice: Choice::All,
                    name: #func_name_str,
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
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_node_builder_impl1() {
        let input = quote! {
            fn divide(n: i32) -> (i32, i32) {
                println!("divide: {}", n);
                return (n, n);
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct DivideBuilder {
                outputs: Vec<Arc<Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a Node,
                    &'a donburako::operator::Operator,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for DivideBuilder {
                fn new() -> Self {
                    DivideBuilder {
                        outputs: vec![Arc::new(Edge::new::<i32>()), Arc::new(Edge::new::<i32>())],
                        func: node_func! {
                            input!(n: i32);
                            println!("divide: {}", n);
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

    #[test]
    fn test_node_builder_impl2() {
        let input = quote! {
            fn is_even(n: i32) -> bool {
                let result = n % 2 == 0;
                return result;
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct IsEvenBuilder {
                outputs: Vec<Arc<Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a Node,
                    &'a donburako::operator::Operator,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for IsEvenBuilder {
                fn new() -> Self {
                    IsEvenBuilder {
                        outputs: vec![Arc::new(Edge::new::<bool>())],
                        func: node_func! {
                            input!(n: i32);
                            let result = n % 2 == 0;
                            output!(result);
                        },
                        is_blocking: false,
                        choice: Choice::All,
                        name: "is_even",
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
