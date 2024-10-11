use convert_case::{Case, Casing};
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::visit::{visit_expr, Visit};
use syn::{parse_quote, Error, Result};

fn convert_return_to_output(stmts: &mut Vec<syn::Stmt>, output_count: usize) -> Result<()> {
    for stmt in stmts {
        if let syn::Stmt::Expr(syn::Expr::Return(ret), _) = stmt {
            if let Some(expr) = ret.expr.as_mut() {
                match expr.as_mut() {
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
                    _ => {
                        if output_count != 1 {
                            return Err(Error::new(
                                expr.span(),
                                format!("return statement must have {} expressions", output_count),
                            ));
                        }
                        *stmt = parse_quote! {
                            output!(#expr);
                        }
                    }
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

#[derive(Default)]
struct AwaitFinder {
    found: bool,
}
impl<'ast> Visit<'ast> for AwaitFinder {
    fn visit_expr(&mut self, expr: &'ast syn::Expr) {
        if let syn::Expr::Await(_) = expr {
            self.found = true;
        }
        visit_expr(self, expr);
    }
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
    let (func_args, args_type) = {
        let mut args = vec![];
        let mut args_type = vec![];
        for arg in func.sig.inputs.iter() {
            if let syn::FnArg::Typed(pat) = arg {
                args.push(pat.clone());
                args_type.push(pat.ty.as_ref().clone());
            }
        }
        (args, args_type)
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
    let build_fn: syn::ImplItemFn = if !args_type.is_empty() {
        let ifs = args_type
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                parse_quote! {
                    if let Some(edge) = inputs.get(manage_cnt + #i) {
                        if !edge.check_type::<#ty>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    }
                }
            })
            .collect::<Vec<syn::ExprIf>>();
        let mut if_expr = ifs[0].clone();

        for if_block in ifs.iter().skip(1) {
            if_expr = parse_quote! {
                #if_expr else #if_block
            };
        }

        parse_quote!(
            fn build(self, inputs: Vec<Arc<donburako::edge::Edge>>, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                #if_expr else {
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
        )
    } else {
        parse_quote! {
            fn build(self, inputs: Vec<Arc<donburako::edge::Edge>>, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
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
    };
    let mut finder = AwaitFinder::default();
    finder.visit_block(&func.block);
    let is_blocking = !finder.found;
    // 中でマクロを使っていると、変数の整合性がとれないため、ダミーの関数でなければならない
    let fake_func = {
        let mut fake_func = func.clone();
        if is_blocking && fake_func.sig.asyncness.is_some() {
            return Err(Error::new(
                fake_func.sig.asyncness.span(),
                "blocking function cannot be async",
            ));
        } else if !is_blocking && fake_func.sig.asyncness.is_none() {
            return Err(Error::new(
                fake_func.sig.asyncness.span(),
                "non-blocking function must be async",
            ));
        }
        fake_func.sig.inputs = fake_func
            .sig
            .inputs
            .clone()
            .iter()
            .map(|arg| -> syn::FnArg {
                if let syn::FnArg::Typed(pat) = arg {
                    let ty = pat.ty.clone();
                    parse_quote!(_: #ty)
                } else {
                    parse_quote!()
                }
            })
            .collect();
        if func_rtn_types.len() == 1 {
            fake_func.block = Box::new(syn::Block {
                brace_token: func.block.brace_token,
                stmts: vec![parse_quote!(return fake::Faker.fake();)],
            })
        } else {
            let mut fakes: Vec<syn::Expr> = Vec::with_capacity(func_rtn_types.len());
            for _ in 0..func_rtn_types.len() {
                fakes.push(parse_quote!(fake::Faker.fake()));
            }
            fake_func.block = Box::new(syn::Block {
                brace_token: func.block.brace_token,
                stmts: vec![parse_quote!(return (#(#fakes),*);)],
            })
        }
        fake_func
    };
    Ok(quote! {
        struct #struct_name {
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
        impl donburako::node::NodeBuilder for #struct_name {
            fn new() -> Self {
                #struct_name {
                    outputs: vec![
                        #(
                            Arc::new(donburako::edge::Edge::new::<#func_rtn_types>())
                        ),*
                    ],
                    func: node_func! {
                        input!(#(#func_args),*);
                        #(#func_stmts)*
                    },
                    is_blocking: #is_blocking,
                    choice: donburako::node::Choice::All,
                    name: #func_name_str,
                }
            }
            fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                &self.outputs
            }
            #build_fn
        }
        #fake_func
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_node_builder_impl1() {
        let input = quote! {
            async fn divide(n: i32) -> (i32, i32) {
                println!("divide: {}", n);
                sleep(Duration::from_secs(1)).await;
                return (n, n);
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct DivideBuilder {
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
            impl donburako::node::NodeBuilder for DivideBuilder {
                fn new() -> Self {
                    DivideBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::<i32>()), Arc::new(donburako::edge::Edge::new::<i32>())],
                        func: node_func! {
                            input!(n: i32);
                            println!("divide: {}", n);
                            sleep(Duration::from_secs(1)).await;
                            output!(n, n);
                        },
                        is_blocking: false,
                        choice: donburako::node::Choice::All,
                        name: "divide",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
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
            async fn divide(_: i32) -> (i32, i32) {
                return (fake::Faker.fake(), fake::Faker.fake());
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
            impl donburako::node::NodeBuilder for IsEvenBuilder {
                fn new() -> Self {
                    IsEvenBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::<bool>())],
                        func: node_func! {
                            input!(n: i32);
                            let result = n % 2 == 0;
                            output!(result);
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "is_even",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
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
            fn is_even(_: i32) -> bool {
                return fake::Faker.fake();
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_node_builder_impl3() {
        let input = quote! {
            fn double(n: i32) -> Option<i32> {
                return Some(n * 2);
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct DoubleBuilder {
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
            impl donburako::node::NodeBuilder for DoubleBuilder {
                fn new() -> Self {
                    DoubleBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::< Option<i32> >())],
                        func: node_func! {
                            input!(n: i32);
                            output!(Some(n * 2));
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "double",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
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
            fn double(_: i32) -> Option<i32> {
                return fake::Faker.fake();
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_node_builder_impl4() {
        let input = quote! {
            fn add(a: i32, b: i32) -> i32 {
                return a + b;
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct AddBuilder {
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
            impl donburako::node::NodeBuilder for AddBuilder {
                fn new() -> Self {
                    AddBuilder {
                        outputs: vec![Arc::new(donburako::edge::Edge::new::<i32>())],
                        func: node_func! {
                            input!(a: i32, b: i32);
                            output!(a + b);
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "add",
                    }
                }
                fn outputs(&self) -> &Vec<Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else if let Some(edge) = inputs.get(manage_cnt + 1usize) {
                        if !edge.check_type::<i32>() {
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
            fn add(_: i32, _: i32) -> i32 {
                return fake::Faker.fake();
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }
}
