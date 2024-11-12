use convert_case::{Case, Casing};
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::visit_mut::{visit_expr_mut, visit_expr_tuple_mut, VisitMut};
use syn::{parse_quote, Error, Result};

struct AwaitFinder<'a> {
    found: bool,
    rtn_types: &'a Vec<syn::TypePath>,
    let_stmts: Option<(TokenStream, syn::Stmt)>,
    in_return: bool,
    error: Option<Error>,
}
impl<'a> AwaitFinder<'a> {
    fn new(rtn_types: &'a Vec<syn::TypePath>) -> Self {
        AwaitFinder {
            found: false,
            rtn_types,
            let_stmts: None,
            in_return: false,
            error: None,
        }
    }
}
impl<'a> VisitMut for AwaitFinder<'a> {
    fn visit_expr_await_mut(&mut self, _: &mut syn::ExprAwait) {
        self.found = true;
    }

    fn visit_expr_tuple_mut(&mut self, expr_tuple: &mut syn::ExprTuple) {
        if !self.in_return {
            visit_expr_tuple_mut(self, expr_tuple);
            return;
        }
        if expr_tuple.elems.len() != self.rtn_types.len() {
            self.error = Some(Error::new(
                expr_tuple.span(),
                format!(
                    "return statement must have {} expressions",
                    self.rtn_types.len()
                ),
            ));
            return;
        }
        let vars = (0..(expr_tuple.elems.len()))
            .map(|i| syn::Ident::new(&format!("_r_{}", i), expr_tuple.span()));
        let elems = expr_tuple.elems.iter();
        let tys = self.rtn_types.iter();
        let vars_clone = vars.clone();
        let var_ts = quote! {(#(#vars),*)};
        self.let_stmts = Some((
            var_ts,
            parse_quote! {
                let (#(#vars_clone),*): (#(#tys),*) = (#(#elems),*);
            },
        ));
    }

    fn visit_expr_return_mut(&mut self, expr_return: &mut syn::ExprReturn) {
        if self.in_return {
            self.error = Some(Error::new(
                expr_return.span(),
                "return statement cannot be nested",
            ));
            return;
        }
        self.in_return = true;
        if let Some(expr) = expr_return.expr.as_mut() {
            self.visit_expr_mut(expr);
        }
        self.in_return = false;
    }

    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if self.in_return {
            if let syn::Expr::Tuple(_) = expr {
                visit_expr_mut(self, expr);
                return;
            }
            if self.rtn_types.len() != 1 {
                self.error = Some(Error::new(
                    expr.span(),
                    format!(
                        "return statement must have {} expressions",
                        self.rtn_types.len()
                    ),
                ));
                return;
            }
            let vars = syn::Ident::new("_r_0", expr.span());
            let ty = &self.rtn_types[0];
            let vars_clone = vars.clone();
            self.let_stmts = Some((
                quote!((#vars)),
                parse_quote! {
                    let #vars_clone: #ty = #expr;
                },
            ));
        } else {
            visit_expr_mut(self, expr);
            if let Some((vars, let_stmts)) = self.let_stmts.take() {
                *expr = syn::Expr::Block(syn::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: syn::Block {
                        brace_token: syn::token::Brace::default(),
                        stmts: vec![let_stmts, parse_quote!(donburako::macros::output!#vars;)],
                    },
                });
            }
        }
    }

    fn visit_macro_mut(&mut self, _macro: &mut syn::Macro) {
        if _macro.path.is_ident("workflow") {
            self.found = true;
        }
    }
}

pub fn node_builder_impl(_: TokenStream, tokens: TokenStream) -> TokenStream {
    node_builder_parse
        .parse2(tokens)
        .unwrap_or_else(Error::into_compile_error)
}

pub fn node_builder_parse(input: ParseStream) -> Result<TokenStream> {
    let mut func = input.parse::<syn::ItemFn>()?;
    let func_name = &func.sig.ident;
    let struct_name = syn::Ident::new(
        &format!("{}Builder", func_name.to_string().to_case(Case::Pascal)),
        func_name.span(),
    );
    let vis = &func.vis;
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
                            rtn_types.push(path.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        rtn_types
    };
    let mut finder = AwaitFinder::new(&func_rtn_types);
    finder.visit_block_mut(&mut func.block);
    if let Some(error) = finder.error {
        return Err(error);
    }
    let func_stmts = func.block.stmts.clone();
    // 再帰的に return を探して、それを donburako::macros::output! に変換する(func_rtn_types との数のチェックを行う)
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
            fn build(self, inputs: Vec<std::sync::Arc<donburako::edge::Edge>>, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                #if_expr else {
                    return Err(donburako::node::NodeError::EdgeTypeMismatch);
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
        )
    } else {
        parse_quote! {
            fn build(self, inputs: Vec<std::sync::Arc<donburako::edge::Edge>>, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
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
    };
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
                stmts: vec![parse_quote!(return donburako::Faker.fake();)],
            })
        } else {
            let mut fakes: Vec<syn::Expr> = Vec::with_capacity(func_rtn_types.len());
            for _ in 0..func_rtn_types.len() {
                fakes.push(parse_quote!(donburako::Faker.fake()));
            }
            fake_func.block = Box::new(syn::Block {
                brace_token: func.block.brace_token,
                stmts: vec![parse_quote!(return (#(#fakes),*);)],
            })
        }
        fake_func
    };
    Ok(quote! {
        #vis struct #struct_name {
            outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
            func: Box<dyn for<'a> Fn(
                &'a donburako::node::Node,
                std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                donburako::operator::ExecutorId,
            ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
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
                            std::sync::Arc::new(donburako::edge::Edge::new::<#func_rtn_types>())
                        ),*
                    ],
                    func: donburako::macros::node_func! {
                        donburako::macros::input!(#(#func_args),*);
                        #(#func_stmts)*
                    },
                    is_blocking: #is_blocking,
                    choice: donburako::node::Choice::All,
                    name: #func_name_str,
                }
            }
            fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
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
                outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a donburako::node::Node,
                    std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for DivideBuilder {
                fn new() -> Self {
                    DivideBuilder {
                        outputs: vec![std::sync::Arc::new(donburako::edge::Edge::new::<i32>()), std::sync::Arc::new(donburako::edge::Edge::new::<i32>())],
                        func: donburako::macros::node_func! {
                            donburako::macros::input!(n: i32);
                            println!("divide: {}", n);
                            sleep(Duration::from_secs(1)).await;
                            {
                                let (_r_0, _r_1): (i32, i32) = (n, n);
                                donburako::macros::output!(_r_0, _r_1);
                            };
                        },
                        is_blocking: false,
                        choice: donburako::node::Choice::All,
                        name: "divide",
                    }
                }
                fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< std::sync::Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
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
            async fn divide(_: i32) -> (i32, i32) {
                return (donburako::Faker.fake(), donburako::Faker.fake());
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_node_builder_impl2() {
        let input = quote! {
            pub fn is_even(n: i32) -> bool {
                let result = n % 2 == 0;
                return result;
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            pub struct IsEvenBuilder {
                outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a donburako::node::Node,
                    std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for IsEvenBuilder {
                fn new() -> Self {
                    IsEvenBuilder {
                        outputs: vec![std::sync::Arc::new(donburako::edge::Edge::new::<bool>())],
                        func: donburako::macros::node_func! {
                            donburako::macros::input!(n: i32);
                            let result = n % 2 == 0;
                            {
                                let _r_0: bool = result;
                                donburako::macros::output!(_r_0);
                            };
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "is_even",
                    }
                }
                fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< std::sync::Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
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
            pub fn is_even(_: i32) -> bool {
                return donburako::Faker.fake();
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
                outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a donburako::node::Node,
                    std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for DoubleBuilder {
                fn new() -> Self {
                    DoubleBuilder {
                        outputs: vec![std::sync::Arc::new(donburako::edge::Edge::new::< Option<i32> >())],
                        func: donburako::macros::node_func! {
                            donburako::macros::input!(n: i32);
                            {
                                let _r_0: Option<i32> = Some(n * 2);
                                donburako::macros::output!(_r_0);
                            };
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "double",
                    }
                }
                fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< std::sync::Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<i32>() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
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
            fn double(_: i32) -> Option<i32> {
                return donburako::Faker.fake();
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
                outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a donburako::node::Node,
                    std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for AddBuilder {
                fn new() -> Self {
                    AddBuilder {
                        outputs: vec![std::sync::Arc::new(donburako::edge::Edge::new::<i32>())],
                        func: donburako::macros::node_func! {
                            donburako::macros::input!(a: i32, b: i32);
                            {
                                let _r_0: i32 = a + b;
                                donburako::macros::output!(_r_0);
                            };
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "add",
                    }
                }
                fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< std::sync::Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
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
            fn add(_: i32, _: i32) -> i32 {
                return donburako::Faker.fake();
            }
        }
        .to_string();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_node_builder_impl5() {
        let input = quote! {
            fn divide_strio(port: Arc<i32>) -> (Arc<i32>, Arc<i32>) {
                let port_clone = port.clone();
                return (port, port_clone);
            }
        };
        let result = node_builder_impl(quote! {}, input).to_string();
        let expected = quote! {
            struct DivideStrioBuilder {
                outputs: Vec<std::sync::Arc<donburako::edge::Edge>>,
                func: Box<dyn for<'a> Fn(
                    &'a donburako::node::Node,
                    std::sync::Arc<tokio::sync::Mutex<donburako::operator::Operator>>,
                    donburako::operator::ExecutorId,
                ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), donburako::node::NodeError>> + Send + 'a>>
                + Send
                + Sync>,
                is_blocking: bool,
                choice: donburako::node::Choice,
                name: &'static str,
            }
            impl donburako::node::NodeBuilder for DivideStrioBuilder {
                fn new() -> Self {
                    DivideStrioBuilder {
                        outputs: vec![std::sync::Arc::new(donburako::edge::Edge::new::<Arc<i32> >()), std::sync::Arc::new(donburako::edge::Edge::new::<Arc<i32> >())],
                        func: donburako::macros::node_func! {
                            donburako::macros::input!(port: Arc<i32>);
                            let port_clone = port.clone();
                            {
                                let (_r_0, _r_1): (Arc<i32>, Arc<i32>) = (port, port_clone);
                                donburako::macros::output!(_r_0, _r_1);
                            };
                        },
                        is_blocking: true,
                        choice: donburako::node::Choice::All,
                        name: "divide_strio",
                    }
                }
                fn outputs(&self) -> &Vec<std::sync::Arc<donburako::edge::Edge>> {
                    &self.outputs
                }
                fn build(self, inputs: Vec< std::sync::Arc<donburako::edge::Edge> >, manage_cnt: usize) -> Result<std::sync::Arc<donburako::node::Node>, donburako::node::NodeError>{
                    if let Some(edge) = inputs.get(manage_cnt + 0usize) {
                        if !edge.check_type::<Arc<i32> >() {
                            return Err(donburako::node::NodeError::EdgeTypeMismatch);
                        }
                    } else {
                        return Err(donburako::node::NodeError::EdgeTypeMismatch);
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
            fn divide_strio(_: Arc<i32>) -> (Arc<i32>, Arc<i32>) {
                return (donburako::Faker.fake(), donburako::Faker.fake());
            }
        }.to_string();
        assert_eq!(result, expected);
    }
}
