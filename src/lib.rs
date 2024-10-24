//! Donburako Macro
//!
//! Donburako を扱う上で便利なマクロを提供する。

#![warn(missing_docs, rustdoc::missing_crate_level_docs, unused_results)]

mod branch;
mod data;
mod ioput;
mod node_builder;
mod node_func;
mod select;
mod workflow;
mod workflow_builder;

use crate::branch::branch_builder_impl;
use crate::data::{store_impl, take_impl};
use crate::ioput::{input_impl, output_impl};
use crate::node_builder::node_builder_impl;
use crate::node_func::node_func_impl;
use crate::select::select_builder_impl;
use crate::workflow::workflow_impl;
use crate::workflow_builder::workflow_builder_impl;
use proc_macro::TokenStream;

/// 条件分岐を行うノードのビルダーを生成するマクロ
///
/// 条件分岐を行うノードのビルダーを生成するコードを生成する。
#[proc_macro]
pub fn branch_builder(tokens: TokenStream) -> TokenStream {
    branch_builder_impl(tokens.into()).into()
}

/// 選択を行うノードのビルダーを生成するマクロ
///
/// 選択を行うノードのビルダーを生成するコードを生成する。
#[proc_macro]
pub fn select_builder(tokens: TokenStream) -> TokenStream {
    select_builder_impl(tokens.into()).into()
}

/// ノードの関数を定義するマクロ
///
/// ノードの関数を定義するコードを生成する。
#[proc_macro]
pub fn node_func(tokens: TokenStream) -> TokenStream {
    node_func_impl(tokens.into()).into()
}

/// データを取り出すマクロ
///
/// データを取り出すコードを生成する。
#[proc_macro]
pub fn take(tokens: TokenStream) -> TokenStream {
    take_impl(tokens.into()).into()
}

/// データを格納するマクロ
///
/// データを格納するコードを生成する。
#[proc_macro]
pub fn store(tokens: TokenStream) -> TokenStream {
    store_impl(tokens.into()).into()
}

/// 入力を取り出すマクロ
///
/// 標準的な入力を取り出すコードを生成する。
#[proc_macro]
pub fn input(tokens: TokenStream) -> TokenStream {
    input_impl(tokens.into()).into()
}

/// 出力を格納するマクロ
///
/// 標準的な出力を格納するコードを生成する。
#[proc_macro]
pub fn output(tokens: TokenStream) -> TokenStream {
    output_impl(tokens.into()).into()
}

/// ワークフローの呼び出しを行うマクロ
///
/// ワークフローの呼び出しを行うコードを生成する。
#[proc_macro]
pub fn workflow(tokens: TokenStream) -> TokenStream {
    workflow_impl(tokens.into()).into()
}

/// ノードビルダーを生成するマクロ
///
/// ノードビルダーを生成するコードを生成する。
#[proc_macro_attribute]
pub fn node_builder(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    node_builder_impl(attrs.into(), tokens.into()).into()
}

/// ワークフロービルダーを生成するマクロ
///
/// ワークフロービルダーを生成するコードを生成する。
#[proc_macro_attribute]
pub fn workflow_builder(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    workflow_builder_impl(attrs.into(), tokens.into()).into()
}
