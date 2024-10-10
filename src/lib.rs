//! Donburako Macro
//!
//! Donburako を扱う上で便利なマクロを提供する。

#![warn(missing_docs, rustdoc::missing_crate_level_docs, unused_results)]

mod branch;
mod data;
mod first;
mod node_func;
mod workflow;

use crate::branch::branch_impl;
use crate::data::{store_impl, take_impl};
use crate::first::first_impl;
use crate::node_func::node_func_impl;
use crate::workflow::workflow_impl;
use proc_macro::TokenStream;

/// 条件分岐を行うマクロ
///
/// 条件分岐を行うコードを生成する。
#[proc_macro]
pub fn branch(tokens: TokenStream) -> TokenStream {
    branch_impl(tokens.into()).into()
}

/// 最初の入力を取り出すマクロ
///
/// 最初の入力を取り出すコードを生成する。
#[proc_macro]
pub fn first(tokens: TokenStream) -> TokenStream {
    first_impl(tokens.into()).into()
}

/// ワークフローを実行するマクロ
///
/// ワークフローを実行するコードを生成する。
#[proc_macro]
pub fn workflow(tokens: TokenStream) -> TokenStream {
    workflow_impl(tokens.into()).into()
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
