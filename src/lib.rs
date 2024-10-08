//! Donburako Macro
//!
//! Donburako を扱う上で便利なマクロを提供する。

#![warn(missing_docs, rustdoc::missing_crate_level_docs, unused_results)]

mod branch;
mod input;
mod output;

use crate::branch::branch_impl;
use crate::input::input_impl;
use crate::output::output_impl;
use proc_macro::TokenStream;

/// 入力をパースするマクロ
///
/// ユーザー定義関数に登録する関数の入力を行うコードを生成する。
#[proc_macro]
pub fn input(tokens: TokenStream) -> TokenStream {
    input_impl(tokens.into()).into()
}

/// 出力をパースするマクロ
///
/// ユーザー定義関数に登録する関数の出力を行うコードを生成する。
#[proc_macro]
pub fn output(tokens: TokenStream) -> TokenStream {
    output_impl(tokens.into()).into()
}

/// 条件分岐を行うマクロ
///
/// 条件分岐を行うコードを生成する。
#[proc_macro]
pub fn branch(tokens: TokenStream) -> TokenStream {
    branch_impl(tokens.into()).into()
}
