//! Donburako Macro
//!
//! Donburako を扱う上で便利なマクロを提供する。

#![warn(missing_docs, rustdoc::missing_crate_level_docs, unused_results)]

mod input;

use crate::input::input_impl;
use proc_macro::TokenStream;

/// 入力をパースするマクロ
///
/// ユーザー定義関数に登録する関数の入力を行うコードを生成する。
#[proc_macro]
pub fn input(tokens: TokenStream) -> TokenStream {
    input_impl(tokens.into()).into()
}
