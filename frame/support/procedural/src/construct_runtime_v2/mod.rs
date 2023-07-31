// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use proc_macro::TokenStream;
pub use parse::Def;

mod parse;
mod expand;

use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;

pub fn construct_runtime(
    attrs: TokenStream,
	item: TokenStream,
) -> TokenStream {
    // let item = syn::parse_macro_input!(item as syn::ItemMod);
	let item: syn::ItemMod = syn::parse(item).unwrap();
	let input_main: TokenStream2 = item.to_token_stream().into();
	println!("input_main: {}", input_main);
    match parse::Def::try_from(item) {
		Ok(def) => expand::expand(def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
