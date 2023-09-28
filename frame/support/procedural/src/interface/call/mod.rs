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

use syn::spanned::Spanned;

mod expand;
mod parse;

pub fn call_entry(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let runtime = if attr.is_empty() {
		let msg = "Invalid interface macro call: unexpected attribute. Macro call must contain \
				runtime identifier, such as `#[frame_support::call_entry($ident)]` or `#[call_entry($ident)]`.";
		let span = proc_macro2::TokenStream::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into();
	} else {
		syn::parse_macro_input!(attr as syn::Ident)
	};

	let item = syn::parse_macro_input!(item as syn::ItemEnum);
	match parse::Def::try_from(item, runtime) {
		Ok(def) => expand::expand(def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
