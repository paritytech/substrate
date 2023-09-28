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

mod call;
mod view;

use crate::interface::definition::parse::Def;
use quote::ToTokens;

pub fn expand(mut def: Def) -> proc_macro2::TokenStream {
	let calls = call::expand(&def);
	let views = view::expand(&def);

	// TODO (needs to be parsed first)
	//  * Expand error
	//  * Expand event

	let new_items = quote::quote!(
		#calls
		#views
	);

	def.item
		.content
		.as_mut()
		.expect("This is checked by parsing")
		.1
		.push(syn::Item::Verbatim(new_items));

	def.item.into_token_stream()
}
