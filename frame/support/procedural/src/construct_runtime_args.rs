// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Implementation of macro `construct_runtime_args`.

mod keyword {
	syn::custom_keyword!(unique_id);
}

pub fn decl_construct_runtime_args(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	use frame_support_procedural_tools::generate_crate_access;

	let def = syn::parse_macro_input!(input as DeclArgsDef);
	let args = &def.args;

	// frame-support is made available by construct_runtime_preprocess
	let hidden_crate_name = "construct_runtime_preprocess";
	let scrate = generate_crate_access(&hidden_crate_name, "frame-support");

	let hidden_macro_name = syn::Ident::new(
		&format!("__hidden_unique_construct_runtime_args_{}", def.unique_id),
		proc_macro2::Span::call_site(),
	);

	quote::quote!(
		/// This can be internally called by `construct_runtime` to builds the pallet args.
		#[macro_export]
		#[doc(hidden)]
		macro_rules! #hidden_macro_name {
			( { $( $pattern:tt )* } $( $t:tt )* ) => {
				#scrate::expand_after! {
					{ $( $pattern )* }
					{ ::{ #args } }
					$( $t )*
				}
			}
		}
		#[doc(inline)]
		pub use #hidden_macro_name as construct_runtime_args;
	).into()
}

struct DeclArgsDef {
	unique_id: String,
	args: proc_macro2::TokenStream,
}

impl syn::parse::Parse for DeclArgsDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let unique_id = if input.peek(syn::Token![#]) {
			input.parse::<syn::Token![#]>()?;
			let content;
			syn::bracketed!(content in input);
			content.parse::<keyword::unique_id>()?;
			content.parse::<syn::Token![=]>()?;
			format!("{}", content.parse::<syn::Ident>()?)
		} else {
			"default_unique_id".into()
		};

		let args = input.parse()?;

		Ok(Self { unique_id, args })
	}
}
