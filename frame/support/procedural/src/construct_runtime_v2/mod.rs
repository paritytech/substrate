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
use proc_macro2::TokenStream as TokenStream2;
use frame_support_procedural_tools::{
	generate_crate_access, generate_crate_access_2018, generate_hidden_includes,
};

pub(crate) mod parse;
mod expand;

pub fn construct_runtime(
    attrs: TokenStream,
	input: TokenStream,
) -> TokenStream {
	let input_copy = input.clone();
    let item = syn::parse_macro_input!(input as syn::ItemMod);
    match parse::Def::try_from(item) {
		Ok(def) => {
			let exp = construct_runtime_intermediary_expansion(input_copy.into(), def).unwrap();
			println!("expansion: {}", exp);
			// expand::expand(def).into()
			quote::quote!(
				
			).into()
		},
		Err(e) => e.to_compile_error().into(),
	}
}

fn construct_runtime_intermediary_expansion(
	input: TokenStream2,
	definition: parse::Def,
) -> syn::Result<TokenStream2> {
	let frame_support = generate_crate_access_2018("frame-support")?;
	let mut expansion = quote::quote!(
		#[frame_support::construct_runtime_v2]
		#input
	);
	for pallet in definition.pallets.pallets.iter().filter(|pallet| pallet.pallet_parts.is_none()) {
		let pallet_path = &pallet.path;
		let pallet_name = &pallet.name;
		let pallet_index: &i32 = &pallet.index.unwrap().into(); //Todo
		let pallet_instance = pallet.instance.as_ref().map(|instance| quote::quote!(::<#instance>));
		expansion = quote::quote!(
			#frame_support::tt_call! {
				macro = [{ #pallet_path:: }]
				frame_support = [{ #frame_support }]
				~~> #frame_support::match_and_insert! {
					target = [{ #expansion }]
					pattern = [{ #pallet_name = #pallet_index, #pallet_path }]
				}
			}
		);
	}

	Ok(expansion)
}