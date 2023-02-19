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

//! Code generation for getting the solution representation from the `IndexAssignment` type.

use crate::vote_field;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

pub(crate) fn from_impl(struct_name: &syn::Ident, count: usize) -> TokenStream2 {
	let from_impl_single = {
		let name = vote_field(1);
		quote!(1 => #struct_name.#name.push(
			(
				*who,
				distribution[0].0,
			)
		),)
	};

	let from_impl_rest = (2..=count)
		.map(|c| {
			let inner = (0..c - 1)
				.map(|i| quote!((distribution[#i].0, distribution[#i].1),))
				.collect::<TokenStream2>();

			let field_name = vote_field(c);
			let last_index = c - 1;
			let last = quote!(distribution[#last_index].0);

			quote!(
				#c => #struct_name.#field_name.push(
					(
						*who,
						[#inner],
						#last,
					)
				),
			)
		})
		.collect::<TokenStream2>();

	quote!(
		#from_impl_single
		#from_impl_rest
	)
}
