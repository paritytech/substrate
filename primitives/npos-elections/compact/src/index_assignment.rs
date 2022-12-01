// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Code generation for getting the compact representation from the `IndexAssignment` type.

use crate::field_name_for;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

pub(crate) fn from_impl(count: usize) -> TokenStream2 {
	let from_impl_single = {
		let name = field_name_for(1);
		quote!(1 => compact.#name.push(
			(
				*who,
				distribution[0].0,
			)
		),)
	};

	let from_impl_double = {
		let name = field_name_for(2);
		quote!(2 => compact.#name.push(
			(
				*who,
				(
					distribution[0].0,
					distribution[0].1,
				),
				distribution[1].0,
			)
		),)
	};

	let from_impl_rest = (3..=count)
		.map(|c| {
			let inner = (0..c - 1)
				.map(|i| quote!((distribution[#i].0, distribution[#i].1),))
				.collect::<TokenStream2>();

			let field_name = field_name_for(c);
			let last_index = c - 1;
			let last = quote!(distribution[#last_index].0);

			quote!(
				#c => compact.#field_name.push(
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
		#from_impl_double
		#from_impl_rest
	)
}
