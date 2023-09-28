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

use quote::ToTokens;

pub fn expand(mut def: super::parse::Def) -> proc_macro2::TokenStream {
	let indices = def.variants.iter().map(|var| var.index).collect::<Vec<_>>();
	let name = def.variants.iter().map(|var| var.name.clone()).collect::<Vec<_>>();
	let inner_types = def.variants.iter().map(|var| var.inner.clone()).collect::<Vec<_>>();
	let frame_support = def.frame_support;
	let sp_core = def.sp_core;
	let enum_name = def.item.ident.clone();

	def.item
		.variants
		.iter_mut()
		.zip(indices)
		.for_each(|(var, index)| var.attrs.push(syn::parse_quote!(#[codec(index = #index)])));

	def.item.attrs.push(
		syn::parse_quote!(#[derive(#frame_support::codec::Decode, #frame_support::codec::Encode, Clone, PartialEq, Eq)]),
	);

	let impl_item = quote::quote_spanned!(def.span =>
		impl #frame_support::interface::View for #enum_name {
			fn view(self) -> #frame_support::interface::ViewResult<Vec<u8>> {
				todo!()
			}
		}

		// Evaluate if the given index actually matches the standard defined index and trigger
		// a warning otherwise.
		const _: () = {

		};
	);

	let enum_item = def.item.into_token_stream();

	quote::quote!(
		#enum_item

		#impl_item
	)
}

/*
#[frame_support::call_entry]
pub enum CallInterface<Runtime> {
	#[call_entry::index(20)]
	Pip20(pip20::Call<Runtime>),
}

impl<Runtime> GetDispatchInfo for CallInterface<Runtime>{
}

impl<Runtime> Call for CallInterface<Runtime>{
}

impl<Runtime> GetCallMetadata for CallInterface<Runtime>{
}
 */
