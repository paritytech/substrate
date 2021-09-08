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

//! Code generation for the ratio assignment type' encode/decode impl.

use crate::vote_field;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

pub(crate) fn codec_impl(
	ident: syn::Ident,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	count: usize,
) -> TokenStream2 {
	let encode = encode_impl(ident.clone(), count);
	let decode = decode_impl(ident, voter_type, target_type, weight_type, count);

	quote! {
		#encode
		#decode
	}
}

fn decode_impl(
	ident: syn::Ident,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	count: usize,
) -> TokenStream2 {
	let decode_impl_single = {
		let name = vote_field(1);
		quote! {
			let #name =
			<
				_npos::sp_std::prelude::Vec<(_npos::codec::Compact<#voter_type>, _npos::codec::Compact<#target_type>)>
				as
				_npos::codec::Decode
			>::decode(value)?;
			let #name = #name
				.into_iter()
				.map(|(v, t)| (v.0, t.0))
				.collect::<_npos::sp_std::prelude::Vec<_>>();
		}
	};

	let decode_impl_rest = (2..=count)
		.map(|c| {
			let name = vote_field(c);

			let inner_impl = (0..c - 1)
				.map(|i| quote! { ( (inner[#i].0).0, (inner[#i].1).0 ), })
				.collect::<TokenStream2>();

			quote! {
				let #name =
				<
					_npos::sp_std::prelude::Vec<(
						_npos::codec::Compact<#voter_type>,
						[(_npos::codec::Compact<#target_type>, _npos::codec::Compact<#weight_type>); #c-1],
						_npos::codec::Compact<#target_type>,
					)>
					as _npos::codec::Decode
				>::decode(value)?;
				let #name = #name
					.into_iter()
					.map(|(v, inner, t_last)| (
						v.0,
						[ #inner_impl ],
						t_last.0,
					))
					.collect::<_npos::sp_std::prelude::Vec<_>>();
			}
		})
		.collect::<TokenStream2>();

	let all_field_names = (1..=count)
		.map(|c| {
			let name = vote_field(c);
			quote! { #name, }
		})
		.collect::<TokenStream2>();

	quote!(
		impl _npos::codec::Decode for #ident {
			fn decode<I: _npos::codec::Input>(value: &mut I) -> Result<Self, _npos::codec::Error> {
				#decode_impl_single
				#decode_impl_rest

				// The above code generates variables with the decoded value with the same name as
				// filed names of the struct, i.e. `let votes4 = decode_value_of_votes4`. All we
				// have to do is collect them into the main struct now.
				Ok(#ident { #all_field_names })
			}
		}
	)
}

// General attitude is that we will convert inner values to `Compact` and then use the normal
// `Encode` implementation.
fn encode_impl(ident: syn::Ident, count: usize) -> TokenStream2 {
	let encode_impl_single = {
		let name = vote_field(1);
		quote! {
			let #name = self.#name
				.iter()
				.map(|(v, t)| (
					_npos::codec::Compact(v.clone()),
					_npos::codec::Compact(t.clone()),
				))
				.collect::<_npos::sp_std::prelude::Vec<_>>();
			#name.encode_to(&mut r);
		}
	};

	let encode_impl_rest = (2..=count)
		.map(|c| {
			let name = vote_field(c);

			// we use the knowledge of the length to avoid copy_from_slice.
			let inners_solution_array = (0..c - 1)
				.map(|i| {
					quote! {(
						_npos::codec::Compact(inner[#i].0.clone()),
						_npos::codec::Compact(inner[#i].1.clone()),
					),}
				})
				.collect::<TokenStream2>();

			quote! {
				let #name = self.#name
					.iter()
					.map(|(v, inner, t_last)| (
						_npos::codec::Compact(v.clone()),
						[ #inners_solution_array ],
						_npos::codec::Compact(t_last.clone()),
					))
					.collect::<_npos::sp_std::prelude::Vec<_>>();
				#name.encode_to(&mut r);
			}
		})
		.collect::<TokenStream2>();

	quote!(
		impl _npos::codec::Encode for #ident {
			fn encode(&self) -> _npos::sp_std::prelude::Vec<u8> {
				let mut r = vec![];
				#encode_impl_single
				#encode_impl_rest
				r
			}
		}
	)
}
