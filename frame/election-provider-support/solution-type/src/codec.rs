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

//! Code generation for the ratio assignment type' encode/decode/info impl.

use crate::vote_field;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

pub(crate) fn codec_and_info_impl(
	ident: syn::Ident,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	count: usize,
) -> TokenStream2 {
	let encode = encode_impl(&ident, count);
	let decode = decode_impl(&ident, &voter_type, &target_type, &weight_type, count);
	let scale_info = scale_info_impl(&ident, &voter_type, &target_type, &weight_type, count);

	quote! {
		#encode
		#decode
		#scale_info
	}
}

fn decode_impl(
	ident: &syn::Ident,
	voter_type: &syn::Type,
	target_type: &syn::Type,
	weight_type: &syn::Type,
	count: usize,
) -> TokenStream2 {
	let decode_impl_single = {
		let name = vote_field(1);
		quote! {
			let #name =
			<
				_feps::sp_std::prelude::Vec<(_feps::codec::Compact<#voter_type>, _feps::codec::Compact<#target_type>)>
				as
				_feps::codec::Decode
			>::decode(value)?;
			let #name = #name
				.into_iter()
				.map(|(v, t)| (v.0, t.0))
				.collect::<_feps::sp_std::prelude::Vec<_>>();
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
					_feps::sp_std::prelude::Vec<(
						_feps::codec::Compact<#voter_type>,
						[(_feps::codec::Compact<#target_type>, _feps::codec::Compact<#weight_type>); #c-1],
						_feps::codec::Compact<#target_type>,
					)>
					as _feps::codec::Decode
				>::decode(value)?;
				let #name = #name
					.into_iter()
					.map(|(v, inner, t_last)| (
						v.0,
						[ #inner_impl ],
						t_last.0,
					))
					.collect::<_feps::sp_std::prelude::Vec<_>>();
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
		impl _feps::codec::Decode for #ident {
			fn decode<I: _feps::codec::Input>(value: &mut I) -> Result<Self, _feps::codec::Error> {
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
fn encode_impl(ident: &syn::Ident, count: usize) -> TokenStream2 {
	let encode_impl_single = {
		let name = vote_field(1);
		quote! {
			let #name = self.#name
				.iter()
				.map(|(v, t)| (
					_feps::codec::Compact(v.clone()),
					_feps::codec::Compact(t.clone()),
				))
				.collect::<_feps::sp_std::prelude::Vec<_>>();
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
						_feps::codec::Compact(inner[#i].0.clone()),
						_feps::codec::Compact(inner[#i].1.clone()),
					),}
				})
				.collect::<TokenStream2>();

			quote! {
				let #name = self.#name
					.iter()
					.map(|(v, inner, t_last)| (
						_feps::codec::Compact(v.clone()),
						[ #inners_solution_array ],
						_feps::codec::Compact(t_last.clone()),
					))
					.collect::<_feps::sp_std::prelude::Vec<_>>();
				#name.encode_to(&mut r);
			}
		})
		.collect::<TokenStream2>();

	quote!(
		impl _feps::codec::Encode for #ident {
			fn encode(&self) -> _feps::sp_std::prelude::Vec<u8> {
				let mut r = vec![];
				#encode_impl_single
				#encode_impl_rest
				r
			}
		}
	)
}

fn scale_info_impl(
	ident: &syn::Ident,
	voter_type: &syn::Type,
	target_type: &syn::Type,
	weight_type: &syn::Type,
	count: usize,
) -> TokenStream2 {
	let scale_info_impl_single = {
		let name = format!("{}", vote_field(1));
		quote! {
			.field(|f|
				f.ty::<_feps::sp_std::prelude::Vec<
				   (_feps::codec::Compact<#voter_type>, _feps::codec::Compact<#target_type>)
				>>()
				.name(#name)
			)
		}
	};

	let scale_info_impl_double = {
		let name = format!("{}", vote_field(2));
		quote! {
			.field(|f|
				f.ty::<_feps::sp_std::prelude::Vec<(
					_feps::codec::Compact<#voter_type>,
					(_feps::codec::Compact<#target_type>, _feps::codec::Compact<#weight_type>),
					_feps::codec::Compact<#target_type>
				)>>()
				.name(#name)
			)
		}
	};

	let scale_info_impl_rest = (3..=count)
		.map(|c| {
			let name = format!("{}", vote_field(c));
			quote! {
				.field(|f|
					f.ty::<_feps::sp_std::prelude::Vec<(
						_feps::codec::Compact<#voter_type>,
						[
							(_feps::codec::Compact<#target_type>, _feps::codec::Compact<#weight_type>);
							#c - 1
						],
						_feps::codec::Compact<#target_type>
					)>>()
					.name(#name)
				)
			}
		})
		.collect::<TokenStream2>();

	quote!(
		 impl _feps::scale_info::TypeInfo for #ident {
			 type Identity = Self;

			 fn type_info() -> _feps::scale_info::Type<_feps::scale_info::form::MetaForm> {
				 _feps::scale_info::Type::builder()
					 .path(_feps::scale_info::Path::new(stringify!(#ident), module_path!()))
					 .composite(
						 _feps::scale_info::build::Fields::named()
						 #scale_info_impl_single
						 #scale_info_impl_double
						 #scale_info_impl_rest
					 )
			 }
		 }
	)
}
