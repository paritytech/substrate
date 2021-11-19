// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use frame_support_procedural_tools::generate_crate_access_2018;
use std::convert::identity;

// Derive `CompactPalletError`
pub fn derive_compact_pallet_error(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let syn::DeriveInput { ident: name, generics, data, .. } = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let frame_support = match generate_crate_access_2018("frame-support") {
		Ok(c) => c,
		Err(e) => return e.into_compile_error().into(),
	};
	let frame_support = &frame_support;
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let compactness_check = match data {
		syn::Data::Struct(syn::DataStruct { struct_token, fields, .. }) => {
			if fields.len() > 1 {
				let msg = "Cannot derive `CompactPalletError` for structs with more than 1 field";
				return syn::Error::new(struct_token.span, msg).into_compile_error().into()
			}

			match fields {
				syn::Fields::Named(mut f) if f.named.len() == 1 => {
					let field_ty = f.named.pop().unwrap().into_value().ty;
					quote::quote! {
						<
							#field_ty as #frame_support::traits::CompactPalletError
						>::check_compactness()
					}
				},
				syn::Fields::Unnamed(mut f) if f.unnamed.len() == 1 => {
					let field_ty = f.unnamed.pop().unwrap().into_value().ty;
					quote::quote! {
						<
							#field_ty as #frame_support::traits::CompactPalletError
						>::check_compactness()
					}
				},
				_ => quote::quote!(true),
			}
		},
		syn::Data::Enum(syn::DataEnum { variants, .. }) => {
			let field_tys = variants
				.into_iter()
				.map(|variant| match variant.fields {
					syn::Fields::Named(mut f) if f.named.len() == 1 =>
						Ok(Some(f.named.pop().unwrap().into_value().ty)),
					syn::Fields::Unnamed(mut f) if f.unnamed.len() == 1 =>
						Ok(Some(f.unnamed.pop().unwrap().into_value().ty)),
					syn::Fields::Unit => Ok(None),
					_ => {
						let msg = "Cannot derive `CompactPalletError` for enum with variants \
						containing more than 1 field";
						let err = syn::Error::new(variant.ident.span(), msg);
						Err(err)
					},
				})
				.collect::<Result<Vec<Option<syn::Type>>, syn::Error>>();

			let field_tys = match field_tys {
				Ok(tys) => tys.into_iter().filter_map(identity).collect::<Vec<_>>(),
				Err(e) => return e.to_compile_error().into(),
			};

			if field_tys.is_empty() {
				quote::quote!(true)
			} else {
				quote::quote! {
					#(
						<
							#field_tys as #frame_support::traits::CompactPalletError
						>::check_compactness()
					)&&*
				}
			}
		},
		syn::Data::Union(syn::DataUnion { union_token, .. }) => {
			let msg = "Cannot derive `CompactPalletError` for union; please implement it directly";
			return syn::Error::new(union_token.span, msg).into_compile_error().into()
		},
	};

	quote::quote!(
		const _: () = {
			impl #impl_generics #frame_support::traits::CompactPalletError
				for #name #ty_generics #where_clause
			{
				fn check_compactness() -> bool {
					#compactness_check
				}
			}
		};
	)
	.into()
}
