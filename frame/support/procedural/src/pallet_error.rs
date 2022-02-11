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

// Derive `PalletError`
pub fn derive_pallet_error(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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

	let max_encoded_size = match data {
		syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
			syn::Fields::Named(f) => {
				let field_tys = f.named.iter().map(|field| &field.ty);
				quote::quote! {
					0_usize
					#(.saturating_add(<
						#field_tys as #frame_support::traits::PalletError
					>::MAX_ENCODED_SIZE))*
				}
			},
			syn::Fields::Unnamed(f) => {
				let field_tys = f.unnamed.iter().map(|field| &field.ty);
				quote::quote! {
					0_usize
					#(.saturating_add(<
						#field_tys as #frame_support::traits::PalletError
					>::MAX_ENCODED_SIZE))*
				}
			},
			syn::Fields::Unit => quote::quote!(0),
		},
		syn::Data::Enum(syn::DataEnum { variants, .. }) => {
			let field_tys = variants
				.iter()
				.map(|variant| {
					match &variant.fields {
						syn::Fields::Unnamed(f) if f.unnamed.len() == 2 => {
							let first = &f.unnamed.first().unwrap().ty;
							let second = &f.unnamed.last().unwrap().ty;

							match (first, second) {
								// Check whether we have (PhantomData, Never), if so we skip it.
								(syn::Type::Path(p1), syn::Type::Path(p2))
									if p1
										.path
										.segments
										.last()
										.map_or(false, |seg| seg.ident == "PhantomData") &&
										p2.path
											.segments
											.last()
											.map_or(false, |seg| seg.ident == "Never") =>
									Ok(None),
								_ => Ok(Some(vec![first, second])),
							}
						},
						syn::Fields::Named(f) =>
							Ok(Some(f.named.iter().map(|field| &field.ty).collect::<Vec<_>>())),
						syn::Fields::Unnamed(f) =>
							Ok(Some(f.unnamed.iter().map(|field| &field.ty).collect::<Vec<_>>())),
						syn::Fields::Unit => Ok(None),
					}
				})
				.collect::<Result<Vec<Option<Vec<&syn::Type>>>, syn::Error>>();

			let field_tys = match field_tys {
				Ok(tys) => tys.into_iter().flatten().collect::<Vec<_>>(),
				Err(e) => return e.to_compile_error().into(),
			};

			// We start with `1`, because the discriminant of an enum is stored as u8
			if field_tys.is_empty() {
				quote::quote!(1)
			} else {
				let variant_sizes = field_tys.into_iter().map(|variant_field_tys| {
					quote::quote! {
						1_usize
						#(.saturating_add(<
							#variant_field_tys as #frame_support::traits::PalletError
						>::MAX_ENCODED_SIZE))*
					}
				});

				quote::quote! {{
					let mut size = 1_usize;
					let mut tmp = 0_usize;
					#(
						tmp = #variant_sizes;
						size = if tmp > size { tmp } else { size };
						tmp = 0_usize;
					)*
					size
				}}
			}
		},
		syn::Data::Union(syn::DataUnion { union_token, .. }) => {
			let msg = "Cannot derive `PalletError` for union; please implement it directly";
			return syn::Error::new(union_token.span, msg).into_compile_error().into()
		},
	};

	quote::quote!(
		const _: () = {
			impl #impl_generics #frame_support::traits::PalletError
				for #name #ty_generics #where_clause
			{
				const MAX_ENCODED_SIZE: usize = #max_encoded_size;
			}
		};
	)
	.into()
}
