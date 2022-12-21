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
use quote::ToTokens;
use std::str::FromStr;

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
			syn::Fields::Named(syn::FieldsNamed { named: fields, .. }) |
			syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed: fields, .. }) => {
				let maybe_field_tys = fields
					.iter()
					.map(|f| generate_field_types(f, &frame_support))
					.collect::<syn::Result<Vec<_>>>();
				let field_tys = match maybe_field_tys {
					Ok(tys) => tys.into_iter().flatten(),
					Err(e) => return e.into_compile_error().into(),
				};
				quote::quote! {
					0_usize
					#(
						.saturating_add(<
							#field_tys as #frame_support::traits::PalletError
						>::MAX_ENCODED_SIZE)
					)*
				}
			},
			syn::Fields::Unit => quote::quote!(0),
		},
		syn::Data::Enum(syn::DataEnum { variants, .. }) => {
			let field_tys = variants
				.iter()
				.map(|variant| generate_variant_field_types(variant, &frame_support))
				.collect::<Result<Vec<Option<Vec<proc_macro2::TokenStream>>>, syn::Error>>();

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

fn generate_field_types(
	field: &syn::Field,
	scrate: &syn::Ident,
) -> syn::Result<Option<proc_macro2::TokenStream>> {
	let attrs = &field.attrs;

	for attr in attrs {
		if attr.path.is_ident("codec") {
			match attr.parse_meta()? {
				syn::Meta::List(ref meta_list) if meta_list.nested.len() == 1 => {
					match meta_list
						.nested
						.first()
						.expect("Just checked that there is one item; qed")
					{
						syn::NestedMeta::Meta(syn::Meta::Path(path))
							if path.get_ident().map_or(false, |i| i == "skip") =>
							return Ok(None),

						syn::NestedMeta::Meta(syn::Meta::Path(path))
							if path.get_ident().map_or(false, |i| i == "compact") =>
						{
							let field_ty = &field.ty;
							return Ok(Some(quote::quote!(#scrate::codec::Compact<#field_ty>)))
						},

						syn::NestedMeta::Meta(syn::Meta::NameValue(syn::MetaNameValue {
							path,
							lit: syn::Lit::Str(lit_str),
							..
						})) if path.get_ident().map_or(false, |i| i == "encoded_as") => {
							let ty = proc_macro2::TokenStream::from_str(&lit_str.value())?;
							return Ok(Some(ty))
						},

						_ => (),
					}
				},
				_ => (),
			}
		}
	}

	Ok(Some(field.ty.to_token_stream()))
}

fn generate_variant_field_types(
	variant: &syn::Variant,
	scrate: &syn::Ident,
) -> syn::Result<Option<Vec<proc_macro2::TokenStream>>> {
	let attrs = &variant.attrs;

	for attr in attrs {
		if attr.path.is_ident("codec") {
			match attr.parse_meta()? {
				syn::Meta::List(ref meta_list) if meta_list.nested.len() == 1 => {
					match meta_list
						.nested
						.first()
						.expect("Just checked that there is one item; qed")
					{
						syn::NestedMeta::Meta(syn::Meta::Path(path))
							if path.get_ident().map_or(false, |i| i == "skip") =>
							return Ok(None),

						_ => (),
					}
				},
				_ => (),
			}
		}
	}

	match &variant.fields {
		syn::Fields::Named(syn::FieldsNamed { named: fields, .. }) |
		syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed: fields, .. }) => {
			let field_tys = fields
				.iter()
				.map(|field| generate_field_types(field, scrate))
				.collect::<syn::Result<Vec<_>>>()?;
			Ok(Some(field_tys.into_iter().flatten().collect()))
		},
		syn::Fields::Unit => Ok(None),
	}
}
