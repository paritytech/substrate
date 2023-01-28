// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Derive macro implementation of `PassBy` with the associated type set to `Inner` and of the
//! helper trait `PassByInner`.
//!
//! It is required that the type is a newtype struct, otherwise an error is generated.

use crate::utils::{generate_crate_access, generate_runtime_interface_include};

use syn::{parse_quote, Data, DeriveInput, Error, Fields, Generics, Ident, Result, Type};

use quote::quote;

use proc_macro2::{Span, TokenStream};

/// The derive implementation for `PassBy` with `Inner` and `PassByInner`.
pub fn derive_impl(mut input: DeriveInput) -> Result<TokenStream> {
	add_trait_bounds(&mut input.generics);
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	let crate_include = generate_runtime_interface_include();
	let crate_ = generate_crate_access();
	let ident = input.ident;
	let (inner_ty, inner_name) = extract_inner_ty_and_name(&input.data)?;

	let access_inner = match inner_name {
		Some(ref name) => quote!(self.#name),
		None => quote!(self.0),
	};

	let from_inner = match inner_name {
		Some(name) => quote!(Self { #name: inner }),
		None => quote!(Self(inner)),
	};

	let res = quote! {
		const _: () = {
			#crate_include

			impl #impl_generics #crate_::pass_by::PassBy for #ident #ty_generics #where_clause {
				type PassBy = #crate_::pass_by::Inner<Self, #inner_ty>;
			}

			impl #impl_generics #crate_::pass_by::PassByInner for #ident #ty_generics #where_clause {
				type Inner = #inner_ty;

				fn into_inner(self) -> Self::Inner {
					#access_inner
				}

				fn inner(&self) -> &Self::Inner {
					&#access_inner
				}

				fn from_inner(inner: Self::Inner) -> Self {
					#from_inner
				}
			}
		};
	};

	Ok(res)
}

/// Add the `RIType` trait bound to every type parameter.
fn add_trait_bounds(generics: &mut Generics) {
	let crate_ = generate_crate_access();

	generics
		.type_params_mut()
		.for_each(|type_param| type_param.bounds.push(parse_quote!(#crate_::RIType)));
}

/// Extract the inner type and optional name from given input data.
///
/// It also checks that the input data is a newtype struct.
fn extract_inner_ty_and_name(data: &Data) -> Result<(Type, Option<Ident>)> {
	if let Data::Struct(ref struct_data) = data {
		match struct_data.fields {
			Fields::Named(ref named) if named.named.len() == 1 => {
				let field = &named.named[0];
				return Ok((field.ty.clone(), field.ident.clone()))
			},
			Fields::Unnamed(ref unnamed) if unnamed.unnamed.len() == 1 => {
				let field = &unnamed.unnamed[0];
				return Ok((field.ty.clone(), field.ident.clone()))
			},
			_ => {},
		}
	}

	Err(Error::new(
		Span::call_site(),
		"Only newtype/one field structs are supported by `PassByInner`!",
	))
}
