// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Derive macro implementation of `PassBy` with the associated type set to `Codec`.
//!
//! It is required that the type implements `Encode` and `Decode` from the `parity-scale-codec`
//! crate.

use crate::utils::{generate_crate_access, generate_runtime_interface_include};

use syn::{DeriveInput, Result, Generics, parse_quote};

use quote::quote;

use proc_macro2::TokenStream;

/// The derive implementation for `PassBy` with `Codec`.
pub fn derive_impl(mut input: DeriveInput) -> Result<TokenStream> {
	add_trait_bounds(&mut input.generics);
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	let crate_include = generate_runtime_interface_include();
	let crate_ = generate_crate_access();
	let ident = input.ident;

	let res = quote! {
		const _: () = {
			#crate_include

			impl #impl_generics #crate_::pass_by::PassBy for #ident #ty_generics #where_clause {
				type PassBy = #crate_::pass_by::Codec<#ident>;
			}
		};
	};

	Ok(res)
}

/// Add the `codec::Codec` trait bound to every type parameter.
fn add_trait_bounds(generics: &mut Generics) {
	let crate_ = generate_crate_access();

	generics.type_params_mut()
		.for_each(|type_param| type_param.bounds.push(parse_quote!(#crate_::codec::Codec)));
}

