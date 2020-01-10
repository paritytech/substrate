// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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

