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

//! Derive macro implementation of `PassBy` with the associated type set to `Enum`.
//!
//! Besides `PassBy`, `TryFrom<u8>` and `From<Self> for u8` are implemented for the type.

use crate::utils::{generate_crate_access, generate_runtime_interface_include};

use syn::{DeriveInput, Result, Data, Fields, Error, Ident};

use quote::quote;

use proc_macro2::{TokenStream, Span};

/// The derive implementation for `PassBy` with `Enum`.
pub fn derive_impl(input: DeriveInput) -> Result<TokenStream> {
	let crate_include = generate_runtime_interface_include();
	let crate_ = generate_crate_access();
	let ident = input.ident;
	let enum_fields = get_enum_field_idents(&input.data)?
		.enumerate()
		.map(|(i, v)| {
			let i = i as u8;

			v.map(|v| (quote!(#i => Ok(#ident::#v)), quote!(#ident::#v => #i)))
		})
		.collect::<Result<Vec<_>>>()?;
	let try_from_variants = enum_fields.iter().map(|i| &i.0);
	let into_variants = enum_fields.iter().map(|i| &i.1);

	let res = quote! {
		const _: () = {
			#crate_include

			impl #crate_::pass_by::PassBy for #ident {
				type PassBy = #crate_::pass_by::Enum<#ident>;
			}

			impl #crate_::sp_std::convert::TryFrom<u8> for #ident {
				type Error = ();

				fn try_from(inner: u8) -> #crate_::sp_std::result::Result<Self, ()> {
					match inner {
						#( #try_from_variants, )*
						_ => Err(()),
					}
				}
			}

			impl From<#ident> for u8 {
				fn from(var: #ident) -> u8 {
					match var {
						#( #into_variants ),*
					}
				}
			}
		};
	};

	Ok(res)
}

/// Get the enum fields idents of the given `data` object as iterator.
///
/// Returns an error if the number of variants is greater than `256`, the given `data` is not an
/// enum or a variant is not an unit.
fn get_enum_field_idents<'a>(data: &'a Data) -> Result<impl Iterator<Item = Result<&'a Ident>>> {
	match data {
		Data::Enum(d) => {
			if d.variants.len() <= 256 {
				Ok(
					d.variants.iter().map(|v| if let Fields::Unit = v.fields {
						Ok(&v.ident)
					} else {
						Err(Error::new(
							Span::call_site(),
							"`PassByEnum` only supports unit variants.",
						))
					})
				)
			} else {
				Err(Error::new(Span::call_site(), "`PassByEnum` only supports `256` variants."))
			}
		},
		_ => Err(Error::new(Span::call_site(), "`PassByEnum` only supports enums as input type."))
	}
}
