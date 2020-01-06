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
