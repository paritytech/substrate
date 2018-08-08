// Copyright 2018 Parity Technologies (UK) Ltd.
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

use proc_macro2::{Span, TokenStream, Ident};
use syn::{
	Data, Fields,
	spanned::Spanned,
};

pub fn quote(data: &Data, type_name: &Ident, input: &TokenStream) -> TokenStream {
	let call_site = Span::call_site();
	match *data {
		Data::Struct(ref data) => match data.fields {
			Fields::Named(_) | Fields::Unnamed(_) => create_instance(
				call_site,
				quote! { #type_name },
				input,
				&data.fields,
			),
			Fields::Unit => {
				quote_spanned! {call_site =>
					drop(#input);
					Some(#type_name)
				}
			},
		},
		Data::Enum(ref data) => {
			assert!(data.variants.len() < 256, "Currently only enums with at most 256 variants are encodable.");

			let recurse = data.variants.iter().enumerate().map(|(i, v)| {
				let name = &v.ident;
				let index = super::index(v, i);

				let create = create_instance(
					call_site,
					quote! { #type_name :: #name },
					input,
					&v.fields,
				);

				quote_spanned! { v.span() =>
					x if x == #index as u8 => {
						#create
					},
				}
			});

			quote! {
				match #input.read_byte()? {
					#( #recurse )*
					_ => None,
				}

			}

		},
		Data::Union(_) => panic!("Union types are not supported."),
	}
}

fn create_instance(call_site: Span, name: TokenStream, input: &TokenStream, fields: &Fields) -> TokenStream {
	match *fields {
		Fields::Named(ref fields) => {
			let recurse = fields.named.iter().map(|f| {
				let name = &f.ident;
				let field = quote_spanned!(call_site => #name);

				quote_spanned! { f.span() =>
					#field: ::codec::Decode::decode(#input)?
				}
			});

			quote_spanned! {call_site =>
				Some(#name {
					#( #recurse, )*
				})
			}
		},
		Fields::Unnamed(ref fields) => {
			let recurse = fields.unnamed.iter().map(|f| {
				quote_spanned! { f.span() =>
					::codec::Decode::decode(#input)?
				}
			});

			quote_spanned! {call_site =>
				Some(#name (
					#( #recurse, )*
				))
			}
		},
		Fields::Unit => {
			quote_spanned! {call_site =>
				Some(#name)
			}
		},
	}
}
