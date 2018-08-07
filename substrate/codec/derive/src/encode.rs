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

use proc_macro2::{Span, TokenStream};
use syn::{
	Data, Fields, Ident, Index,
	spanned::Spanned,
};

pub fn quote(data: &Data, type_name: &Ident, self_: &TokenStream, dest_: &TokenStream) -> TokenStream {
	let call_site = Span::call_site();
	match *data {
		Data::Struct(ref data) => match data.fields {
			Fields::Named(ref fields) => {
				let recurse = fields.named.iter().map(|f| {
					let name = &f.ident;
					let field = quote_spanned!(call_site => #self_.#name);

					quote_spanned! { f.span() =>
						#dest_.push(&#field);
					}
				});

				quote_spanned! { call_site =>
					#( #recurse )*
				}
			},
			Fields::Unnamed(ref fields) => {
				let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
					let index = Index { index: i as u32, span: call_site };
					let field = quote_spanned!(call_site => #self_.#index);
					quote_spanned! { f.span() =>
						#dest_.push(&#field);
					}
				});

				quote! {
					#( #recurse )*
				}
			},
			// Do nothing, we don't encode unit type and assume it's always decodable.
			Fields::Unit => quote! {
				drop(#dest_);
			},
		},
		Data::Enum(ref data) => {
			assert!(data.variants.len() < 256, "Currently only enums with less than 255 variants are encodable.");

			let recurse = data.variants.iter().enumerate().map(|(i, f)| {
				let name = &f.ident;

				match f.fields {
					Fields::Named(ref fields) => {
						let names = fields.named.iter().map(|f| {
							let field_name = &f.ident;
							quote_spanned!(call_site => #field_name)
						}).collect::<Vec<_>>();

						let fields = names.iter();
						let encode_fields = names.iter().map(|f| {
							quote_spanned! { call_site => #dest_.push(#f); }
						});

						quote_spanned! { f.span() =>
							#type_name :: #name { #( ref #fields, )* } => {
								#dest_.push_byte(#i as u8);
								#( #encode_fields )*
							}
						}
					},
					Fields::Unnamed(ref fields) => {
						let names = fields.unnamed.iter().enumerate().map(|(i, _f)| {
							let ident = Ident::new(&format!("f_{}", i), call_site);
							quote_spanned!(call_site => #ident)
						}).collect::<Vec<_>>();

						let fields = names.iter();
						let encode_fields = names.iter().map(|f| {
							quote_spanned! { call_site => #dest_.push(#f); }
						});

						quote_spanned! { f.span() =>
							#type_name :: #name ( #( ref #fields, )* ) => {
								#dest_.push_byte(#i as u8);
								#( #encode_fields )*
							}
						}
					},
					Fields::Unit => {
						quote_spanned! { f.span() =>
							#type_name :: #name => {
								#dest_.push_byte(#i as u8);
							}
						}
					},
				}
			});

			quote! {
				match *#self_ {
					#( #recurse )*,
					_ => unreachable!(),
				}
			}
		},
		// NOTE [ToDr] we currently don't use unions at all.
		Data::Union(_) => unimplemented!(),
	}
}


