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

//! Derives serialization and deserialization codec for complex structs for simple marshalling.

#![cfg_attr(not(feature = "std"), no_std)]
//#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate proc_macro;
extern crate proc_macro2;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use syn::{DeriveInput, Generics, GenericParam, Ident};

mod decode;
mod encode;

const ENCODE_ERR: &str = "derive(Encode) failed";

#[proc_macro_derive(Encode, attributes(codec))]
pub fn encode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = syn::parse(input).expect(ENCODE_ERR);
	let name = &input.ident;

	let generics = add_trait_bounds(input.generics, parse_quote!(::codec::Encode));
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let self_ = quote!(self);
	let dest_ = quote!(dest);
	let encoding = encode::quote(&input.data, name, &self_, &dest_);

	let expanded = quote! {
		impl #impl_generics ::codec::Encode for #name #ty_generics #where_clause {
			fn encode_to<EncOut: ::codec::Output>(&#self_, #dest_: &mut EncOut) {
				#encoding
			}
		}
	};

	expanded.into()
}

#[proc_macro_derive(Decode, attributes(codec))]
pub fn decode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = syn::parse(input).expect(ENCODE_ERR);
	let name = &input.ident;

	let generics = add_trait_bounds(input.generics, parse_quote!(::codec::Decode));
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let input_ = quote!(input);
	let decoding = decode::quote(&input.data, name, &input_);

	let expanded = quote! {
		impl #impl_generics ::codec::Decode for #name #ty_generics #where_clause {
			fn decode<DecIn: ::codec::Input>(#input_: &mut DecIn) -> Option<Self> {
				#decoding
			}
		}
	};

	expanded.into()
}

fn add_trait_bounds(mut generics: Generics, bounds: syn::TypeParamBound) -> Generics {
	for param in &mut generics.params {
		if let GenericParam::Type(ref mut type_param) = *param {
			type_param.bounds.push(bounds.clone());
		}
	}
	generics
}

fn index(v: &syn::Variant, i: usize) -> proc_macro2::TokenStream {
	// look for an index in attributes
	let index = v.attrs.iter().filter_map(|attr| {
		let pair = attr.path.segments.first()?;
		let seg = pair.value();

		if seg.ident == Ident::new("codec", seg.ident.span()) {
			assert_eq!(attr.path.segments.len(), 1);

			let meta = attr.interpret_meta();
			if let Some(syn::Meta::List(ref l)) = meta {
				if let syn::NestedMeta::Meta(syn::Meta::NameValue(ref nv)) = l.nested.last().unwrap().value() {
					assert_eq!(nv.ident, Ident::new("index", nv.ident.span()));
					if let syn::Lit::Str(ref s) = nv.lit {
						let byte: u8 = s.value().parse().expect("Numeric index expected.");
						return Some(byte)
					}
					panic!("Invalid syntax for `codec` attribute: Expected string literal.")
				}
			}
			panic!("Invalid syntax for `codec` attribute: Expected `name = value` pair.")
		} else {
			None
		}
	}).next();

	// then fallback to discriminant or just index
	index.map(|i| quote! { #i })
		.unwrap_or_else(|| v.discriminant
			.as_ref()
			.map(|&(_, ref expr)| quote! { #expr })
			.unwrap_or_else(|| quote! { #i })
		)
}

