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
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate substrate_codec;
extern crate proc_macro;
extern crate proc_macro2;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use syn::{DeriveInput, Generics, GenericParam};

mod decode;
mod encode;

const ENCODE_ERR: &str = "derive(Encode) failed";

#[proc_macro_derive(Encode)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = syn::parse(input).expect(ENCODE_ERR);
	let name = &input.ident;

	let generics = add_trait_bounds(input.generics, parse_quote!(::substrate_codec::Encode));
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let self_ = quote!(self);
	let dest_ = quote!(dest);
	let encoding = encode::quote(&input.data, &self_, &dest_);

	let expanded = quote! {
		impl #impl_generics ::substrate_codec::Encode for #name #ty_generics #where_clause {
			fn encode_to<T: ::substrate_codec::Output>(&#self_, #dest_: &mut T) {
				#encoding
			}
		}
	};

	expanded.into()
}

#[proc_macro_derive(Decode)]
pub fn decode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = syn::parse(input).expect(ENCODE_ERR);
	let name = &input.ident;

	let generics = add_trait_bounds(input.generics, parse_quote!(::substrate_codec::Decode));
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let input_ = quote!(input);
	let decoding = decode::quote(&input.data, &input_);

	let expanded = quote! {
		impl #impl_generics ::substrate_codec::Decode for #name #ty_generics #where_clause {
			fn decode<I: ::substrate_codec::Input>(#input_: &mut I) -> Option<Self> {
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
