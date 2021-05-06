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
use quote::{quote, quote_spanned};
use syn::{
	Data, DeriveInput, Fields, GenericParam, Generics, TraitBound, Type, TypeParamBound,
	parse_quote, spanned::Spanned,
};

/// impl for `#[derive(MaxEncodedLen)]`
pub fn derive_max_encoded_len(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input: DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let mel_trait = match max_encoded_len_trait() {
		Ok(mel_trait) => mel_trait,
		Err(e) => return e.to_compile_error().into(),
	};

	let name = &input.ident;
	let generics = add_trait_bounds(input.generics, mel_trait.clone());
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let data_expr = data_length_expr(&input.data);

	quote::quote!(
		const _: () = {
			impl #impl_generics #mel_trait for #name #ty_generics #where_clause {
				fn max_encoded_len() -> usize {
					#data_expr
				}
			}
		};
	)
	.into()
}

fn max_encoded_len_trait() -> syn::Result<TraitBound> {
	let frame_support = generate_crate_access_2018("frame-support")?;
	Ok(parse_quote!(#frame_support::traits::MaxEncodedLen))
}

// Add a bound `T: MaxEncodedLen` to every type parameter T.
fn add_trait_bounds(mut generics: Generics, mel_trait: TraitBound) -> Generics {
	for param in &mut generics.params {
		if let GenericParam::Type(ref mut type_param) = *param {
			type_param.bounds.push(TypeParamBound::Trait(mel_trait.clone()));
		}
	}
	generics
}

/// generate an expression to sum up the max encoded length from several fields
fn fields_length_expr(fields: &Fields) -> proc_macro2::TokenStream {
	let type_iter: Box<dyn Iterator<Item = &Type>> = match fields {
		Fields::Named(ref fields) => Box::new(fields.named.iter().map(|field| &field.ty)),
		Fields::Unnamed(ref fields) => Box::new(fields.unnamed.iter().map(|field| &field.ty)),
		Fields::Unit => Box::new(std::iter::empty()),
	};
	// expands to an expression like
	//
	//   0
	//     .saturating_add(<type of first field>::max_encoded_len())
	//     .saturating_add(<type of second field>::max_encoded_len())
	//
	// We match the span of each field to the span of the corresponding
	// `max_encoded_len` call. This way, if one field's type doesn't implement
	// `MaxEncodedLen`, the compiler's error message will underline which field
	// caused the issue.
	let expansion = type_iter.map(|ty| {
		quote_spanned! {
			ty.span() => .saturating_add(<#ty>::max_encoded_len())
		}
	});
	quote! {
		0_usize #( #expansion )*
	}
}

// generate an expression to sum up the max encoded length of each field
fn data_length_expr(data: &Data) -> proc_macro2::TokenStream {
	match *data {
		Data::Struct(ref data) => fields_length_expr(&data.fields),
		Data::Enum(ref data) => {
			// We need an expression expanded for each variant like
			//
			//   0
			//     .max(<variant expression>)
			//     .max(<variant expression>)
			//     .saturating_add(1)
			//
			// The 1 derives from the discriminant; see
			// https://github.com/paritytech/parity-scale-codec/
			//   blob/f0341dabb01aa9ff0548558abb6dcc5c31c669a1/derive/src/encode.rs#L211-L216
			//
			// Each variant expression's sum is computed the way an equivalent struct's would be.

			let expansion = data.variants.iter().map(|variant| {
				let variant_expression = fields_length_expr(&variant.fields);
				quote! {
					.max(#variant_expression)
				}
			});

			quote! {
				0_usize #( #expansion )* .saturating_add(1)
			}
		}
		Data::Union(ref data) => {
			// https://github.com/paritytech/parity-scale-codec/
			//   blob/f0341dabb01aa9ff0548558abb6dcc5c31c669a1/derive/src/encode.rs#L290-L293
			syn::Error::new(data.union_token.span(), "Union types are not supported")
				.to_compile_error()
		}
	}
}
