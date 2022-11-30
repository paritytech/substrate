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

use quote::{quote, quote_spanned};
use syn::{
	Data, DeriveInput, Error, Fields, GenericParam, Generics, Meta, TraitBound, Type,
	TypeParamBound, parse_quote, spanned::Spanned,
};
use proc_macro_crate::{crate_name, FoundCrate};
use proc_macro2::{Ident, Span};

/// Generate the crate access for the crate using 2018 syntax.
fn generate_crate_access_2018(def_crate: &str) -> Result<syn::Ident, Error> {
	match crate_name(def_crate) {
		Ok(FoundCrate::Itself) => {
			let name = def_crate.to_string().replace("-", "_");
			Ok(syn::Ident::new(&name, Span::call_site()))
		},
		Ok(FoundCrate::Name(name)) => {
			Ok(Ident::new(&name, Span::call_site()))
		},
		Err(e) => {
			Err(Error::new(Span::call_site(), e))
		}
	}
}

/// Derive `MaxEncodedLen`.
#[proc_macro_derive(MaxEncodedLen, attributes(max_encoded_len_crate))]
pub fn derive_max_encoded_len(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input: DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let mel_trait = match max_encoded_len_trait(&input) {
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

fn max_encoded_len_trait(input: &DeriveInput) -> syn::Result<TraitBound> {
	let mel = {
		const EXPECT_LIST: &str = "expect: #[max_encoded_len_crate(path::to::crate)]";
		const EXPECT_PATH: &str = "expect: path::to::crate";

		macro_rules! return_err {
			($wrong_style:expr, $err:expr) => {
				return Err(Error::new($wrong_style.span(), $err))
			};
		}

		let mut mel_crates = Vec::with_capacity(2);
		mel_crates.extend(input
			.attrs
			.iter()
			.filter(|attr| attr.path == parse_quote!(max_encoded_len_crate))
			.take(2)
			.map(|attr| {
				let meta_list = match attr.parse_meta()? {
					Meta::List(meta_list) => meta_list,
					Meta::Path(wrong_style) => return_err!(wrong_style, EXPECT_LIST),
					Meta::NameValue(wrong_style) => return_err!(wrong_style, EXPECT_LIST),
				};
				if meta_list.nested.len() != 1 {
					return_err!(meta_list, "expected exactly 1 item");
				}
				let first_nested =
					meta_list.nested.into_iter().next().expect("length checked above");
				let meta = match first_nested {
					syn::NestedMeta::Lit(l) => {
						return_err!(l, "expected a path item, not a literal")
					}
					syn::NestedMeta::Meta(meta) => meta,
				};
				let path = match meta {
					Meta::Path(path) => path,
					Meta::List(ref wrong_style) => return_err!(wrong_style, EXPECT_PATH),
					Meta::NameValue(ref wrong_style) => return_err!(wrong_style, EXPECT_PATH),
				};
				Ok(path)
			})
			.collect::<Result<Vec<_>, _>>()?);

		// we have to return `Result<Ident, Error>` here in order to satisfy the trait
		// bounds for `.or_else` for `generate_crate_access_2018`, even though `Option<Ident>`
		// would be more natural in this circumstance.
		match mel_crates.len() {
			0 => Err(Error::new(
				input.span(),
				"this error is spurious and swallowed by the or_else below",
			)),
			1 => Ok(mel_crates.into_iter().next().expect("length is checked")),
			_ => return_err!(mel_crates[1], "duplicate max_encoded_len_crate definition"),
		}
	}
	.or_else(|_| generate_crate_access_2018("max-encoded-len").map(|ident| ident.into()))?;
	Ok(parse_quote!(#mel::MaxEncodedLen))
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
			Error::new(data.union_token.span(), "Union types are not supported").to_compile_error()
		}
	}
}
