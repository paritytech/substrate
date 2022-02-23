// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use syn::spanned::Spanned;

/// Derive PartialEq but do not bound any generic.
pub fn derive_partial_eq_no_bound(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input: syn::DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

	let impl_ = match input.data {
		syn::Data::Struct(struct_) => match struct_.fields {
			syn::Fields::Named(named) => {
				let fields = named
					.named
					.iter()
					.map(|i| &i.ident)
					.map(|i| quote::quote_spanned!(i.span() => self.#i == other.#i ));

				quote::quote!( true #( && #fields )* )
			},
			syn::Fields::Unnamed(unnamed) => {
				let fields = unnamed
					.unnamed
					.iter()
					.enumerate()
					.map(|(i, _)| syn::Index::from(i))
					.map(|i| quote::quote_spanned!(i.span() => self.#i == other.#i ));

				quote::quote!( true #( && #fields )* )
			},
			syn::Fields::Unit => {
				quote::quote!(true)
			},
		},
		syn::Data::Enum(enum_) => {
			let variants =
				enum_.variants.iter().map(|variant| {
					let ident = &variant.ident;
					match &variant.fields {
						syn::Fields::Named(named) => {
							let names = named.named.iter().map(|i| &i.ident);
							let other_names = names.clone().enumerate().map(|(n, ident)| {
								syn::Ident::new(&format!("_{}", n), ident.span())
							});

							let capture = names.clone();
							let other_capture = names
								.clone()
								.zip(other_names.clone())
								.map(|(i, other_i)| quote::quote!(#i: #other_i));
							let eq = names.zip(other_names).map(
								|(i, other_i)| quote::quote_spanned!(i.span() => #i == #other_i),
							);
							quote::quote!(
								(
									Self::#ident { #( #capture, )* },
									Self::#ident { #( #other_capture, )* },
								) => true #( && #eq )*
							)
						},
						syn::Fields::Unnamed(unnamed) => {
							let names = unnamed
								.unnamed
								.iter()
								.enumerate()
								.map(|(i, f)| syn::Ident::new(&format!("_{}", i), f.span()));
							let other_names =
								unnamed.unnamed.iter().enumerate().map(|(i, f)| {
									syn::Ident::new(&format!("_{}_other", i), f.span())
								});
							let eq = names.clone().zip(other_names.clone()).map(
								|(i, other_i)| quote::quote_spanned!(i.span() => #i == #other_i),
							);
							quote::quote!(
								(
									Self::#ident ( #( #names, )* ),
									Self::#ident ( #( #other_names, )* ),
								) => true #( && #eq )*
							)
						},
						syn::Fields::Unit => quote::quote!( (Self::#ident, Self::#ident) => true ),
					}
				});

			let mut different_variants = vec![];
			for (i, i_variant) in enum_.variants.iter().enumerate() {
				for (j, j_variant) in enum_.variants.iter().enumerate() {
					if i != j {
						let i_ident = &i_variant.ident;
						let j_ident = &j_variant.ident;
						different_variants.push(quote::quote!(
							(Self::#i_ident { .. }, Self::#j_ident { .. }) => false
						))
					}
				}
			}

			quote::quote!( match (self, other) {
				#( #variants, )*
				#( #different_variants, )*
			})
		},
		syn::Data::Union(_) => {
			let msg = "Union type not supported by `derive(PartialEqNoBound)`";
			return syn::Error::new(input.span(), msg).to_compile_error().into()
		},
	};

	quote::quote!(
		const _: () = {
			impl #impl_generics core::cmp::PartialEq for #name #ty_generics #where_clause {
				fn eq(&self, other: &Self) -> bool {
					#impl_
				}
			}
		};
	)
	.into()
}
