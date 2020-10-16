// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

/// Derive Debug but do not bound any generics.
pub fn derive_debug_no_bound(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input: syn::DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let input_ident = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

	let impl_ = match input.data {
		syn::Data::Struct(struct_) => match struct_.fields {
			syn::Fields::Named(named) => {
				let fields = named.named.iter()
					.map(|i| &i.ident)
					.map(|i| quote::quote_spanned!(i.span() => .field(stringify!(#i), &self.#i) ));

				quote::quote!(
					fmt.debug_struct(stringify!(#input_ident))
						#( #fields )*
						.finish()
				)
			},
			syn::Fields::Unnamed(unnamed) => {
				let fields = unnamed.unnamed.iter().enumerate()
					.map(|(i, _)| syn::Index::from(i))
					.map(|i| quote::quote_spanned!(i.span() => .field(&self.#i) ));

				quote::quote!(
					fmt.debug_tuple(stringify!(#input_ident))
						#( #fields )*
						.finish()
				)
			},
			syn::Fields::Unit => quote::quote!( fmt.write_str(stringify!(#input_ident)) ),
		},
		syn::Data::Enum(enum_) => {
			let variants = enum_.variants.iter()
				.map(|variant| {
					let ident = &variant.ident;
					let full_variant_str = format!("{}::{}", input_ident, ident);
					match &variant.fields {
						syn::Fields::Named(named) => {
							let captured = named.named.iter().map(|i| &i.ident);
							let debugged = captured.clone()
								.map(|i| quote::quote_spanned!(i.span() =>
									.field(stringify!(#i), &#i)
								));
							quote::quote!(
								Self::#ident { #( ref #captured, )* } => {
									fmt.debug_struct(#full_variant_str)
										#( #debugged )*
										.finish()
								}
							)
						},
						syn::Fields::Unnamed(unnamed) => {
							let captured = unnamed.unnamed.iter().enumerate()
								.map(|(i, f)| syn::Ident::new(&format!("_{}", i), f.span()));
							let debugged = captured.clone()
								.map(|i| quote::quote_spanned!(i.span() => .field(&#i)));
							quote::quote!(
								Self::#ident ( #( ref #captured, )* ) => {
									fmt.debug_tuple(#full_variant_str)
										#( #debugged )*
										.finish()
								}
							)
						},
						syn::Fields::Unit => quote::quote!(
							Self::#ident => fmt.write_str(#full_variant_str)
						),
					}
				});

			quote::quote!(match *self {
				#( #variants, )*
			})
		},
		syn::Data::Union(_) => {
			let msg = "Union type not supported by `derive(DebugNoBound)`";
			return syn::Error::new(input.span(), msg).to_compile_error().into()
		},
	};

	quote::quote!(
		const _: () = {
			impl #impl_generics core::fmt::Debug for #input_ident #ty_generics #where_clause {
				fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
					#impl_
				}
			}
		};
	).into()
}
