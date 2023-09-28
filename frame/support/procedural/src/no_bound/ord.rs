// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

/// Derive Ord but do not bound any generic.
pub fn derive_ord_no_bound(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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
					.map(|i| quote::quote_spanned!(i.span() => self.#i.cmp(&other.#i) ));

				quote::quote!( core::cmp::Ordering::Equal #( .then_with(|| #fields) )* )
			},
			syn::Fields::Unnamed(unnamed) => {
				let fields = unnamed
					.unnamed
					.iter()
					.enumerate()
					.map(|(i, _)| syn::Index::from(i))
					.map(|i| quote::quote_spanned!(i.span() => self.#i.cmp(&other.#i) ));

				quote::quote!( core::cmp::Ordering::Equal #( .then_with(|| #fields) )* )
			},
			syn::Fields::Unit => {
				quote::quote!(core::cmp::Ordering::Equal)
			},
		},
		syn::Data::Enum(_) => {
			let msg = "Enum type not supported by `derive(OrdNoBound)`";
			return syn::Error::new(input.span(), msg).to_compile_error().into()
		},
		syn::Data::Union(_) => {
			let msg = "Union type not supported by `derive(OrdNoBound)`";
			return syn::Error::new(input.span(), msg).to_compile_error().into()
		},
	};

	quote::quote!(
		const _: () = {
			impl #impl_generics core::cmp::Ord for #name #ty_generics #where_clause {
				fn cmp(&self, other: &Self) -> core::cmp::Ordering {
					#impl_
				}
			}
		};
	)
	.into()
}
