// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use proc_macro2::Span;
use quote::{quote, quote_spanned};
use syn::{spanned::Spanned, Data, DeriveInput, Fields};

/// Derive Default but do not bound any generic.
pub fn derive_default_no_bound(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = syn::parse_macro_input!(input as DeriveInput);

	let name = &input.ident;

	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

	let impl_ = match input.data {
		Data::Struct(struct_) => match struct_.fields {
			Fields::Named(named) => {
				let fields = named.named.iter().map(|field| &field.ident).map(|ident| {
					quote_spanned! {ident.span() =>
						#ident: core::default::Default::default()
					}
				});

				quote!(Self { #( #fields, )* })
			},
			Fields::Unnamed(unnamed) => {
				let fields = unnamed.unnamed.iter().map(|field| {
					quote_spanned! {field.span()=>
						core::default::Default::default()
					}
				});

				quote!(Self( #( #fields, )* ))
			},
			Fields::Unit => {
				quote!(Self)
			},
		},
		Data::Enum(enum_) => {
			if enum_.variants.is_empty() {
				return syn::Error::new_spanned(name, "cannot derive Default for an empty enum")
					.to_compile_error()
					.into()
			}

			// all #[default] attrs with the variant they're on; i.e. a var
			let default_variants = enum_
				.variants
				.into_iter()
				.filter(|variant| variant.attrs.iter().any(|attr| attr.path.is_ident("default")))
				.collect::<Vec<_>>();

			match &*default_variants {
				[] => {
					return syn::Error::new(
						name.clone().span(),
						// writing this as a regular string breaks rustfmt for some reason
						r#"no default declared, make a variant default by placing `#[default]` above it"#,
					)
					.into_compile_error()
					.into()
				},
				// only one variant with the #[default] attribute set
				[default_variant] => {
					let variant_attrs = default_variant
						.attrs
						.iter()
						.filter(|a| a.path.is_ident("default"))
						.collect::<Vec<_>>();

					// check that there is only one #[default] attribute on the variant
					if let [first_attr, second_attr, additional_attrs @ ..] = &*variant_attrs {
						let mut err =
							syn::Error::new(Span::call_site(), "multiple `#[default]` attributes");

						err.combine(syn::Error::new_spanned(first_attr, "`#[default]` used here"));

						err.extend([second_attr].into_iter().chain(additional_attrs).map(
							|variant| {
								syn::Error::new_spanned(variant, "`#[default]` used again here")
							},
						));

						return err.into_compile_error().into()
					}

					let variant_ident = &default_variant.ident;

					let fully_qualified_variant_path = quote!(Self::#variant_ident);

					match &default_variant.fields {
						Fields::Named(named) => {
							let fields =
								named.named.iter().map(|field| &field.ident).map(|ident| {
									quote_spanned! {ident.span()=>
										#ident: core::default::Default::default()
									}
								});

							quote!(#fully_qualified_variant_path { #( #fields, )* })
						},
						Fields::Unnamed(unnamed) => {
							let fields = unnamed.unnamed.iter().map(|field| {
								quote_spanned! {field.span()=>
									core::default::Default::default()
								}
							});

							quote!(#fully_qualified_variant_path( #( #fields, )* ))
						},
						Fields::Unit => fully_qualified_variant_path,
					}
				},
				[first, additional @ ..] => {
					let mut err = syn::Error::new(Span::call_site(), "multiple declared defaults");

					err.combine(syn::Error::new_spanned(first, "first default"));

					err.extend(
						additional
							.into_iter()
							.map(|variant| syn::Error::new_spanned(variant, "additional default")),
					);

					return err.into_compile_error().into()
				},
			}
		},
		Data::Union(union_) =>
			return syn::Error::new_spanned(
				union_.union_token,
				"Union type not supported by `derive(DefaultNoBound)`",
			)
			.to_compile_error()
			.into(),
	};

	quote!(
		const _: () = {
			impl #impl_generics core::default::Default for #name #ty_generics #where_clause {
				fn default() -> Self {
					#impl_
				}
			}
		};
	)
	.into()
}
