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

mod expand;
mod parse;

use quote::{format_ident, quote};
use syn::{parse_macro_input, DeriveInput, ItemTrait, Path};

pub fn interface(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	if !attr.is_empty() {
		let msg = "Invalid interface macro call: unexpected attribute. Macro call must be \
				bare, such as `#[frame_support::interface]` or `#[interface]`.";
		let span = proc_macro2::TokenStream::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into()
	}

	let item = syn::parse_macro_input!(item as syn::ItemTrait);
	match r#mod::Def::try_from(item) {
		Ok(def) => r#mod::expand(def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}

pub fn interface_2(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let trait_item = parse_macro_input!(item as ItemTrait);
	let attr_item = parse_macro_input!(attr as AttributeArgs);
	let trait_ident = &trait_item.ident;
	let trait_item_clone = trait_item.clone();

	// Rule 1: The macro can only be applied to traits.
	if !matches!(trait_item_clone, ItemTrait { .. }) {
		panic!("The macro can only be applied to traits.");
	}

	// Rule 2: The macro must automatically set a trait called Core as a supertrait of the trait
	// that the interface macro is applied to.
	let core_trait = Path::new("Core");
	let supertraits = trait_item_clone.supertraits.clone();
	let mut has_core_trait = false;
	for trait_path in supertraits {
		if trait_path.path.is_ident("Core") {
			has_core_trait = true;
			break
		}
	}
	if !has_core_trait {
		let new_supertraits = quote! {
			#(#supertraits,)* #core_trait
		};
		let mut trait_item = trait_item_clone.clone();
		trait_item.supertraits = syn::parse2(new_supertraits).unwrap();
	}

	// Rule 3: The trait that the interface macro is applied to must not have generics.
	if trait_item.generics.params.len() > 0 || trait_item.generics.where_clause.is_some() {
		panic!("The trait that the interface macro is applied to must not have generics.");
	}

	// Rule 4: The trait that the interface macro is applied to can have arbitrary associated types,
	// that must be carried over to the expansion.
	let associated_types = trait_item.items.iter().filter_map(|item| {
		if let syn::TraitItem::Type(t) = item {
			Some(t.clone())
		} else {
			None
		}
	});

	let mut new_items = Vec::new();

	// Rule 5: The macro must support the following procedural macro attributes.
	for attr in attr_item {
		if let syn::NestedMeta::Meta(meta) = attr {
			if let syn::Meta::NameValue(nv) = meta {
				if nv.path.is_ident("with_selector") {
					let mut new_methods = Vec::new();
					let mut default_selector = false;

					// Rule 5.1: The interface::with_selector attribute is usable as an attribute on
					// the trait the macro is applied to.
					for item in trait_item.items.iter() {
						if let syn::TraitItem::Method(method) = item {
							let is_view = method.attrs.iter().any(|attr| {
								attr.path.is_ident("interface") &&
									attr.tokens.to_string().contains("view")
							});

							let is_call = method.attrs.iter().any(|attr| {
								attr.path.is_ident("interface") &&
									attr.tokens.to_string().contains("call")
							});

							let is_selector = method.attrs.iter().any(|attr| {
								attr.path.is_ident("interface") &&
									attr.tokens.to_string().contains("selector")
							});

							let is_default_selector = method.attrs.iter().any(|attr| {
								attr.path.is_ident("interface") &&
									attr.tokens.to_string().contains("default_selector")
							});

							if is_view && is_call {}
						}
					}
				}
			}
		}
	}

	TokenStream::new()
}
