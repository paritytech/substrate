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

use frame_support_procedural_tools::generate_crate_access_2018;
use std::{cmp::Ordering, collections::HashMap};
use syn::spanned::Spanned;

pub struct Def {
	pub item: syn::ItemEnum,
	pub span: proc_macro2::Span,
	pub variants: Vec<VariantDef>,
	pub frame_support: syn::Ident,
	pub frame_system: syn::Ident,
	pub runtime: syn::Ident,
	pub sp_core: syn::Ident,
}
impl Def {
	pub fn try_from(mut item: syn::ItemEnum, runtime: syn::Ident) -> syn::Result<Self> {
		let item_span = item.span();
		let frame_support = generate_crate_access_2018("frame-support")?;
		let frame_system = generate_crate_access_2018("frame-system")?;
		let sp_core = generate_crate_access_2018("sp-core")?;

		// TODO: Check if other high-level attributes of #[call_entry::*] are present and error out

		// TODO: Maybe check if derive of Codec and error out as we automatically wanna do that. Bad
		//       style?

		let mut indices = HashMap::new();
		let mut variants = Vec::new();

		for variant in &mut item.variants {
			let call_idx_attr: Option<CallEntryAttr> =
				crate::interface::helper::take_first_item_call_entry_attr(&mut variant.attrs)?
					.into_iter()
					.try_fold(None, |mut call_idx_attr, attr| {
						match attr {
							CallEntryAttr::Index(_span, _index) => {
								if variant.discriminant.is_some() {
									let msg =
								"Invalid call_entry variant. Explicit discriminant is given. \
								Remove and use `#[call_entry::index($expr)]` instead.";
									return Err(syn::Error::new(variant.span(), msg));
								}

								if call_idx_attr.is_some() {
									let msg =
								"Invalid call_entry variant, multiple `#[call_entry::index($expr)]` \
								attributes used on the same variant. Only one is allowed.";
									return Err(syn::Error::new(variant.span(), msg));
								}

								call_idx_attr = Some(attr);
							},
						}

						Ok(call_idx_attr)
					})?;

			let call_idx = match call_idx_attr {
				None => {
					let msg = "Invalid call_entry variant, no `#[call_entry::index($expr)]` \
					 attributes used on variant. Explicit index must be provided.";
					return Err(syn::Error::new(variant.span(), msg));
				},
				Some(index) => match index {
					CallEntryAttr::Index(_, idx) => idx,
				},
			};

			assert!(indices.insert(variant.ident.clone(), call_idx).is_none());

			let inner = match &variant.fields {
				syn::Fields::Unit | syn::Fields::Named(..) => {
					let msg = "Invalid call_entry variant, only unnamed variants are allowed.` \
					 attributes used on variant. Explicit index must be provided.";
					return Err(syn::Error::new(variant.span(), msg));
				},
				syn::Fields::Unnamed(unnamed) => match unnamed.unnamed.len().cmp(&1) {
					Ordering::Equal => unnamed.unnamed.first().expect("Is one. Qed.").ty.clone(),
					Ordering::Greater | Ordering::Less => {
						let msg = format!(
							"Invalid call_entry variant, only a single unnamed field is allowed.` \
					 			Try using the following: {}($ty).",
							variant.ident
						);
						return Err(syn::Error::new(variant.span(), msg));
					},
				},
			};

			variants.push(VariantDef {
				name: variant.ident.clone(),
				index: call_idx,
				inner: Box::new(inner),
				span: variant.span(),
			})
		}

		Ok(Def { item, span: item_span, variants, frame_support, frame_system, sp_core, runtime })
	}
}

pub struct VariantDef {
	pub name: syn::Ident,
	pub index: u8,
	pub inner: Box<syn::Type>,
	pub span: proc_macro2::Span,
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(call_entry);
	syn::custom_keyword!(index);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::call]`)
enum CallEntryAttr {
	Index(proc_macro2::Span, u8),
}

impl syn::parse::Parse for CallEntryAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::call_entry>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::index) {
			let span = content.parse::<keyword::index>()?.span();
			let call_index_content;
			syn::parenthesized!(call_index_content in content);
			let index = call_index_content.parse::<syn::LitInt>()?;
			if !index.suffix().is_empty() {
				let msg = "Number literal must not have a suffix";
				return Err(syn::Error::new(index.span(), msg));
			}
			Ok(CallEntryAttr::Index(span, index.base10_parse()?))
		} else {
			Err(lookahead.error())
		}
	}
}
