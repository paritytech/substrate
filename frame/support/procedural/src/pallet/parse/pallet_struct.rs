// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use super::helper;
use syn::spanned::Spanned;
use quote::ToTokens;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(Pallet);
	syn::custom_keyword!(generate_store);
	syn::custom_keyword!(Store);
}

/// Definition of the pallet pallet.
pub struct PalletStructDef {
	/// The index of item in pallet pallet.
	pub index: usize,
	/// A set of usage of instance, must be check for consistency with config trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The keyword Pallet used (contains span).
	pub pallet: keyword::Pallet,
	/// Whether the trait `Store` must be generated.
	pub store: Option<(syn::Visibility, keyword::Store)>,
	/// The span of the pallet::pallet attribute.
	pub attr_span: proc_macro2::Span,
}

/// Parse for `#[pallet::generate_store($vis trait Store)]`
pub struct PalletStructAttr {
	vis: syn::Visibility,
	keyword: keyword::Store,
}

impl syn::parse::Parse for PalletStructAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;
		content.parse::<keyword::generate_store>()?;

		let generate_content;
		syn::parenthesized!(generate_content in content);
		let vis = generate_content.parse::<syn::Visibility>()?;
		generate_content.parse::<syn::Token![trait]>()?;
		let keyword = generate_content.parse::<keyword::Store>()?;
		Ok(Self { vis, keyword })
	}
}

impl PalletStructDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Struct(item) = item {
			item
		} else {
			let msg = "Invalid pallet::pallet, expected struct definition";
			return Err(syn::Error::new(item.span(), msg));
		};

		let mut event_attrs: Vec<PalletStructAttr> = helper::take_item_attrs(&mut item.attrs)?;
		if event_attrs.len() > 1 {
			let msg = "Invalid pallet::pallet, multiple argument pallet::generate_store found";
			return Err(syn::Error::new(event_attrs[1].keyword.span(), msg));
		}
		let store = event_attrs.pop().map(|attr| (attr.vis, attr.keyword));

		let pallet = syn::parse2::<keyword::Pallet>(item.ident.to_token_stream())?;

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::pallet, Pallet must be public";
			return Err(syn::Error::new(item.span(), msg));
		}

		if item.generics.where_clause.is_some() {
			let msg = "Invalid pallet::pallet, where clause not supported on Pallet declaration";
			return Err(syn::Error::new(item.generics.where_clause.span(), msg));
		}

		let mut instances = vec![];
		instances.push(helper::check_type_def_gen_no_bounds(&item.generics, item.ident.span())?);

		Ok(Self { index, instances, pallet, store, attr_span })
	}
}
