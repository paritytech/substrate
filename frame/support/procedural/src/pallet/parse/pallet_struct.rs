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

use super::helper;
use quote::ToTokens;
use syn::spanned::Spanned;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(Pallet);
	syn::custom_keyword!(generate_store);
	syn::custom_keyword!(without_storage_info);
	syn::custom_keyword!(storage_version);
	syn::custom_keyword!(Store);
	syn::custom_keyword!(call_weight);
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
	pub store: Option<(syn::Visibility, keyword::Store, proc_macro2::Span)>,
	/// The span of the pallet::pallet attribute.
	pub attr_span: proc_macro2::Span,
	/// Whether to specify the storages max encoded len when implementing `StorageInfoTrait`.
	/// Contains the span of the attribute.
	pub without_storage_info: Option<proc_macro2::Span>,
	/// The current storage version of the pallet.
	pub storage_version: Option<syn::Path>,
	pub call_weight: Option<PalletCallWeight>,
}

/// Parse for one variant of:
/// * `#[pallet::generate_store($vis trait Store)]`
/// * `#[pallet::without_storage_info]`
/// * `#[pallet::storage_version(STORAGE_VERSION)]`
/// * `#[pallet::call_weight($weight_trait)]`
pub enum PalletStructAttr {
	GenerateStore { span: proc_macro2::Span, vis: syn::Visibility, keyword: keyword::Store },
	WithoutStorageInfoTrait(proc_macro2::Span),
	StorageVersion { storage_version: syn::Path, span: proc_macro2::Span },
	CallWeight(PalletCallWeight),
}

#[derive(Clone)]
pub struct PalletCallWeight {
	// FAIL-CI rename
	pub weight_info: syn::Type,
	pub span: proc_macro2::Span,
}

impl PalletStructAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::GenerateStore { span, .. } |
			Self::WithoutStorageInfoTrait(span) |
			Self::StorageVersion { span, .. } |
			Self::CallWeight(PalletCallWeight { span, .. }) => *span,
		}
	}
}

impl syn::parse::Parse for PalletStructAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::generate_store) {
			content.parse::<keyword::generate_store>()?;
			let generate_content;
			syn::parenthesized!(generate_content in content);
			let vis = generate_content.parse::<syn::Visibility>()?;
			generate_content.parse::<syn::Token![trait]>()?;
			let keyword = generate_content.parse::<keyword::Store>()?;
			let span = content.span();
			Ok(Self::GenerateStore { vis, keyword, span })
		} else if lookahead.peek(keyword::without_storage_info) {
			let span = content.parse::<keyword::without_storage_info>()?.span();
			Ok(Self::WithoutStorageInfoTrait(span))
		} else if lookahead.peek(keyword::storage_version) {
			let span = content.parse::<keyword::storage_version>()?.span();

			let version_content;
			syn::parenthesized!(version_content in content);
			let storage_version = version_content.parse::<syn::Path>()?;

			Ok(Self::StorageVersion { storage_version, span })
		} else if lookahead.peek(keyword::call_weight) {
			let span = content.parse::<keyword::call_weight>().expect("peeked").span();
			let attr_content;
			syn::parenthesized!(attr_content in content);
			attr_content.parse::<syn::Token![trait]>()?;
			let weight_info = attr_content.parse::<syn::Type>()?;

			Ok(Self::CallWeight(PalletCallWeight { weight_info, span }))
		} else {
			Err(lookahead.error())
		}
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
			return Err(syn::Error::new(item.span(), msg))
		};

		let mut store = None;
		let mut without_storage_info = None;
		let mut storage_version_found = None;
		let mut call_weight = None;

		let struct_attrs: Vec<PalletStructAttr> = helper::take_item_pallet_attrs(&mut item.attrs)?;
		for attr in struct_attrs {
			match attr {
				PalletStructAttr::GenerateStore { vis, keyword, span } if store.is_none() => {
					store = Some((vis, keyword, span));
				},
				PalletStructAttr::WithoutStorageInfoTrait(span)
					if without_storage_info.is_none() =>
				{
					without_storage_info = Some(span);
				},
				PalletStructAttr::StorageVersion { storage_version, .. }
					if storage_version_found.is_none() =>
				{
					storage_version_found = Some(storage_version);
				},
				PalletStructAttr::CallWeight(cw) if call_weight.is_none() => {
					call_weight = Some(cw);
				},
				attr => {
					let msg = "Unexpected duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg))
				},
			}
		}

		let pallet = syn::parse2::<keyword::Pallet>(item.ident.to_token_stream())?;

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::pallet, Pallet must be public";
			return Err(syn::Error::new(item.span(), msg))
		}

		if item.generics.where_clause.is_some() {
			let msg = "Invalid pallet::pallet, where clause not supported on Pallet declaration";
			return Err(syn::Error::new(item.generics.where_clause.span(), msg))
		}

		let instances =
			vec![helper::check_type_def_gen_no_bounds(&item.generics, item.ident.span())?];

		Ok(Self {
			index,
			instances,
			pallet,
			store,
			attr_span,
			without_storage_info,
			storage_version: storage_version_found,
			call_weight,
		})
	}
}
