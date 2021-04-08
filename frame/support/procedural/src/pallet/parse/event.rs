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
use frame_support_procedural_tools::clean_type_string;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(metadata);
	syn::custom_keyword!(Event);
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(generate_deposit);
	syn::custom_keyword!(deposit_event);
}

/// Definition for pallet event enum.
pub struct EventDef {
	/// The index of event item in pallet module.
	pub index: usize,
	/// The keyword Event used (contains span).
	pub event: keyword::Event,
	/// Event metadatas: `(name, args, docs)`.
	pub metadata: Vec<(syn::Ident, Vec<String>, Vec<syn::Lit>)>,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The kind of generic the type `Event` has.
	pub gen_kind: super::GenericKind,
	/// Whether the function `deposit_event` must be generated.
	pub deposit_event: Option<(syn::Visibility, proc_macro2::Span)>,
	/// Where clause used in event definition.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::event attribute.
	pub attr_span: proc_macro2::Span,
}

/// Attribute for Event: defines metadata name to use.
///
/// Syntax is:
/// * `#[pallet::metadata(SomeType = MetadataName, ...)]`
/// * `#[pallet::generate_deposit($vis fn deposit_event)]`
enum PalletEventAttr {
	Metadata {
		metadata: Vec<(syn::Type, String)>,
		// Span of the attribute
		span: proc_macro2::Span,
	},
	DepositEvent {
		fn_vis: syn::Visibility,
		// Span for the keyword deposit_event
		fn_span: proc_macro2::Span,
		// Span of the attribute
		span: proc_macro2::Span,
	},
}

impl PalletEventAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Metadata { span, .. } => *span,
			Self::DepositEvent { span, .. } => *span,
		}
	}
}

/// Parse for syntax `$Type = "$SomeString"`.
fn parse_event_metadata_element(
	input: syn::parse::ParseStream
) -> syn::Result<(syn::Type, String)> {
	let typ = input.parse::<syn::Type>()?;
	input.parse::<syn::Token![=]>()?;
	let ident = input.parse::<syn::LitStr>()?;
	Ok((typ, ident.value()))
}

impl syn::parse::Parse for PalletEventAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::metadata) {
			let span = content.parse::<keyword::metadata>()?.span();
			let metadata_content;
			syn::parenthesized!(metadata_content in content);

			let metadata = metadata_content
				.parse_terminated::<_, syn::Token![,]>(parse_event_metadata_element)?
				.into_pairs()
				.map(syn::punctuated::Pair::into_value)
				.collect();

			Ok(PalletEventAttr::Metadata { metadata, span })
		} else if lookahead.peek(keyword::generate_deposit) {
			let span = content.parse::<keyword::generate_deposit>()?.span();

			let generate_content;
			syn::parenthesized!(generate_content in content);
			let fn_vis = generate_content.parse::<syn::Visibility>()?;
			generate_content.parse::<syn::Token![fn]>()?;
			let fn_span = generate_content.parse::<keyword::deposit_event>()?.span();


			Ok(PalletEventAttr::DepositEvent { fn_vis, span, fn_span })
		} else {
			Err(lookahead.error())
		}
	}
}

struct PalletEventAttrInfo {
	metadata: Option<Vec<(syn::Type, String)>>,
	deposit_event: Option<(syn::Visibility, proc_macro2::Span)>,
}

impl PalletEventAttrInfo {
	fn from_attrs(attrs: Vec<PalletEventAttr>) -> syn::Result<Self> {
		let mut metadata = None;
		let mut deposit_event = None;
		for attr in attrs {
			match attr {
				PalletEventAttr::Metadata { metadata: m, .. } if metadata.is_none() =>
					metadata = Some(m),
				PalletEventAttr::DepositEvent { fn_vis, fn_span, .. } if deposit_event.is_none() =>
					deposit_event = Some((fn_vis, fn_span)),
				attr => {
					return Err(syn::Error::new(attr.span(), "Duplicate attribute"));
				}
			}
		}

		Ok(PalletEventAttrInfo { metadata, deposit_event })
	}
}

impl EventDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Enum(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::event, expected item enum"))
		};

		let event_attrs: Vec<PalletEventAttr> = helper::take_item_pallet_attrs(&mut item.attrs)?;
		let attr_info = PalletEventAttrInfo::from_attrs(event_attrs)?;
		let metadata = attr_info.metadata.unwrap_or_else(Vec::new);
		let deposit_event = attr_info.deposit_event;

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::event, `Error` must be public";
			return Err(syn::Error::new(item.span(), msg));
		}

		let where_clause = item.generics.where_clause.clone();

		let mut instances = vec![];
		// NOTE: Event is not allowed to be only generic on I because it is not supported
		// by construct_runtime.
		if let Some(u) = helper::check_type_def_optional_gen(&item.generics, item.ident.span())? {
			instances.push(u);
		} else {
			// construct_runtime only allow non generic event for non instantiable pallet.
			instances.push(helper::InstanceUsage {
				has_instance: false,
				span: item.ident.span(),
			})
		}

		let has_instance = item.generics.type_params().any(|t| t.ident == "I");
		let has_config = item.generics.type_params().any(|t| t.ident == "T");
		let gen_kind = super::GenericKind::from_gens(has_config, has_instance)
			.expect("Checked by `helper::check_type_def_optional_gen` above");

		let event = syn::parse2::<keyword::Event>(item.ident.to_token_stream())?;

		let metadata = item.variants.iter()
			.map(|variant| {
				let name = variant.ident.clone();
				let docs = helper::get_doc_literals(&variant.attrs);
				let args = variant.fields.iter()
					.map(|field| {
						metadata.iter().find(|m| m.0 == field.ty)
							.map(|m| m.1.clone())
							.unwrap_or_else(|| {
								clean_type_string(&field.ty.to_token_stream().to_string())
							})
					})
					.collect();

				(name, args, docs)
			})
			.collect();

		Ok(EventDef {
			attr_span,
			index,
			metadata,
			instances,
			deposit_event,
			event,
			gen_kind,
			where_clause,
		})
	}
}
