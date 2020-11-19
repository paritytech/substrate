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

use super::helper;
use syn::spanned::Spanned;
use quote::ToTokens;

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
	/// If event is declared with instance.
	pub has_instance: bool,
	/// If event is declared with generics.
	pub is_generic: bool,
	/// Whether the function `deposit_event` must be generated.
	pub deposit_event: Option<(syn::Visibility, proc_macro2::Span)>,
	/// Where clause used in event definition.
	pub where_clause: Option<syn::WhereClause>,
}

impl EventDef {
	/// Return the generic to be used when using Event type
	///
	/// Depending on its definition it can be: ``, `T` or `T, I`
	pub fn event_use_gen(&self) -> proc_macro2::TokenStream {
		if self.is_generic {
			if self.has_instance {
				quote::quote!(T, I)
			} else {
				quote::quote!(T)
			}
		} else {
			quote::quote!()
		}
	}

	/// Return the generic to be used in `impl<..>` when implementing on Event type.
	pub fn event_impl_gen(&self) -> proc_macro2::TokenStream {
		if self.is_generic {
			if self.has_instance {
				quote::quote!(T: Config<I>, I)
			} else {
				quote::quote!(T: Config)
			}
		} else {
			quote::quote!()
		}
	}
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
			Self::Metadata { span, .. } => span.clone(),
			Self::DepositEvent { span, .. } => span.clone(),
		}
	}
}

/// Parse for syntax `$Type = "$SomeString"`.
fn parse_event_metadata_element(input: syn::parse::ParseStream) -> syn::Result<(syn::Type, String)> {
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
	pub fn try_from(index: usize, item: &mut syn::Item) -> syn::Result<Self> {
		let item = if let syn::Item::Enum(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::event, expect item enum"))
		};

		let event_attrs: Vec<PalletEventAttr> = helper::take_item_attrs(&mut item.attrs)?;
		let attr_info = PalletEventAttrInfo::from_attrs(event_attrs)?;
		let metadata = attr_info.metadata.unwrap_or_else(|| vec![]);
		let deposit_event = attr_info.deposit_event;

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::event, `Error` must be public";
			return Err(syn::Error::new(item.span(), msg));
		}

		let where_clause = item.generics.where_clause.clone();
		let has_instance = item.generics.params.len() == 2;
		let is_generic = item.generics.params.len() > 0;

		let mut instances = vec![];
		if let Some(u) = helper::check_type_def_optional_gen(&item.generics, item.ident.span())? {
			instances.push(u);
		} else {
			// construct_runtime only allow generic event for instantiable pallet.
			instances.push(helper::InstanceUsage {
				has_instance: false,
				span: item.ident.span(),
			})
		}

		let event = syn::parse2::<keyword::Event>(item.ident.to_token_stream())?;

		let metadata = item.variants.iter()
			.map(|variant| {
				let name = variant.ident.clone();
				let docs = helper::get_doc_literals(&variant.attrs);
				let args = variant.fields.iter()
					.map(|field| {
						metadata.iter().find(|m| m.0 == field.ty)
							.map(|m| m.1.clone())
							.or_else(|| {
								if let syn::Type::Path(p) = &field.ty {
									p.path.segments.last().map(|s| format!("{}", s.ident))
								} else {
									None
								}
							})
							.ok_or_else(|| {
								let msg = "Invalid pallet::event, type can't be parsed for \
									metadata, must be either a path type (and thus last \
									segments ident is metadata) or match a type in the \
									metadata attributes";
								syn::Error::new(field.span(), msg)
							})
					})
					.collect::<syn::Result<_>>()?;

				Ok((name, args, docs))
			})
			.collect::<syn::Result<_>>()?;

		Ok(EventDef {
			index,
			metadata,
			instances,
			has_instance,
			deposit_event,
			event,
			is_generic,
			where_clause,
		})
	}
}
