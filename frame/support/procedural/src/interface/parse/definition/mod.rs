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

mod call;
mod selector;
mod view;

use frame_support_procedural_tools::generate_crate_access_2018;
use quote::ToTokens;
use syn::spanned::Spanned;

pub struct InterfaceDef {
	index: usize,
	item: syn::ItemTrait,
	selectors: Option<selector::SelectorDef>,
	views: Option<view::ViewDef>,
	calls: Option<call::CallDef>,
	unrelated: Option<Vec<(usize, syn::TraitItem)>>,
}

impl InterfaceDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Trait(item) = item {
			item
		} else {
			return Err(syn::Error::new(
				attr_span,
				"Invalid #[interface::definition], expected item trait",
			))
		};

		let frame_support = generate_crate_access_2018("frame-support")?;
		let has_frame_suppert_core_supertrait = item.supertraits.iter().any(|s| {
			syn::parse2::<CoreBoundParse>(s.to_token_stream())
				.map_or(false, |b| b.0 == frame_support)
		});
		if !has_frame_suppert_core_supertrait {
			let found = if item.supertraits.is_empty() {
				"none".to_string()
			} else {
				let mut found = item
					.supertraits
					.iter()
					.fold(String::new(), |acc, s| format!("{}`{}`, ", acc, quote::quote!(#s)));
				found.pop();
				found.pop();
				found
			};

			let msg = format!(
				"Invalid interface::trait, expected explicit `{}::interface::Core` as supertrait, \
				found {}. \
				(try `pub trait {}: frame_support::interface::Config)",
				frame_support, found, item.ident
			);
			return Err(syn::Error::new(attr_span, msg))
		}

		// Ensure no generics on interface trait
		let item_span = item.span();
		if !item.generics.params.is_empty() {
			// TODO: Where clauses should be allowed. We can carry them to all impl blocks.
			//       But "extending" an interface gets harder, as carrying them over from
			//       extended traits is harder.
			let msg = "Invalid Interface definition. Traits that define an interface \
                currently can not have generics.";
			return Err(syn::Error::new(item_span, msg))
		}

		let mut with_selector = false;
		super::helper::take_first_item_interface_attr::<InterfaceTraitAttr>(item)?.map(|attr| {
			match attr {
				InterfaceTraitAttr::WithSelector(span) => {
					with_selector = true;
				},
				_ => (),
			}
		});

		let mut selectors = None;
		let mut views = None;
		let mut calls = None;
		let mut unrelated: Option<Vec<(usize, syn::TraitItem)>> = None;

		for (index, item) in item.items.iter_mut().enumerate() {
			let interface_attr: Option<InterfaceTraitAttr> =
				super::helper::take_first_item_interface_attr(item)?;

			match interface_attr {
				Some(InterfaceTraitAttr::Call(span)) =>
					calls = Some(call::CallDef::try_from(calls, with_selector, span, index, item)?),
				Some(InterfaceTraitAttr::View(span)) =>
					views = Some(view::ViewDef::try_from(views, with_selector, span, index, item)?),
				Some(InterfaceTraitAttr::Selector(span)) =>
					selectors = Some(selector::SelectorDef::try_from(span, index, item)?),
				Some(InterfaceTraitAttr::WithSelector(_)) => {
					let msg = "Invalid interface definition. #[interface::with_selector] is \
						only allowed as an annotation at the trait of the interface.";
					return Err(syn::Error::new(attr_span, msg))
				},
				None => {
					unrelated = Some(unrelated.map_or_else(
						|| Vec::new(),
						|mut v| {
							v.push((index, item.clone()));
							v
						},
					));
				},
			}
		}

		if with_selector && selectors.is_none() {
			let msg = "Invalid interface definition. Expected one trait annotated \
				with #[interface::selector] or #[selector].";
			return Err(syn::Error::new(item_span, msg))
		}

		Ok(InterfaceDef { index, item: item.clone(), calls, views, selectors, unrelated })
	}
}

/// Parse for `$ident::interface::Core`
pub struct CoreBoundParse(syn::Ident);

impl syn::parse::Parse for CoreBoundParse {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let ident = input.parse::<syn::Ident>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::interface>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::Core>()?;

		if input.peek(syn::token::Lt) {
			input.parse::<syn::AngleBracketedGenericArguments>()?;
		}

		Ok(Self(ident))
	}
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(with_selector);
	syn::custom_keyword!(selector);
	syn::custom_keyword!(Core);
	syn::custom_keyword!(call);
	syn::custom_keyword!(view);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::call]`)
enum InterfaceTraitAttr {
	Call(proc_macro2::Span),
	View(proc_macro2::Span),
	Selector(proc_macro2::Span),
	WithSelector(proc_macro2::Span),
}

impl InterfaceTraitAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Call(span) => *span,
			Self::View(span) => *span,
			Self::Selector(span) => *span,
			Self::WithSelector(span) => *span,
		}
	}
}

impl syn::parse::Parse for InterfaceTraitAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::call) {
			Ok(InterfaceTraitAttr::Call(content.parse::<keyword::call>()?.span()))
		} else if lookahead.peek(keyword::view) {
			Ok(InterfaceTraitAttr::View(content.parse::<keyword::view>()?.span()))
		} else if lookahead.peek(keyword::selector) {
			Ok(InterfaceTraitAttr::Selector(content.parse::<keyword::selector>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}
