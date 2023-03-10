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

use syn::{spanned::Spanned, Generics, Item};

pub struct InterfaceDef {
	item: syn::ItemTrait,
	selectors: Option<SelectorDef>,
	views: Option<Vec<ViewDef>>,
	calls: Option<Vec<CallDef>>,
}

impl InterfaceDef {
	fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		// Ensure NO generics or where clauses on interface trait
		let item_span = item.span();
		if !item.generics == Generics::default() {
			// TODO: Where clauses should be allowed. We can carry them to all impl blocks.
			//       But "extending" an interface gets harder, as carrying them over from
			//       extended traits is harder.
			let msg = "Invalid Interface definition. Traits that define an interface \
                currently can not have generics or where clauses.";
			return Err(syn::Error::new(item_span, msg))
		}

		// Filter selector methods
		let with_selector = false;

		// Filter view methods

		// Filter call methods
		todo!()
	}
}

struct SelectorDef {
	default: SingleSelectorDef,
	others: Option<Vec<SingleSelectorDef>>,
}

impl SelectorDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}

struct SingleSelectorDef {
	item: syn::TraitItemMethod,
	name: syn::Ident,
}

impl SingleSelectorDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}

struct ViewDef {
	views: Vec<syn::TraitItemMethod>,
}

impl ViewDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}

struct CallDef {
	calls: Vec<syn::TraitItemMethod>,
}

impl CallDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}

pub struct Def {
	item: syn::ItemMod,
	interface: InterfaceDef,
	error: Option<ErrorDef>,
	event: Option<EventDef>,
}

impl Def {
	pub fn try_from(mut item: syn::ItemMod) -> syn::Result<Self> {
		let item_span = item.span();
		let items = &mut item
			.content
			.as_mut()
			.ok_or_else(|| {
				let msg = "Invalid interface definition, expected mod to be inlined.";
				syn::Error::new(item_span, msg)
			})?
			.1;

		let mut interface = None;
		let mut error = None;
		let mut event = None;
		let mut unrelated: Option<Vec<(usize, Item)>> = None;

		for (index, item) in items.iter_mut().enumerate() {
			let interface_attr: Option<InterfaceAttr> = take_first_item_interface_attr(item)?;

			match interface_attr {
				Some(InterfaceAttr::Definition(span)) if interface.is_none() =>
					interface = Some(InterfaceDef::try_from(span, index, item)?),
				Some(InterfaceAttr::Event(span)) if event.is_none() => {
					event = Some(EventDef::try_from(span, index, item)?);
				},
				Some(InterfaceAttr::Error(span)) if error.is_none() => {
					event = Some(ErrorDef::try_from(span, index, item)?);
				},
				Some(attr) => {
					let msg = "Invalid duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg))
				},
				None => unrelated.map_or_else(
					|| Vec::new(),
					|mut v| {
						v.push((index, item));
						v
					},
				),
			}
		}

		let interface = interface.ok_or_else(|| {
			let msg = "Invalid interface definition. Expected one trait annotated \
				with #[interface::definition] or #[definition].";
			syn::Error::new(item_span, msg)
		})?;

		todo!()
	}
}

/// Take the first interface attribute (e.g. attribute like `#[interface..]`) and decode it to
/// `Attr`
pub fn take_first_item_interface_attr<Attr>(
	item: &mut impl MutItemAttrs,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = item.mut_item_attrs() { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path.segments.first().map_or(false, |segment| segment.ident == "interface")
	}) {
		let interface_attr = attrs.remove(index);
		Ok(Some(syn::parse2(interface_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(definition);
	syn::custom_keyword!(error);
	syn::custom_keyword!(event);
}

/// Parse attributes for item in pallet module
/// syntax must be `interface::` (e.g. `#[interface::definition]`)
enum InterfaceAttr {
	Definition(proc_macro2::Span),
	Error(proc_macro2::Span),
	Event(proc_macro2::Span),
}

impl InterfaceAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Error(span) => *span,
			Self::Event(span) => *span,
			Self::Definition(span) => *span,
		}
	}
}

impl syn::parse::Parse for InterfaceAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::config) {
			Ok(PalletAttr::Error(content.parse::<keyword::event>()?.span()))
		} else if lookahead.peek(keyword::pallet) {
			Ok(PalletAttr::Event(content.parse::<keyword::error>()?.span()))
		} else if lookahead.peek(keyword::hooks) {
			Ok(PalletAttr::Definition(content.parse::<keyword::definition>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}
