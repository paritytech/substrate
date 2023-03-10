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

mod error;
mod interface;
mod event;
mod selector;

use quote::ToTokens;
use syn::{spanned::Spanned, Generics, Item, Attribute};
pub use error::ErrorDef;
pub use event::EventDef;
pub use interface::InterfaceDef;

pub struct Def {
	item: syn::ItemMod,
	interface: InterfaceDef,
	error: Option<ErrorDef>,
	event: Option<EventDef>,
	unrelated: Option<Vec<(usize, Item)>>
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
					error = Some(ErrorDef::try_from(span, index, item)?);
				},
				Some(attr) => {
					let msg = "Invalid duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg))
				},
				None => unrelated.map_or_else(
					|| Vec::new(),
					|mut v| {
						v.push((index, item.clone()));
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


		Ok(Def {
			item,
			interface,
			error,
			event,
			unrelated
		})

	}
}

/// Take the first interface attribute (e.g. attribute like `#[interface..]`) and decode it to
/// `Attr`
fn take_first_item_interface_attr<Attr>(
	item: &mut Item,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = mut_item_attrs(item) { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path.segments.first().map_or(false, |segment| segment.ident == "interface")
	}) {
		let interface_attr = attrs.remove(index);
		Ok(Some(syn::parse2(interface_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

fn mut_item_attrs(item: &mut syn::Item) -> Option<&mut Vec<syn::Attribute>> {
		match item {
			Item::Const(item) => Some(item.attrs.as_mut()),
			Item::Enum(item) => Some(item.attrs.as_mut()),
			Item::ExternCrate(item) => Some(item.attrs.as_mut()),
			Item::Fn(item) => Some(item.attrs.as_mut()),
			Item::ForeignMod(item) => Some(item.attrs.as_mut()),
			Item::Impl(item) => Some(item.attrs.as_mut()),
			Item::Macro(item) => Some(item.attrs.as_mut()),
			Item::Macro2(item) => Some(item.attrs.as_mut()),
			Item::Mod(item) => Some(item.attrs.as_mut()),
			Item::Static(item) => Some(item.attrs.as_mut()),
			Item::Struct(item) => Some(item.attrs.as_mut()),
			Item::Trait(item) => Some(item.attrs.as_mut()),
			Item::TraitAlias(item) => Some(item.attrs.as_mut()),
			Item::Type(item) => Some(item.attrs.as_mut()),
			Item::Union(item) => Some(item.attrs.as_mut()),
			Item::Use(item) => Some(item.attrs.as_mut()),
			_ => None,
		}
	}
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
