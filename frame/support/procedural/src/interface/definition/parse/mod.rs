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

mod definition;
mod error;
mod event;

pub use definition::InterfaceDef;
pub use error::ErrorDef;
pub use event::EventDef;
use frame_support_procedural_tools::generate_crate_access_2018;
use syn::spanned::Spanned;

pub struct Def {
	pub item: syn::ItemMod,
	pub interface: InterfaceDef,
	pub error: Option<ErrorDef>,
	pub event: Option<EventDef>,
	pub frame_support: syn::Ident,
	pub frame_system: syn::Ident,
	pub sp_core: syn::Ident,
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

		let frame_support = generate_crate_access_2018("frame-support")?;
		let frame_system = generate_crate_access_2018("frame-system")?;
		let sp_core = generate_crate_access_2018("sp-core")?;
		let mut interface = None;
		let mut error = None;
		let mut event = None;

		for (index, item) in items.iter_mut().enumerate() {
			let interface_attr: Option<InterfaceAttr> =
				crate::interface::helper::take_first_item_interface_attr(item)?;

			match interface_attr {
				Some(InterfaceAttr::Definition(span)) if interface.is_none() => {
					interface = Some(InterfaceDef::try_from(
						span,
						index,
						item,
						frame_support.clone(),
						frame_system.clone(),
					)?)
				},
				Some(InterfaceAttr::Event(span)) if event.is_none() => {
					event = Some(EventDef::try_from(span, index, item)?);
				},
				Some(InterfaceAttr::Error(span)) if error.is_none() => {
					error = Some(ErrorDef::try_from(span, index, item)?);
				},
				Some(attr) => {
					let msg = "Invalid duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg));
				},
				None => (),
			}
		}

		let interface = interface.ok_or_else(|| {
			let msg = "Invalid interface definition. Expected one trait annotated \
				with #[interface::definition] or #[definition].";
			syn::Error::new(item_span, msg)
		})?;

		Ok(Def { item, interface, error, event, frame_support, frame_system, sp_core })
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
		if lookahead.peek(keyword::error) {
			Ok(InterfaceAttr::Error(content.parse::<keyword::error>()?.span()))
		} else if lookahead.peek(keyword::event) {
			Ok(InterfaceAttr::Event(content.parse::<keyword::event>()?.span()))
		} else if lookahead.peek(keyword::definition) {
			Ok(InterfaceAttr::Definition(content.parse::<keyword::definition>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}
