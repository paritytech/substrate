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

pub mod helper;
pub mod pallet;
pub mod pallet_decl;
pub mod pallets;
pub mod runtime_struct;
pub mod runtime_types;

use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use syn::{spanned::Spanned, Token};

use frame_support_procedural_tools::syn_ext as ext;
use runtime_types::RuntimeType;

mod keyword {
	syn::custom_keyword!(frame);
	syn::custom_keyword!(runtime);
	syn::custom_keyword!(pallets);
	syn::custom_keyword!(derive);
}

enum RuntimeAttr {
	Runtime(proc_macro2::Span),
	Pallets(proc_macro2::Span),
	Derive(proc_macro2::Span, Vec<RuntimeType>),
}

impl RuntimeAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Runtime(span) => *span,
			Self::Pallets(span) => *span,
			Self::Derive(span, _) => *span,
		}
	}
}

impl syn::parse::Parse for RuntimeAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::frame>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::runtime) {
			Ok(RuntimeAttr::Runtime(content.parse::<keyword::runtime>()?.span()))
		} else if lookahead.peek(keyword::pallets) {
			Ok(RuntimeAttr::Pallets(content.parse::<keyword::pallets>()?.span()))
		} else if lookahead.peek(keyword::derive) {
			let _ = content.parse::<keyword::derive>();
			let derive_content;
			syn::parenthesized!(derive_content in content);
			let runtime_types =
				derive_content.parse::<ext::Punctuated<RuntimeType, Token![,]>>()?;
			let runtime_types = runtime_types.inner.into_iter().collect();
			Ok(RuntimeAttr::Derive(derive_content.span(), runtime_types))
		} else {
			Err(lookahead.error())
		}
	}
}

pub struct Def {
	pub input: TokenStream2,
	pub item: syn::ItemMod,
	pub runtime_struct: runtime_struct::RuntimeStructDef,
	pub pallets: pallets::AllPalletsDeclaration,
	pub runtime_types: Vec<RuntimeType>,
}

impl Def {
	pub fn try_from(mut item: syn::ItemMod) -> syn::Result<Self> {
		let input: TokenStream2 = item.to_token_stream().into();
		let item_span = item.span();
		let items = &mut item
			.content
			.as_mut()
			.ok_or_else(|| {
				let msg = "Invalid runtime definition, expected mod to be inlined.";
				syn::Error::new(item_span, msg)
			})?
			.1;

		let mut runtime_struct = None;
		let mut pallets = None;
		let mut runtime_types = None;

		for item in items.iter_mut() {
			while let Some(runtime_attr) =
				helper::take_first_item_runtime_attr::<RuntimeAttr>(item)?
			{
				match runtime_attr {
					RuntimeAttr::Runtime(span) if runtime_struct.is_none() => {
						let p = runtime_struct::RuntimeStructDef::try_from(span, item)?;
						runtime_struct = Some(p);
					},
					RuntimeAttr::Pallets(span) if pallets.is_none() => {
						let p = pallets::AllPalletsDeclaration::try_from(span, item)?;
						pallets = Some(p);
					},
					RuntimeAttr::Derive(_, types) if runtime_types.is_none() => {
						runtime_types = Some(types);
					},
					attr => {
						let msg = "Invalid duplicated attribute";
						return Err(syn::Error::new(attr.span(), msg))
					},
				}
			}
		}

		let def = Def {
			input,
			item,
			runtime_struct: runtime_struct
				.ok_or_else(|| syn::Error::new(item_span, "Missing `#[frame::runtime]`"))?,
			pallets: pallets
				.ok_or_else(|| syn::Error::new(item_span, "Missing `#[frame::pallets]`"))?,
			runtime_types: runtime_types
				.ok_or_else(|| syn::Error::new(item_span, "Missing `#[frame::runtime_types]`"))?,
		};

		Ok(def)
	}
}
