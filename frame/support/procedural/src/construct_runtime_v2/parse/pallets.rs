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

use syn::spanned::Spanned;

pub struct PalletDef {
	/// The name of the pallet, e.g.`System` in `System: frame_system`.
	pub name: syn::Ident,
	/// Optional attributes tagged right above a pallet declaration.
	pub attrs: Vec<syn::Attribute>,
	/// Optional fixed index, e.g. `MyPallet ...  = 3,`.
	pub index: Option<u8>,
	/// The path of the pallet, e.g. `frame_system` in `System: frame_system`.
	pub path: PalletPath,
	/// The instance of the pallet, e.g. `Instance1` in `Council: pallet_collective::<Instance1>`.
	pub instance: Option<syn::Ident>,
}

/// A struct representing a path to a pallet. `PalletPath` is almost identical to the standard
/// Rust path with a few restrictions:
/// - No leading colons allowed
/// - Path segments can only consist of identifers separated by colons
#[derive(Debug, Clone)]
pub struct PalletPath {
	pub inner: syn::Path,
}

// /// The possible declaration of pallet parts to use.
// #[derive(Debug, Clone)]
// pub enum SpecifiedParts {
// 	/// Use all the pallet parts except those specified.
// 	Exclude(Vec<PalletPartNoGeneric>),
// 	/// Use only the specified pallet parts.
// 	Use(Vec<PalletPartNoGeneric>),
// 	/// Use the all the pallet parts.
// 	All,
// }

// impl PalletDef {
// 	pub fn try_from(
// 		attr_span: proc_macro2::Span,
// 		index: usize,
// 		item: &mut syn::Item,
// 	) -> syn::Result<Self> {
// 		let attrs = input.call(Attribute::parse_outer)?;

// 		let name = input.parse()?;
// 		let _: Token![:] = input.parse()?;
// 		let path = input.parse()?;

// 		// Parse for instance.
// 		let instance = if input.peek(Token![::]) && input.peek3(Token![<]) {
// 			let _: Token![::] = input.parse()?;
// 			let _: Token![<] = input.parse()?;
// 			let res = Some(input.parse()?);
// 			let _: Token![>] = input.parse()?;
// 			res
// 		} else if !(input.peek(Token![::]) && input.peek3(token::Brace)) &&
// 			!input.peek(keyword::exclude_parts) &&
// 			!input.peek(keyword::use_parts) &&
// 			!input.peek(Token![=]) &&
// 			!input.peek(Token![,]) &&
// 			!input.is_empty()
// 		{
// 			return Err(input.error(
// 				"Unexpected tokens, expected one of `::$ident` `::{`, `exclude_parts`, `use_parts`, `=`, `,`",
// 			));
// 		} else {
// 			None
// 		};

// 		// Parse for explicit parts
// 		let pallet_parts = if input.peek(Token![::]) && input.peek3(token::Brace) {
// 			let _: Token![::] = input.parse()?;
// 			// Some(parse_pallet_parts(input)?)
// 		} else if !input.peek(keyword::exclude_parts) &&
// 			!input.peek(keyword::use_parts) &&
// 			!input.peek(Token![=]) &&
// 			!input.peek(Token![,]) &&
// 			!input.is_empty()
// 		{
// 			return Err(input.error(
// 				"Unexpected tokens, expected one of `::{`, `exclude_parts`, `use_parts`, `=`, `,`",
// 			))
// 		} else {
// 			None
// 		};

// 		// Parse for specified parts
// 		let specified_parts = if input.peek(keyword::exclude_parts) {
// 			let _: keyword::exclude_parts = input.parse()?;
// 			// SpecifiedParts::Exclude(parse_pallet_parts_no_generic(input)?)
// 		} else if input.peek(keyword::use_parts) {
// 			let _: keyword::use_parts = input.parse()?;
// 			// SpecifiedParts::Use(parse_pallet_parts_no_generic(input)?)
// 		} else if !input.peek(Token![=]) && !input.peek(Token![,]) && !input.is_empty() {
// 			return Err(input.error("Unexpected tokens, expected one of `exclude_parts`, `=`, `,`"))
// 		} else {
// 			SpecifiedParts::All
// 		};

// 		// Parse for pallet index
// 		let index = if input.peek(Token![=]) {
// 			input.parse::<Token![=]>()?;
// 			let index = input.parse::<syn::LitInt>()?;
// 			let index = index.base10_parse::<u8>()?;
// 			Some(index)
// 		} else if !input.peek(Token![,]) && !input.is_empty() {
// 			return Err(input.error("Unexpected tokens, expected one of `=`, `,`"))
// 		} else {
// 			None
// 		};

// 		Ok(Self { attrs, name, path, instance, pallet_parts, specified_parts, index })
// 	}
// }

pub struct AllPalletsDef {
	pub ident: syn::Ident,
	pub pallets: Vec<PalletDef>,
}

impl AllPalletsDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Struct(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid frame::pallets, expect item struct."))
		};

		println!("item: {:?}", item);

		Ok(Self {
			ident: item.ident.clone(),
			pallets: vec![]
		})
	}
}