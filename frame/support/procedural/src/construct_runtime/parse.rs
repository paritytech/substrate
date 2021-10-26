// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use frame_support_procedural_tools::syn_ext as ext;
use proc_macro2::{Span, TokenStream};
use std::collections::HashSet;
use syn::{
	ext::IdentExt,
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	spanned::Spanned,
	token, Error, Ident, Path, PathArguments, PathSegment, Result, Token,
};

mod keyword {
	syn::custom_keyword!(Block);
	syn::custom_keyword!(NodeBlock);
	syn::custom_keyword!(UncheckedExtrinsic);
	syn::custom_keyword!(Pallet);
	syn::custom_keyword!(Call);
	syn::custom_keyword!(Storage);
	syn::custom_keyword!(Event);
	syn::custom_keyword!(Config);
	syn::custom_keyword!(Origin);
	syn::custom_keyword!(Inherent);
	syn::custom_keyword!(ValidateUnsigned);
}

#[derive(Debug)]
pub struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_section: WhereSection,
	pub pallets: ext::Braces<ext::Punctuated<PalletDeclaration, Token![,]>>,
}

impl Parse for RuntimeDefinition {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(Self {
			visibility_token: input.parse()?,
			enum_token: input.parse()?,
			name: input.parse()?,
			where_section: input.parse()?,
			pallets: input.parse()?,
		})
	}
}

#[derive(Debug)]
pub struct WhereSection {
	pub block: syn::TypePath,
	pub node_block: syn::TypePath,
	pub unchecked_extrinsic: syn::TypePath,
}

impl Parse for WhereSection {
	fn parse(input: ParseStream) -> Result<Self> {
		input.parse::<token::Where>()?;
		let mut definitions = Vec::new();
		while !input.peek(token::Brace) {
			let definition: WhereDefinition = input.parse()?;
			definitions.push(definition);
			if !input.peek(Token![,]) {
				if !input.peek(token::Brace) {
					return Err(input.error("Expected `,` or `{`"))
				}
				break
			}
			input.parse::<Token![,]>()?;
		}
		let block = remove_kind(input, WhereKind::Block, &mut definitions)?.value;
		let node_block = remove_kind(input, WhereKind::NodeBlock, &mut definitions)?.value;
		let unchecked_extrinsic =
			remove_kind(input, WhereKind::UncheckedExtrinsic, &mut definitions)?.value;
		if let Some(WhereDefinition { ref kind_span, ref kind, .. }) = definitions.first() {
			let msg = format!(
				"`{:?}` was declared above. Please use exactly one declaration for `{:?}`.",
				kind, kind
			);
			return Err(Error::new(*kind_span, msg))
		}
		Ok(Self { block, node_block, unchecked_extrinsic })
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum WhereKind {
	Block,
	NodeBlock,
	UncheckedExtrinsic,
}

#[derive(Debug)]
pub struct WhereDefinition {
	pub kind_span: Span,
	pub kind: WhereKind,
	pub value: syn::TypePath,
}

impl Parse for WhereDefinition {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		let (kind_span, kind) = if lookahead.peek(keyword::Block) {
			(input.parse::<keyword::Block>()?.span(), WhereKind::Block)
		} else if lookahead.peek(keyword::NodeBlock) {
			(input.parse::<keyword::NodeBlock>()?.span(), WhereKind::NodeBlock)
		} else if lookahead.peek(keyword::UncheckedExtrinsic) {
			(input.parse::<keyword::UncheckedExtrinsic>()?.span(), WhereKind::UncheckedExtrinsic)
		} else {
			return Err(lookahead.error())
		};

		Ok(Self {
			kind_span,
			kind,
			value: {
				let _: Token![=] = input.parse()?;
				input.parse()?
			},
		})
	}
}

#[derive(Debug, Clone)]
pub struct PalletDeclaration {
	pub name: Ident,
	/// Optional fixed index (e.g. `MyPallet ...  = 3,`)
	pub index: Option<u8>,
	pub path: PalletPath,
	pub instance: Option<Ident>,
	pub pallet_parts: Vec<PalletPart>,
}

impl Parse for PalletDeclaration {
	fn parse(input: ParseStream) -> Result<Self> {
		let name = input.parse()?;
		let _: Token![:] = input.parse()?;
		let path = input.parse()?;
		let instance = if input.peek(Token![<]) {
			let _: Token![<] = input.parse()?;
			let res = Some(input.parse()?);
			let _: Token![>] = input.parse()?;
			let _: Token![::] = input.parse()?;
			res
		} else {
			None
		};

		let pallet_parts = parse_pallet_parts(input)?;

		let index = if input.peek(Token![=]) {
			input.parse::<Token![=]>()?;
			let index = input.parse::<syn::LitInt>()?;
			let index = index.base10_parse::<u8>()?;
			Some(index)
		} else {
			None
		};

		let parsed = Self { name, path, instance, pallet_parts, index };

		Ok(parsed)
	}
}

/// A struct representing a path to a pallet. `PalletPath` is almost identical to the standard
/// Rust path with a few restrictions:
/// - No leading colons allowed
/// - Path segments can only consist of identifers; angle-bracketed or parenthesized segments will
///   result in a parsing error (except when specifying instances)
#[derive(Debug, Clone)]
pub struct PalletPath {
	pub inner: Path,
}

impl PalletPath {
	pub fn module_name(&self) -> String {
		self.inner.segments.iter().fold(String::new(), |mut acc, segment| {
			if !acc.is_empty() {
				acc.push_str("::");
			}
			acc.push_str(&segment.ident.to_string());
			acc
		})
	}
}

impl Parse for PalletPath {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut lookahead = input.lookahead1();
		let mut segments = Punctuated::new();

		if lookahead.peek(Token![crate]) ||
			lookahead.peek(Token![self]) ||
			lookahead.peek(Token![super]) ||
			lookahead.peek(Ident)
		{
			let ident = input.call(Ident::parse_any)?;
			segments.push(PathSegment { ident, arguments: PathArguments::None });
			let _: Token![::] = input.parse()?;
			lookahead = input.lookahead1();
		} else {
			return Err(lookahead.error())
		}

		while lookahead.peek(Ident) {
			let ident = input.parse()?;
			segments.push(PathSegment { ident, arguments: PathArguments::None });
			let _: Token![::] = input.parse()?;
			lookahead = input.lookahead1();
		}

		if !lookahead.peek(token::Brace) && !lookahead.peek(Token![<]) {
			return Err(lookahead.error())
		}

		Ok(Self { inner: Path { leading_colon: None, segments } })
	}
}

impl quote::ToTokens for PalletPath {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.inner.to_tokens(tokens);
	}
}

/// Parse [`PalletPart`]'s from a braces enclosed list that is split by commas, e.g.
///
/// `{ Call, Event }`
fn parse_pallet_parts(input: ParseStream) -> Result<Vec<PalletPart>> {
	let pallet_parts: ext::Braces<ext::Punctuated<PalletPart, Token![,]>> = input.parse()?;

	let mut resolved = HashSet::new();
	for part in pallet_parts.content.inner.iter() {
		if !resolved.insert(part.name()) {
			let msg = format!(
				"`{}` was already declared before. Please remove the duplicate declaration",
				part.name(),
			);
			return Err(Error::new(part.keyword.span(), msg))
		}
	}

	Ok(pallet_parts.content.inner.into_iter().collect())
}

#[derive(Debug, Clone)]
pub enum PalletPartKeyword {
	Pallet(keyword::Pallet),
	Call(keyword::Call),
	Storage(keyword::Storage),
	Event(keyword::Event),
	Config(keyword::Config),
	Origin(keyword::Origin),
	Inherent(keyword::Inherent),
	ValidateUnsigned(keyword::ValidateUnsigned),
}

impl Parse for PalletPartKeyword {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();

		if lookahead.peek(keyword::Pallet) {
			Ok(Self::Pallet(input.parse()?))
		} else if lookahead.peek(keyword::Call) {
			Ok(Self::Call(input.parse()?))
		} else if lookahead.peek(keyword::Storage) {
			Ok(Self::Storage(input.parse()?))
		} else if lookahead.peek(keyword::Event) {
			Ok(Self::Event(input.parse()?))
		} else if lookahead.peek(keyword::Config) {
			Ok(Self::Config(input.parse()?))
		} else if lookahead.peek(keyword::Origin) {
			Ok(Self::Origin(input.parse()?))
		} else if lookahead.peek(keyword::Inherent) {
			Ok(Self::Inherent(input.parse()?))
		} else if lookahead.peek(keyword::ValidateUnsigned) {
			Ok(Self::ValidateUnsigned(input.parse()?))
		} else {
			Err(lookahead.error())
		}
	}
}

impl PalletPartKeyword {
	/// Returns the name of `Self`.
	fn name(&self) -> &'static str {
		match self {
			Self::Pallet(_) => "Pallet",
			Self::Call(_) => "Call",
			Self::Storage(_) => "Storage",
			Self::Event(_) => "Event",
			Self::Config(_) => "Config",
			Self::Origin(_) => "Origin",
			Self::Inherent(_) => "Inherent",
			Self::ValidateUnsigned(_) => "ValidateUnsigned",
		}
	}

	/// Returns `true` if this pallet part is allowed to have generic arguments.
	fn allows_generic(&self) -> bool {
		Self::all_generic_arg().iter().any(|n| *n == self.name())
	}

	/// Returns the names of all pallet parts that allow to have a generic argument.
	fn all_generic_arg() -> &'static [&'static str] {
		&["Event", "Origin", "Config"]
	}
}

impl Spanned for PalletPartKeyword {
	fn span(&self) -> Span {
		match self {
			Self::Pallet(inner) => inner.span(),
			Self::Call(inner) => inner.span(),
			Self::Storage(inner) => inner.span(),
			Self::Event(inner) => inner.span(),
			Self::Config(inner) => inner.span(),
			Self::Origin(inner) => inner.span(),
			Self::Inherent(inner) => inner.span(),
			Self::ValidateUnsigned(inner) => inner.span(),
		}
	}
}

#[derive(Debug, Clone)]
pub struct PalletPart {
	pub keyword: PalletPartKeyword,
	pub generics: syn::Generics,
}

impl Parse for PalletPart {
	fn parse(input: ParseStream) -> Result<Self> {
		let keyword: PalletPartKeyword = input.parse()?;

		let generics: syn::Generics = input.parse()?;
		if !generics.params.is_empty() && !keyword.allows_generic() {
			let valid_generics = PalletPart::format_names(PalletPartKeyword::all_generic_arg());
			let msg = format!(
				"`{}` is not allowed to have generics. \
				 Only the following pallets are allowed to have generics: {}.",
				keyword.name(),
				valid_generics,
			);
			return Err(syn::Error::new(keyword.span(), msg))
		}

		Ok(Self { keyword, generics })
	}
}

impl PalletPart {
	pub fn format_names(names: &[&'static str]) -> String {
		let res: Vec<_> = names.iter().map(|s| format!("`{}`", s)).collect();
		res.join(", ")
	}

	/// The name of this pallet part.
	pub fn name(&self) -> &'static str {
		self.keyword.name()
	}
}

fn remove_kind(
	input: ParseStream,
	kind: WhereKind,
	definitions: &mut Vec<WhereDefinition>,
) -> Result<WhereDefinition> {
	if let Some(pos) = definitions.iter().position(|d| d.kind == kind) {
		Ok(definitions.remove(pos))
	} else {
		let msg = format!(
			"Missing associated type for `{:?}`. Add `{:?}` = ... to where section.",
			kind, kind
		);
		Err(input.error(msg))
	}
}
