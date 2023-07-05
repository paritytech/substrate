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

use frame_support_procedural_tools::syn_ext as ext;
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::{
	ext::IdentExt,
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	spanned::Spanned,
	token, Attribute, Error, Ident, Path, Result, Token,
};

mod keyword {
	syn::custom_keyword!(Block);
	syn::custom_keyword!(NodeBlock);
	syn::custom_keyword!(UncheckedExtrinsic);
	syn::custom_keyword!(Pallet);
	syn::custom_keyword!(Call);
	syn::custom_keyword!(Storage);
	syn::custom_keyword!(Event);
	syn::custom_keyword!(Error);
	syn::custom_keyword!(Config);
	syn::custom_keyword!(Origin);
	syn::custom_keyword!(Inherent);
	syn::custom_keyword!(ValidateUnsigned);
	syn::custom_keyword!(FreezeReason);
	syn::custom_keyword!(HoldReason);
	syn::custom_keyword!(LockId);
	syn::custom_keyword!(SlashReason);
	syn::custom_keyword!(exclude_parts);
	syn::custom_keyword!(use_parts);
	syn::custom_keyword!(expanded);
}

/// Declaration of a runtime.
///
/// Pallet declare their part either explicitly or implicitly (using no part declaration)
/// If all pallet have explicit parts then the runtime declaration is explicit, otherwise it is
/// implicit.
#[derive(Debug)]
pub enum RuntimeDeclaration {
	Implicit(ImplicitRuntimeDeclaration),
	Explicit(ExplicitRuntimeDeclaration),
	ExplicitExpanded(ExplicitRuntimeDeclaration),
}

/// Declaration of a runtime with some pallet with implicit declaration of parts.
#[derive(Debug)]
pub struct ImplicitRuntimeDeclaration {
	pub name: Ident,
	pub where_section: WhereSection,
	pub pallets: Vec<PalletDeclaration>,
}

/// Declaration of a runtime with all pallet having explicit declaration of parts.
#[derive(Debug)]
pub struct ExplicitRuntimeDeclaration {
	pub name: Ident,
	pub where_section: WhereSection,
	pub pallets: Vec<Pallet>,
	pub pallets_token: token::Brace,
}

impl Parse for RuntimeDeclaration {
	fn parse(input: ParseStream) -> Result<Self> {
		input.parse::<Token![pub]>()?;

		// Support either `enum` or `struct`.
		if input.peek(Token![struct]) {
			input.parse::<Token![struct]>()?;
		} else {
			input.parse::<Token![enum]>()?;
		}

		let name = input.parse::<syn::Ident>()?;
		let where_section = input.parse()?;
		let pallets =
			input.parse::<ext::Braces<ext::Punctuated<PalletDeclaration, Token![,]>>>()?;
		let pallets_token = pallets.token;

		match convert_pallets(pallets.content.inner.into_iter().collect())? {
			PalletsConversion::Implicit(pallets) =>
				Ok(RuntimeDeclaration::Implicit(ImplicitRuntimeDeclaration {
					name,
					where_section,
					pallets,
				})),
			PalletsConversion::Explicit(pallets) =>
				Ok(RuntimeDeclaration::Explicit(ExplicitRuntimeDeclaration {
					name,
					where_section,
					pallets,
					pallets_token,
				})),
			PalletsConversion::ExplicitExpanded(pallets) =>
				Ok(RuntimeDeclaration::ExplicitExpanded(ExplicitRuntimeDeclaration {
					name,
					where_section,
					pallets,
					pallets_token,
				})),
		}
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

/// The declaration of a pallet.
#[derive(Debug, Clone)]
pub struct PalletDeclaration {
	/// Is this pallet fully expanded?
	pub is_expanded: bool,
	/// The name of the pallet, e.g.`System` in `System: frame_system`.
	pub name: Ident,
	/// Optional attributes tagged right above a pallet declaration.
	pub attrs: Vec<Attribute>,
	/// Optional fixed index, e.g. `MyPallet ...  = 3,`.
	pub index: Option<u8>,
	/// The path of the pallet, e.g. `frame_system` in `System: frame_system`.
	pub path: PalletPath,
	/// The instance of the pallet, e.g. `Instance1` in `Council: pallet_collective::<Instance1>`.
	pub instance: Option<Ident>,
	/// The declared pallet parts,
	/// e.g. `Some([Pallet, Call])` for `System: system::{Pallet, Call}`
	/// or `None` for `System: system`.
	pub pallet_parts: Option<Vec<PalletPart>>,
	/// The specified parts, either use_parts or exclude_parts.
	pub specified_parts: SpecifiedParts,
}

/// The possible declaration of pallet parts to use.
#[derive(Debug, Clone)]
pub enum SpecifiedParts {
	/// Use all the pallet parts except those specified.
	Exclude(Vec<PalletPartNoGeneric>),
	/// Use only the specified pallet parts.
	Use(Vec<PalletPartNoGeneric>),
	/// Use the all the pallet parts.
	All,
}

impl Parse for PalletDeclaration {
	fn parse(input: ParseStream) -> Result<Self> {
		let attrs = input.call(Attribute::parse_outer)?;

		let name = input.parse()?;
		let _: Token![:] = input.parse()?;
		let path = input.parse()?;

		// Parse for instance.
		let instance = if input.peek(Token![::]) && input.peek3(Token![<]) {
			let _: Token![::] = input.parse()?;
			let _: Token![<] = input.parse()?;
			let res = Some(input.parse()?);
			let _: Token![>] = input.parse()?;
			res
		} else if !(input.peek(Token![::]) && input.peek3(token::Brace)) &&
			!input.peek(keyword::expanded) &&
			!input.peek(keyword::exclude_parts) &&
			!input.peek(keyword::use_parts) &&
			!input.peek(Token![=]) &&
			!input.peek(Token![,]) &&
			!input.is_empty()
		{
			return Err(input.error(
				"Unexpected tokens, expected one of `::$ident` `::{`, `exclude_parts`, `use_parts`, `=`, `,`",
			));
		} else {
			None
		};

		// Check if the pallet is fully expanded.
		let (is_expanded, extra_parts) = if input.peek(keyword::expanded) {
			let _: keyword::expanded = input.parse()?;
			let _: Token![::] = input.parse()?;
			(true, parse_pallet_parts(input)?)
		} else {
			(false, vec![])
		};

		// Parse for explicit parts
		let pallet_parts = if input.peek(Token![::]) && input.peek3(token::Brace) {
			let _: Token![::] = input.parse()?;
			let mut parts = parse_pallet_parts(input)?;
			parts.extend(extra_parts.into_iter());
			Some(parts)
		} else if !input.peek(keyword::exclude_parts) &&
			!input.peek(keyword::use_parts) &&
			!input.peek(Token![=]) &&
			!input.peek(Token![,]) &&
			!input.is_empty()
		{
			return Err(input.error(
				"Unexpected tokens, expected one of `::{`, `exclude_parts`, `use_parts`, `=`, `,`",
			))
		} else {
			is_expanded.then_some(extra_parts)
		};

		// Parse for specified parts
		let specified_parts = if input.peek(keyword::exclude_parts) {
			let _: keyword::exclude_parts = input.parse()?;
			SpecifiedParts::Exclude(parse_pallet_parts_no_generic(input)?)
		} else if input.peek(keyword::use_parts) {
			let _: keyword::use_parts = input.parse()?;
			SpecifiedParts::Use(parse_pallet_parts_no_generic(input)?)
		} else if !input.peek(Token![=]) && !input.peek(Token![,]) && !input.is_empty() {
			return Err(input.error("Unexpected tokens, expected one of `exclude_parts`, `=`, `,`"))
		} else {
			SpecifiedParts::All
		};

		// Parse for pallet index
		let index = if input.peek(Token![=]) {
			input.parse::<Token![=]>()?;
			let index = input.parse::<syn::LitInt>()?;
			let index = index.base10_parse::<u8>()?;
			Some(index)
		} else if !input.peek(Token![,]) && !input.is_empty() {
			return Err(input.error("Unexpected tokens, expected one of `=`, `,`"))
		} else {
			None
		};

		Ok(Self { is_expanded, attrs, name, path, instance, pallet_parts, specified_parts, index })
	}
}

/// A struct representing a path to a pallet. `PalletPath` is almost identical to the standard
/// Rust path with a few restrictions:
/// - No leading colons allowed
/// - Path segments can only consist of identifers separated by colons
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
		let mut res =
			PalletPath { inner: Path { leading_colon: None, segments: Punctuated::new() } };

		let lookahead = input.lookahead1();
		if lookahead.peek(Token![crate]) ||
			lookahead.peek(Token![self]) ||
			lookahead.peek(Token![super]) ||
			lookahead.peek(Ident)
		{
			let ident = input.call(Ident::parse_any)?;
			res.inner.segments.push(ident.into());
		} else {
			return Err(lookahead.error())
		}

		while input.peek(Token![::]) && input.peek3(Ident) {
			input.parse::<Token![::]>()?;
			let ident = input.parse::<Ident>()?;
			res.inner.segments.push(ident.into());
		}
		Ok(res)
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
	Error(keyword::Error),
	Config(keyword::Config),
	Origin(keyword::Origin),
	Inherent(keyword::Inherent),
	ValidateUnsigned(keyword::ValidateUnsigned),
	FreezeReason(keyword::FreezeReason),
	HoldReason(keyword::HoldReason),
	LockId(keyword::LockId),
	SlashReason(keyword::SlashReason),
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
		} else if lookahead.peek(keyword::Error) {
			Ok(Self::Error(input.parse()?))
		} else if lookahead.peek(keyword::Config) {
			Ok(Self::Config(input.parse()?))
		} else if lookahead.peek(keyword::Origin) {
			Ok(Self::Origin(input.parse()?))
		} else if lookahead.peek(keyword::Inherent) {
			Ok(Self::Inherent(input.parse()?))
		} else if lookahead.peek(keyword::ValidateUnsigned) {
			Ok(Self::ValidateUnsigned(input.parse()?))
		} else if lookahead.peek(keyword::FreezeReason) {
			Ok(Self::FreezeReason(input.parse()?))
		} else if lookahead.peek(keyword::HoldReason) {
			Ok(Self::HoldReason(input.parse()?))
		} else if lookahead.peek(keyword::LockId) {
			Ok(Self::LockId(input.parse()?))
		} else if lookahead.peek(keyword::SlashReason) {
			Ok(Self::SlashReason(input.parse()?))
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
			Self::Error(_) => "Error",
			Self::Config(_) => "Config",
			Self::Origin(_) => "Origin",
			Self::Inherent(_) => "Inherent",
			Self::ValidateUnsigned(_) => "ValidateUnsigned",
			Self::FreezeReason(_) => "FreezeReason",
			Self::HoldReason(_) => "HoldReason",
			Self::LockId(_) => "LockId",
			Self::SlashReason(_) => "SlashReason",
		}
	}

	/// Returns `true` if this pallet part is allowed to have generic arguments.
	fn allows_generic(&self) -> bool {
		Self::all_generic_arg().iter().any(|n| *n == self.name())
	}

	/// Returns the names of all pallet parts that allow to have a generic argument.
	fn all_generic_arg() -> &'static [&'static str] {
		&["Event", "Error", "Origin", "Config"]
	}
}

impl ToTokens for PalletPartKeyword {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		match self {
			Self::Pallet(inner) => inner.to_tokens(tokens),
			Self::Call(inner) => inner.to_tokens(tokens),
			Self::Storage(inner) => inner.to_tokens(tokens),
			Self::Event(inner) => inner.to_tokens(tokens),
			Self::Error(inner) => inner.to_tokens(tokens),
			Self::Config(inner) => inner.to_tokens(tokens),
			Self::Origin(inner) => inner.to_tokens(tokens),
			Self::Inherent(inner) => inner.to_tokens(tokens),
			Self::ValidateUnsigned(inner) => inner.to_tokens(tokens),
			Self::FreezeReason(inner) => inner.to_tokens(tokens),
			Self::HoldReason(inner) => inner.to_tokens(tokens),
			Self::LockId(inner) => inner.to_tokens(tokens),
			Self::SlashReason(inner) => inner.to_tokens(tokens),
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

/// The declaration of a part without its generics
#[derive(Debug, Clone)]
pub struct PalletPartNoGeneric {
	keyword: PalletPartKeyword,
}

impl Parse for PalletPartNoGeneric {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(Self { keyword: input.parse()? })
	}
}

/// Parse [`PalletPartNoGeneric`]'s from a braces enclosed list that is split by commas, e.g.
///
/// `{ Call, Event }`
fn parse_pallet_parts_no_generic(input: ParseStream) -> Result<Vec<PalletPartNoGeneric>> {
	let pallet_parts: ext::Braces<ext::Punctuated<PalletPartNoGeneric, Token![,]>> =
		input.parse()?;

	let mut resolved = HashSet::new();
	for part in pallet_parts.content.inner.iter() {
		if !resolved.insert(part.keyword.name()) {
			let msg = format!(
				"`{}` was already declared before. Please remove the duplicate declaration",
				part.keyword.name(),
			);
			return Err(Error::new(part.keyword.span(), msg))
		}
	}

	Ok(pallet_parts.content.inner.into_iter().collect())
}

/// The final definition of a pallet with the resulting fixed index and explicit parts.
#[derive(Debug, Clone)]
pub struct Pallet {
	/// Is this pallet fully expanded?
	pub is_expanded: bool,
	/// The name of the pallet, e.g.`System` in `System: frame_system`.
	pub name: Ident,
	/// Either automatically infered, or defined (e.g. `MyPallet ...  = 3,`).
	pub index: u8,
	/// The path of the pallet, e.g. `frame_system` in `System: frame_system`.
	pub path: PalletPath,
	/// The instance of the pallet, e.g. `Instance1` in `Council: pallet_collective::<Instance1>`.
	pub instance: Option<Ident>,
	/// The pallet parts to use for the pallet.
	pub pallet_parts: Vec<PalletPart>,
	/// Expressions specified inside of a #[cfg] attribute.
	pub cfg_pattern: Vec<cfg_expr::Expression>,
}

impl Pallet {
	/// Get resolved pallet parts
	pub fn pallet_parts(&self) -> &[PalletPart] {
		&self.pallet_parts
	}

	/// Find matching parts
	pub fn find_part(&self, name: &str) -> Option<&PalletPart> {
		self.pallet_parts.iter().find(|part| part.name() == name)
	}

	/// Return whether pallet contains part
	pub fn exists_part(&self, name: &str) -> bool {
		self.find_part(name).is_some()
	}
}

/// Result of a conversion of a declaration of pallets.
///
/// # State Transitions
///
/// ```ignore
/// +----------+    +----------+    +------------------+
/// | Implicit | -> | Explicit | -> | ExplicitExpanded |
/// +----------+    +----------+    +------------------+
/// ```
enum PalletsConversion {
	/// Pallets implicitely declare parts.
	///
	/// `System: frame_system`.
	Implicit(Vec<PalletDeclaration>),
	/// Pallets explicitly declare parts.
	///
	/// `System: frame_system::{Pallet, Call}`
	///
	/// However, for backwards compatibility with Polkadot/Kusama
	/// we must propagate some other parts to the pallet by default.
	Explicit(Vec<Pallet>),
	/// Pallets explicitly declare parts that are fully expanded.
	///
	/// This is the end state that contains extra parts included by
	/// default by Subtrate.
	///
	/// `System: frame_system expanded::{Error} ::{Pallet, Call}`
	///
	/// For this example, the `Pallet`, `Call` and `Error` parts are collected.
	ExplicitExpanded(Vec<Pallet>),
}

/// Convert from the parsed pallet declaration to their final information.
///
/// Check if all pallet have explicit declaration of their parts, if so then assign index to each
/// pallet using same rules as rust for fieldless enum. I.e. implicit are assigned number
/// incrementedly from last explicit or 0.
fn convert_pallets(pallets: Vec<PalletDeclaration>) -> syn::Result<PalletsConversion> {
	if pallets.iter().any(|pallet| pallet.pallet_parts.is_none()) {
		return Ok(PalletsConversion::Implicit(pallets))
	}

	let mut indices = HashMap::new();
	let mut last_index: Option<u8> = None;
	let mut names = HashMap::new();
	let mut is_expanded = true;

	let pallets = pallets
		.into_iter()
		.map(|pallet| {
			let final_index = match pallet.index {
				Some(i) => i,
				None => last_index.map_or(Some(0), |i| i.checked_add(1)).ok_or_else(|| {
					let msg = "Pallet index doesn't fit into u8, index is 256";
					syn::Error::new(pallet.name.span(), msg)
				})?,
			};

			last_index = Some(final_index);

			if let Some(used_pallet) = indices.insert(final_index, pallet.name.clone()) {
				let msg = format!(
					"Pallet indices are conflicting: Both pallets {} and {} are at index {}",
					used_pallet, pallet.name, final_index,
				);
				let mut err = syn::Error::new(used_pallet.span(), &msg);
				err.combine(syn::Error::new(pallet.name.span(), msg));
				return Err(err)
			}

			if let Some(used_pallet) = names.insert(pallet.name.clone(), pallet.name.span()) {
				let msg = "Two pallets with the same name!";

				let mut err = syn::Error::new(used_pallet, &msg);
				err.combine(syn::Error::new(pallet.name.span(), &msg));
				return Err(err)
			}

			let mut pallet_parts = pallet.pallet_parts.expect("Checked above");

			let available_parts =
				pallet_parts.iter().map(|part| part.keyword.name()).collect::<HashSet<_>>();

			// Check parts are correctly specified
			match &pallet.specified_parts {
				SpecifiedParts::Exclude(parts) | SpecifiedParts::Use(parts) =>
					for part in parts {
						if !available_parts.contains(part.keyword.name()) {
							let msg = format!(
								"Invalid pallet part specified, the pallet `{}` doesn't have the \
								`{}` part. Available parts are: {}.",
								pallet.name,
								part.keyword.name(),
								pallet_parts.iter().fold(String::new(), |fold, part| {
									if fold.is_empty() {
										format!("`{}`", part.keyword.name())
									} else {
										format!("{}, `{}`", fold, part.keyword.name())
									}
								})
							);
							return Err(syn::Error::new(part.keyword.span(), msg))
						}
					},
				SpecifiedParts::All => (),
			}

			// Set only specified parts.
			match pallet.specified_parts {
				SpecifiedParts::Exclude(excluded_parts) => pallet_parts.retain(|part| {
					!excluded_parts
						.iter()
						.any(|excluded_part| excluded_part.keyword.name() == part.keyword.name())
				}),
				SpecifiedParts::Use(used_parts) => pallet_parts.retain(|part| {
					used_parts.iter().any(|use_part| use_part.keyword.name() == part.keyword.name())
				}),
				SpecifiedParts::All => (),
			}

			let cfg_pattern = pallet
				.attrs
				.iter()
				.map(|attr| {
					if attr.path().segments.first().map_or(false, |s| s.ident != "cfg") {
						let msg = "Unsupported attribute, only #[cfg] is supported on pallet \
						declarations in `construct_runtime`";
						return Err(syn::Error::new(attr.span(), msg))
					}

					attr.parse_args_with(|input: syn::parse::ParseStream| {
						// Required, otherwise the parse stream doesn't advance and will result in
						// an error.
						let input = input.parse::<proc_macro2::TokenStream>()?;
						cfg_expr::Expression::parse(&input.to_string())
							.map_err(|e| syn::Error::new(attr.span(), e.to_string()))
					})
				})
				.collect::<Result<Vec<_>>>()?;

			is_expanded &= pallet.is_expanded;

			Ok(Pallet {
				is_expanded: pallet.is_expanded,
				name: pallet.name,
				index: final_index,
				path: pallet.path,
				instance: pallet.instance,
				cfg_pattern,
				pallet_parts,
			})
		})
		.collect::<Result<Vec<_>>>()?;

	if is_expanded {
		Ok(PalletsConversion::ExplicitExpanded(pallets))
	} else {
		Ok(PalletsConversion::Explicit(pallets))
	}
}
