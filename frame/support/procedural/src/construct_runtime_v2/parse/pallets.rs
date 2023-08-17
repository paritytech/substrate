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
use crate::construct_runtime::parse::PalletPartKeyword;
use crate::construct_runtime::parse::PalletPath;
use crate::construct_runtime::parse::PalletPart;
use crate::construct_runtime::parse::PalletPartNoGeneric;
use crate::construct_runtime::parse::Pallet;

mod keyword {
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
}

#[derive(Debug, Clone)]
pub enum AllPalletsDeclaration {
	Implicit(ImplicitAllPalletsDeclaration),
	Explicit(ExplicitAllPalletsDeclaration),
}

/// Declaration of a runtime with some pallet with implicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ImplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallets: Vec<PalletDeclaration>,
}

/// Declaration of a runtime with all pallet having explicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ExplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallets: Vec<Pallet>,
	pub pallets_token: token::Brace,
}

impl Parse for AllPalletsDeclaration {
    fn parse(input: ParseStream) -> Result<Self> {
		input.parse::<Token![pub]>()?;

	   	// Support either `enum` or `struct`.
		if input.peek(Token![struct]) {
			input.parse::<Token![struct]>()?;
		} else {
			input.parse::<Token![enum]>()?;
		}

        let name = input.parse::<syn::Ident>()?;
        let pallets =
			input.parse::<ext::Braces<ext::Punctuated<PalletDeclaration, Token![,]>>>()?;
		let pallets_token = pallets.token;

        match convert_pallets(pallets.content.inner.into_iter().collect())? {
			PalletsConversion::Implicit(pallets) =>
				Ok(AllPalletsDeclaration::Implicit(ImplicitAllPalletsDeclaration {
					name,
					pallets,
				})),
			PalletsConversion::Explicit(pallets) =>
				Ok(AllPalletsDeclaration::Explicit(ExplicitAllPalletsDeclaration {
					name,
					pallets,
					pallets_token,
				})),
		}
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
		// println!("path: {:?}", path);

		// Parse for instance.
		let instance = if input.peek(Token![::]) && input.peek3(Token![<]) {
			let _: Token![::] = input.parse()?;
			let _: Token![<] = input.parse()?;
			let res = Some(input.parse()?);
			let _: Token![>] = input.parse()?;
			res
		} else if !(input.peek(Token![+])) &&
			!input.peek(keyword::exclude_parts) &&
			!input.peek(keyword::use_parts) &&
			!input.peek(Token![=]) &&
			!input.peek(Token![,]) &&
			!input.is_empty()
		{
			return Err(input.error(
				"Unexpected tokens, expected one of `::$ident` `+`, `exclude_parts`, `use_parts`, `=`, `,`",
			));
		} else {
			None
		};

		// // Check if the pallet is fully expanded.
		// let (is_expanded, extra_parts) = if input.peek(keyword::expanded) {
		// 	let _: keyword::expanded = input.parse()?;
		// 	let _: Token![::] = input.parse()?;
		// 	(true, parse_pallet_parts(input)?)
		// } else {
		// 	(false, vec![])
		// };

		let (is_expanded, extra_parts) = (false, vec![]);

		// Parse for explicit parts
		let pallet_parts = if input.peek(Token![+]) {
			let _: Token![+] = input.parse()?;
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
				"Unexpected tokens, expected one of `+`, `exclude_parts`, `use_parts`, `=`, `,`",
			))
		} else {
			is_expanded.then_some(extra_parts)
		};

		// Parse for specified parts
		// let specified_parts = if input.peek(keyword::exclude_parts) {
		// 	let _: keyword::exclude_parts = input.parse()?;
		// 	SpecifiedParts::Exclude(parse_pallet_parts_no_generic(input)?)
		// } else if input.peek(keyword::use_parts) {
		// 	let _: keyword::use_parts = input.parse()?;
		// 	SpecifiedParts::Use(parse_pallet_parts_no_generic(input)?)
		// } else if !input.peek(Token![=]) && !input.peek(Token![,]) && !input.is_empty() {
		// 	return Err(input.error("Unexpected tokens, expected one of `exclude_parts`, `=`, `,`"))
		// } else {
		// 	SpecifiedParts::All
		// };

		let specified_parts = SpecifiedParts::All;


		// Parse for pallet index
		// let index = if input.peek(Token![=]) {
		// 	input.parse::<Token![=]>()?;
		// 	let index = input.parse::<syn::LitInt>()?;
		// 	let index = index.base10_parse::<u8>()?;
		// 	Some(index)
		// } else if !input.peek(Token![,]) && !input.is_empty() {
		// 	return Err(input.error("Unexpected tokens, expected one of `=`, `,`"))
		// } else {
		// 	None
		// };
		let index = None;

		Ok(Self { is_expanded, attrs, name, path, instance, pallet_parts, specified_parts, index })
	}
}

/// Parse [`PalletPart`]'s from a braces enclosed list that is split by commas, e.g.
///
/// `{ Call, Event }`
fn parse_pallet_parts(input: ParseStream) -> Result<Vec<PalletPart>> {
	// let pallet_parts: ext::Punctuated<PalletPart, Token![+]> = input.parse()?;
	let pallet_parts = Punctuated::<PalletPart, Token![+]>::parse_separated_nonempty(&input)?;

	let mut resolved = HashSet::new();
	for part in pallet_parts.iter() {
		if !resolved.insert(part.name()) {
			let msg = format!(
				"`{}` was already declared before. Please remove the duplicate declaration",
				part.name(),
			);
			return Err(Error::new(part.keyword.span(), msg))
		}
	}

	Ok(pallet_parts.into_iter().collect())
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

/// Result of a conversion of a declaration of pallets.
///
/// # State Transitions
///
/// ```ignore
/// +----------+    +----------+
/// | Implicit | -> | Explicit |
/// +----------+    +----------+
/// ```
enum PalletsConversion {
	/// Pallets implicitely declare parts.
	///
	/// `System: frame_system`.
	Implicit(Vec<PalletDeclaration>),
	/// Pallets explicitly declare parts.
	///
	/// `System: frame_system + Pallet + Call`
	///
	/// However, for backwards compatibility with Polkadot/Kusama
	/// we must propagate some other parts to the pallet by default.
	Explicit(Vec<Pallet>),
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

	Ok(PalletsConversion::Explicit(pallets))
}
