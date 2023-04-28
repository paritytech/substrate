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

//! Implementation of the `derive_impl` attribute macro.

use derive_syn_parse::Parse;
use macro_magic::mm_core::ForeignPath;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use std::collections::HashSet;
use syn::{parse2, parse_quote, spanned::Spanned, Ident, ImplItem, ItemImpl, Path, Result, Token};

#[derive(Parse)]
pub struct DeriveImplAttrArgs {
	pub foreign_path: Path,
	_as: Option<Token![as]>,
	#[parse_if(_as.is_some())]
	pub disambiguation_path: Option<Path>,
}

impl ForeignPath for DeriveImplAttrArgs {
	fn foreign_path(&self) -> &Path {
		&self.foreign_path
	}
}

impl ToTokens for DeriveImplAttrArgs {
	fn to_tokens(&self, tokens: &mut TokenStream2) {
		tokens.extend(self.foreign_path.to_token_stream());
		tokens.extend(self._as.to_token_stream());
		tokens.extend(self.disambiguation_path.to_token_stream());
	}
}

/// Gets the [`Ident`] representation of the given [`ImplItem`], if one exists. Otherwise
/// returns [`None`].
///
/// Used by [`combine_impls`] to determine whether we can compare [`ImplItem`]s by [`Ident`]
/// or not.
fn impl_item_ident(impl_item: &ImplItem) -> Option<Ident> {
	match impl_item {
		ImplItem::Const(item) => Some(item.ident.clone()),
		ImplItem::Fn(item) => Some(item.sig.ident.clone()),
		ImplItem::Type(item) => Some(item.ident.clone()),
		ImplItem::Macro(item) => item.mac.path.get_ident().cloned(),
		_ => None,
	}
}

/// The real meat behind `derive_impl`. Takes in a `local_impl`, which is the impl for which we
/// want to implement defaults (i.e. the one the attribute macro is attached to), and a
/// `foreign_impl`, which is the impl containing the defaults we want to use, and returns an
/// [`ItemImpl`] containing the final generated impl.
///
/// This process has the following caveats:
/// * Colliding items that have an ident are not copied into `local_impl`
/// * Uncolliding items that have an ident are copied into `local_impl` but are qualified as `type
///   #ident = <#foreign_path as #disambiguation_path>::#ident;`
/// * Items that lack an ident are de-duplicated so only unique items that lack an ident are copied
///   into `local_impl`. Items that lack an ident and also exist verbatim in `local_impl` are not
///   copied over.
fn combine_impls(
	local_impl: ItemImpl,
	foreign_impl: ItemImpl,
	foreign_path: Path,
	disambiguation_path: Path,
) -> ItemImpl {
	let existing_local_keys: HashSet<Ident> = local_impl
		.items
		.iter()
		.filter_map(|impl_item| impl_item_ident(impl_item))
		.collect();
	let existing_unsupported_items: HashSet<ImplItem> = local_impl
		.items
		.iter()
		.filter(|impl_item| impl_item_ident(impl_item).is_none())
		.cloned()
		.collect();
	let mut final_impl = local_impl;
	let extended_items = foreign_impl
		.items
		.into_iter()
		.filter_map(|item| {
			if let Some(ident) = impl_item_ident(&item) {
				if existing_local_keys.contains(&ident) {
					// do not copy colliding items that have an ident
					None
				} else {
					if matches!(item, ImplItem::Type(_)) {
						// modify and insert uncolliding type items
						let modified_item: ImplItem = parse_quote! {
							type #ident = <#foreign_path as #disambiguation_path>::#ident;
						};
						Some(modified_item)
					} else {
						// copy uncolliding non-type items that have an ident
						Some(item)
					}
				}
			} else {
				if existing_unsupported_items.contains(&item) {
					// do not copy colliding items that lack an ident
					None
				} else {
					// copy uncolliding items without an ident verbaitm
					Some(item)
				}
			}
		});
	final_impl.items.extend(extended_items);
	final_impl
}

/// Internal implementation behind [`#[derive_impl(..)]`](`macro@crate::derive_impl`).
///
/// `foreign_path`: the module path of the external `impl` statement whose tokens we are
///	                importing via `macro_magic`
///
/// `foreign_tokens`: the tokens for the external `impl` statement
///
/// `local_tokens`: the tokens for the local `impl` statement this attribute is attached to
///
/// `disambiguation_path`: the module path of the external trait we will use to qualify
///                        defaults imported from the external `impl` statement
pub fn derive_impl(
	foreign_path: TokenStream2,
	foreign_tokens: TokenStream2,
	local_tokens: TokenStream2,
	disambiguation_path: Option<Path>,
) -> Result<TokenStream2> {
	let local_impl = parse2::<ItemImpl>(local_tokens)?;
	let foreign_impl = parse2::<ItemImpl>(foreign_tokens)?;
	let foreign_path = parse2::<Path>(foreign_path)?;

	// have disambiguation_path default to the item being impl'd in the foreign impl if we
	// don't specify an `as [disambiguation_path]` in the macro attr
	let disambiguation_path = match disambiguation_path {
		Some(disambiguation_path) => disambiguation_path,
		None => {
			let Some((_, foreign_impl_path, _)) = foreign_impl.clone().trait_ else {
				return Err(
					syn::Error::new(foreign_impl.span(),
					"Impl statement must have a defined type being implemented for a defined type such as `impl A for B`")
				);
			};
			foreign_impl_path
		},
	};

	// generate the combined impl
	let combined_impl = combine_impls(local_impl, foreign_impl, foreign_path, disambiguation_path);

	Ok(quote!(#combined_impl))
}

#[test]
fn test_derive_impl_attr_args_parsing() {
	parse2::<DeriveImplAttrArgs>(quote!(
		some::path::TestDefaultConfig as some::path::DefaultConfig
	))
	.unwrap();
	parse2::<DeriveImplAttrArgs>(quote!(
		frame_system::preludes::testing::TestDefaultConfig as DefaultConfig
	))
	.unwrap();
	parse2::<DeriveImplAttrArgs>(quote!(Something as some::path::DefaultConfig)).unwrap();
	parse2::<DeriveImplAttrArgs>(quote!(Something as DefaultConfig)).unwrap();
	parse2::<DeriveImplAttrArgs>(quote!(DefaultConfig)).unwrap();
	assert!(parse2::<DeriveImplAttrArgs>(quote!()).is_err());
	assert!(parse2::<DeriveImplAttrArgs>(quote!(Config Config)).is_err());
}
