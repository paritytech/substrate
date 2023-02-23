// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Implementation of the `storage_alias` attribute macro.

use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::{punctuated::Punctuated, ItemImpl, Result, Token};

mod keywords {
	syn::custom_keyword!(derive_impl);
	syn::custom_keyword!(partial_impl_block);
	syn::custom_keyword!(implementing_type);
	syn::custom_keyword!(type_items);
	syn::custom_keyword!(fn_items);
	syn::custom_keyword!(const_items);
}

pub struct DeriveImplDef {
	/// The partial impl block that the user provides. This should be interpreted as "override".
	partial_impl_block: syn::ItemImpl,
	/// The full path to the type that can be used to receive defaults form.
	implementing_type: syn::TypePath,
	/// All of the associated type items that we must eventually implement.
	type_items: Punctuated<syn::Ident, Token![,]>,
	/// All of the function items that we must eventually implement.
	fn_items: Punctuated<syn::Ident, Token![,]>,
	/// All of the constant items that we must eventually implement.
	const_items: Punctuated<syn::Ident, Token![,]>,
}

impl syn::parse::Parse for DeriveImplDef {
	fn parse(input: syn::parse::ParseStream) -> Result<Self> {
		// NOTE: unfortunately, the order the keywords here must match what the pallet macro
		// expands. We can probably used a shared set of keywords later.
		let mut partial_impl_block;
		let _ = input.parse::<keywords::partial_impl_block>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket =
			syn::bracketed!(partial_impl_block in input);
		let _replace_with_brace: syn::token::Brace =
			syn::braced!(partial_impl_block in partial_impl_block);
		let partial_impl_block = partial_impl_block.parse()?;

		let mut implementing_type;
		let _ = input.parse::<keywords::implementing_type>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket =
			syn::bracketed!(implementing_type in input);
		let _replace_with_brace: syn::token::Brace =
			syn::braced!(implementing_type in implementing_type);
		let implementing_type = implementing_type.parse()?;

		let mut type_items;
		let _ = input.parse::<keywords::type_items>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(type_items in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(type_items in type_items);
		let type_items = Punctuated::<syn::Ident, Token![,]>::parse_terminated(&type_items)?;

		let mut fn_items;
		let _ = input.parse::<keywords::fn_items>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(fn_items in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(fn_items in fn_items);
		let fn_items = Punctuated::<syn::Ident, Token![,]>::parse_terminated(&fn_items)?;

		let mut const_items;
		let _ = input.parse::<keywords::const_items>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(const_items in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(const_items in const_items);
		let const_items = Punctuated::<syn::Ident, Token![,]>::parse_terminated(&const_items)?;

		Ok(Self { partial_impl_block, type_items, fn_items, const_items, implementing_type })
	}
}

pub(crate) fn derive_impl_inner(input: TokenStream) -> Result<TokenStream> {
	println!("input: {}", input);
	let DeriveImplDef { partial_impl_block, implementing_type, type_items, .. } =
		syn::parse2(input)?;

	let type_item_name = |i: &syn::ImplItem| {
		if let syn::ImplItem::Type(t) = i {
			t.ident.clone()
		} else {
			panic!("only support type items for now")
		}
	};

	// might be able to mutate `partial_impl_block` along the way, but easier like this for now.
	let mut final_impl_block = partial_impl_block.clone();
	let source_crate_path = implementing_type.path.segments.first().unwrap().ident.clone();

	// TODO: ensure type ident specified in `partial_impl_block` is beyond union(type_items,
	// const_items, fn_items).
	assert!(
		partial_impl_block
			.items
			.iter()
			.all(|i| { type_items.iter().find(|tt| tt == &&type_item_name(i)).is_some() }),
		"some item in the partial_impl_block is unexpected"
	);

	// for each item that is in `type_items` but not present in `partial_impl_block`, fill it in.
	type_items.iter().for_each(|ident| {
		if partial_impl_block.items.iter().any(|i| &type_item_name(i) == ident) {
			// this is already present in the partial impl block -- noop
		} else {
			// add it
			let tokens = quote::quote!(type #ident = <#implementing_type as #source_crate_path::pallet::DefaultConfig>::#ident;);
			let parsed: syn::ImplItem = syn::parse2(tokens).expect("it is a valid type item");
			debug_assert!(matches!(parsed, syn::ImplItem::Type(_)));

			final_impl_block.items.push(parsed)
		}
	});

	Ok(quote::quote!(#final_impl_block))
}

pub fn derive_impl(attrs: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let implementing_type: syn::TypePath = syn::parse2(attrs.clone())?;
	// ideas for sam:
	// let other_path_tokens = magic_macro!(path_to_other_path_token);
	// let foreign_trait_def_token: Syn::TraitItem = magic_macro!(frame_system::Config);

	let frame_support = generate_crate_access_2018("frame-support")?;
	// TODO: may not be accurate.
	let source_crate_path = implementing_type.path.segments.first().unwrap().ident.clone();

	Ok(quote::quote!(
		#frame_support::tt_call! {
			macro = [{ #source_crate_path::tt_config_items }]
			frame_support = [{ #frame_support }]
			~~> #frame_support::derive_impl_inner! {
				partial_impl_block = [{ #input }]
				implementing_type = [{ #attrs }]
			}
		}
	))
}
