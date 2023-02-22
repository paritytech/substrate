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

use crate::pallet::{parse::event::PalletEventDepositAttr, Def};
use proc_macro2::{Ident, TokenStream};
use quote::{ToTokens, spanned::Spanned};
use syn::{
	parenthesized,
	parse::{self, Parse, ParseStream},
	Attribute, Lit, Token,
};

const DOC: &'static str = "doc";
const INCLUDE_STR: &'static str = "include_str";
const PALLET_DOC: &'static str = "pallet_doc";

/// Get the documentation file path from the `pallet_doc` attribute.
///
/// Supported format:
/// `#[pallet_doc(PATH)]`: The path of the file from which the documentation is loaded
fn parse_pallet_doc_value(attr: &Attribute) -> syn::Result<DocMetaValue> {
	let meta = attr.parse_meta()?;
	let span = meta.ident

	match meta {
    syn::Meta::List(metalist) => {
		metalist.__span();
	}
	_ => syn::Error::new(proc_macro2::Span::call_site(), "Unexpected arguments for `pallet_doc` attribute. Supported version: `pallet_doc(PATH)`");
	}

}

/// Get the value from the `doc` comment attribute:
///
/// Supported formats:
/// - `#[doc = "A doc string"]`: Documentation as a string literal
/// - `#[doc = include_str!(PATH)]`: Documentation obtained from a path
fn parse_doc_value(attr: &Attribute) -> Option<DocMetaValue> {
	let Some(ident) = attr.path.get_ident() else {
		return None
	};
	if ident != DOC {
		return None
	}

	let parser = |input: ParseStream| DocMetaValue::parse(input);
	parse::Parser::parse2(parser, attr.tokens.clone()).ok()
}

/// Supported documentation tokens.
#[derive(Debug)]
enum DocMetaValue {
	/// Documentation with string literals.
	///
	/// `#[doc = "Lit"]`
	Lit(Lit),
	/// Documentation with `include_str!` macro.
	///
	/// The string literal represents the file `PATH`.
	///
	/// `#[doc = include_str!(PATH)]`
	IncludeStr(Lit),
}

impl Parse for DocMetaValue {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let _token: Token![=] = input.parse()?;

		if input.peek(Lit) {
			return input.parse().map(DocMetaValue::Lit)
		}

		let ident: Ident = input.parse()?;
		if ident != INCLUDE_STR {
			return Err(input.error("expected include_str ident"))
		}
		let _token: Token![!] = input.parse()?;

		// We must have a path literal inside `(...)`
		let content;
		parenthesized!(content in input);
		content.parse().map(DocMetaValue::IncludeStr)
	}
}

impl ToTokens for DocMetaValue {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		match self {
			DocMetaValue::Lit(lit) => lit.to_tokens(tokens),
			DocMetaValue::IncludeStr(path_lit) => {
				let decl = quote::quote!(include_str!(#path_lit));
				tokens.extend(decl)
			},
		}
	}
}

/// Extract the documentation from the given pallet definition
/// to include in the runtime metadata.
///
/// The documentation is placed at the top of the module similar to:
///
/// ```ignore
/// #[pallet]
/// /// Documentation for pallet
/// #[doc = include_str!("../README.md")]
/// #[doc = "Documentation for pallet"]
/// pub mod pallet {}
/// ```
///
/// Developers that want to expose this documentation via the metadata are
/// encouraged to place it above the module, similar to the above example.
///
/// Implement a `pallet_documentation_metadata` function to fetch the
/// documentation that is included in the metadata.
pub fn expand_documentation(def: &mut Def) -> proc_macro2::TokenStream {
	let frame_support = &def.frame_support;
	let type_impl_gen = &def.type_impl_generics(proc_macro2::Span::call_site());
	let type_use_gen = &def.type_use_generics(proc_macro2::Span::call_site());
	let pallet_ident = &def.pallet_struct.pallet;
	let where_clauses = &def.config.where_clause;

	// TODO: Use [drain_filter](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain_filter) when it is stable.

	// The `pallet_doc` attributes are excluded from the generation of the pallet,
	// but they are included in the runtime metadata.
	let mut pallet_docs = Vec::with_capacity(def.item.attrs.len());
	let mut index = 0;
	while index < def.item.attrs.len() {
		let attr = &def.item.attrs[index];

		if let Some(ident) = attr.path.get_ident() {
			if ident == PALLET_DOC {
				let elem = def.item.attrs.remove(index);
				pallet_docs.push(elem);
				// Do not increment the index, we have just removed the
				// element from the attributes.
				continue
			}
		}

		index += 1;
	}

	// Capture the `#[doc = include_str!("../README.md")]` and `#[doc = "Documentation"]`.
	let docs: Vec<_> = def.item.attrs.iter().filter_map(parse_doc_value).collect();

	let res = quote::quote!(
		impl<#type_impl_gen> #pallet_ident<#type_use_gen> #where_clauses{

			#[doc(hidden)]
			pub fn pallet_documentation_metadata()
				-> #frame_support::sp_std::vec::Vec<&'static str>
			{
				#frame_support::sp_std::vec![ #( #docs ),* ]
			}
		}
	);
	println!("Res is {}", res);
	res
}
