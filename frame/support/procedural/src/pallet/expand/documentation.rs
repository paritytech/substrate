// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::pallet::Def;
use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::{
	parenthesized,
	parse::{self, Parse, ParseStream},
	spanned::Spanned,
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
	let span = attr.span();

	let meta = attr.parse_meta()?;
	let syn::Meta::List(metalist) = meta else {
                let msg =
                        "The `pallet_doc` attribute must receive arguments as a list. Supported format: `pallet_doc(PATH)`";
                return Err(syn::Error::new(span, msg))
        };

	let paths: Vec<_> = metalist
                .nested
                .into_iter()
                .map(|nested| {
                        let syn::NestedMeta::Lit(lit) = nested else {
                                let msg = "The `pallet_doc` received an unsupported argument. Supported format: `pallet_doc(PATH)`";
                        return Err(syn::Error::new(span, msg))
                };

                        Ok(lit)
                })
                .collect::<syn::Result<_>>()?;

	if paths.len() != 1 {
		let msg = "The `pallet_doc` attribute must receive only one argument. Supported format: `pallet_doc(PATH)`";
		return Err(syn::Error::new(span, msg))
	}

	Ok(DocMetaValue::Path(paths[0].clone()))
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
	Path(Lit),
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
		content.parse().map(DocMetaValue::Path)
	}
}

impl ToTokens for DocMetaValue {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		match self {
			DocMetaValue::Lit(lit) => lit.to_tokens(tokens),
			DocMetaValue::Path(path_lit) => {
				let decl = quote::quote!(include_str!(#path_lit));
				tokens.extend(decl)
			},
		}
	}
}
