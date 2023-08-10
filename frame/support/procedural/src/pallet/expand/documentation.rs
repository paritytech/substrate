// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::{spanned::Spanned, Attribute, Lit, LitStr};

const DOC: &'static str = "doc";
const PALLET_DOC: &'static str = "pallet_doc";

/// Get the documentation file path from the `pallet_doc` attribute.
///
/// Supported format:
/// `#[pallet_doc(PATH)]`: The path of the file from which the documentation is loaded
fn parse_pallet_doc_value(attr: &Attribute) -> syn::Result<DocMetaValue> {
	let lit: syn::LitStr = attr.parse_args().map_err(|_| {
		let msg = "The `pallet_doc` received an unsupported argument. Supported format: `pallet_doc(\"PATH\")`";
		syn::Error::new(attr.span(), msg)
	})?;

	Ok(DocMetaValue::Path(lit))
}

/// Get the value from the `doc` comment attribute:
///
/// Supported formats:
/// - `#[doc = "A doc string"]`: Documentation as a string literal
/// - `#[doc = include_str!(PATH)]`: Documentation obtained from a path
fn parse_doc_value(attr: &Attribute) -> syn::Result<Option<DocMetaValue>> {
	if !attr.path().is_ident(DOC) {
		return Ok(None)
	}

	let meta = attr.meta.require_name_value()?;

	match &meta.value {
		syn::Expr::Lit(lit) => Ok(Some(DocMetaValue::Lit(lit.lit.clone()))),
		syn::Expr::Macro(mac) if mac.mac.path.is_ident("include_str") =>
			Ok(Some(DocMetaValue::Path(mac.mac.parse_body()?))),
		_ =>
			Err(syn::Error::new(attr.span(), "Expected `= \"docs\"` or `= include_str!(\"PATH\")`")),
	}
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
	Path(LitStr),
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

/// Extract the documentation from the given pallet definition
/// to include in the runtime metadata.
///
/// Implement a `pallet_documentation_metadata` function to fetch the
/// documentation that is included in the metadata.
///
/// The documentation is placed on the pallet similar to:
///
/// ```ignore
/// #[pallet]
/// /// Documentation for pallet
/// #[doc = "Documentation for pallet"]
/// #[doc = include_str!("../README.md")]
/// #[pallet_doc("../documentation1.md")]
/// #[pallet_doc("../documentation2.md")]
/// pub mod pallet {}
/// ```
///
/// # pallet_doc
///
/// The `pallet_doc` attribute can only be provided with one argument,
/// which is the file path that holds the documentation to be added to the metadata.
///
/// Unlike the `doc` attribute, the documentation provided to the `proc_macro` attribute is
/// not added to the pallet.
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
		if attr.path().get_ident().map_or(false, |i| *i == PALLET_DOC) {
			pallet_docs.push(def.item.attrs.remove(index));
			// Do not increment the index, we have just removed the
			// element from the attributes.
			continue
		}

		index += 1;
	}

	// Capture the `#[doc = include_str!("../README.md")]` and `#[doc = "Documentation"]`.
	let docs = match def
		.item
		.attrs
		.iter()
		.filter_map(|v| parse_doc_value(v).transpose())
		.collect::<syn::Result<Vec<_>>>()
	{
		Ok(r) => r,
		Err(err) => return err.into_compile_error(),
	};

	// Capture the `#[pallet_doc("../README.md")]`.
	let pallet_docs = match pallet_docs
		.into_iter()
		.map(|attr| parse_pallet_doc_value(&attr))
		.collect::<syn::Result<Vec<_>>>()
	{
		Ok(docs) => docs,
		Err(err) => return err.into_compile_error(),
	};

	let docs = docs.iter().chain(pallet_docs.iter());

	quote::quote!(
		impl<#type_impl_gen> #pallet_ident<#type_use_gen> #where_clauses{

			#[doc(hidden)]
			pub fn pallet_documentation_metadata()
				-> #frame_support::__private::sp_std::vec::Vec<&'static str>
			{
				#frame_support::__private::sp_std::vec![ #( #docs ),* ]
			}
		}
	)
}
