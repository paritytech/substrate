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
use derive_syn_parse::Parse;
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::{
	parse::{self, Parse, ParseStream},
	spanned::Spanned,
	Attribute, Lit,
};

const DOC: &'static str = "doc";
const PALLET_DOC: &'static str = "pallet_doc";

mod keywords {
	syn::custom_keyword!(include_str);
}

/// Get the documentation file path from the `pallet_doc` attribute.
///
/// Supported format:
/// `#[pallet_doc(PATH)]`: The path of the file from which the documentation is loaded
fn parse_pallet_doc_value(attr: &Attribute) -> syn::Result<DocMetaValue> {
	let span = attr.span();

	let meta = attr.parse_meta()?;
	let syn::Meta::List(metalist) = meta else {
		let msg = "The `pallet_doc` attribute must receive arguments as a list. Supported format: `pallet_doc(PATH)`";
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

	let parser = |input: ParseStream| DocParser::parse(input);
	let result = parse::Parser::parse2(parser, attr.tokens.clone()).ok()?;

	if let Some(lit) = result.lit {
		Some(DocMetaValue::Lit(lit))
	} else if let Some(include_doc) = result.include_doc {
		Some(DocMetaValue::Path(include_doc.lit))
	} else {
		None
	}
}

/// Parse the include_str attribute.
#[derive(Debug, Parse)]
struct IncludeDocParser {
	_include_str: keywords::include_str,
	_eq_token: syn::token::Bang,
	#[paren]
	_paren: syn::token::Paren,
	#[inside(_paren)]
	lit: Lit,
}

/// Parse the doc literal.
#[derive(Debug, Parse)]
struct DocParser {
	_eq_token: syn::token::Eq,
	#[peek(Lit)]
	lit: Option<Lit>,
	#[parse_if(lit.is_none())]
	include_doc: Option<IncludeDocParser>,
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
	let mut docs: Vec<_> = def.item.attrs.iter().filter_map(parse_doc_value).collect();

	// Capture the `#[pallet_doc("../README.md")]`.
	let pallet_docs: Vec<_> = match pallet_docs
		.into_iter()
		.map(|attr| parse_pallet_doc_value(&attr))
		.collect::<syn::Result<_>>()
	{
		Ok(docs) => docs,
		Err(err) => return err.into_compile_error(),
	};

	docs.extend(pallet_docs);

	quote::quote!(
		impl<#type_impl_gen> #pallet_ident<#type_use_gen> #where_clauses{

			#[doc(hidden)]
			pub fn pallet_documentation_metadata()
				-> #frame_support::sp_std::vec::Vec<&'static str>
			{
				#frame_support::sp_std::vec![ #( #docs ),* ]
			}
		}
	)
}
