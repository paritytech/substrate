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

// tag::description[]
//! Proc macro helpers for procedural macros
// end::description[]

// reexport proc macros
pub use frame_support_procedural_tools_derive::*;

use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::parse::Error;

pub mod syn_ext;

// FIXME #1569, remove the following functions, which are copied from sp-api-macros
use proc_macro2::{Span, TokenStream};
use syn::Ident;

fn generate_hidden_includes_mod_name(unique_id: &str) -> Ident {
	Ident::new(&format!("sp_api_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the access to the `frame-support` crate.
pub fn generate_crate_access(unique_id: &str, def_crate: &str) -> TokenStream {
	if std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		quote::quote!(frame_support)
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote::quote!( self::#mod_name::hidden_include )
	}
}

/// Check if the output of [`generate_crate_access_2018`] (or generally another path) is using the
/// `frame` crate or not.
pub fn is_using_frame_crate(path: &syn::Path) -> bool {
	path.segments.first().map(|s| s.ident == "frame").unwrap_or(false)
}

/// Generate the crate access for the crate using 2018 syntax.
///
/// If `frame` is in scope, it will use `frame::deps::<def_crate>`. Else, it will try and find
/// `<def_crate>` directly.
pub fn generate_crate_access_2018(def_crate: &str) -> Result<syn::Path, Error> {
	if let Ok(FoundCrate::Name(name)) = crate_name(&"frame") {
		let path = format!("{}::deps::{}", name, def_crate.to_string().replace("-", "_"));
		let path = syn::parse_str::<syn::Path>(&path)?;
		return Ok(path)
	}

	let ident = match crate_name(def_crate) {
		Ok(FoundCrate::Itself) => {
			let name = def_crate.to_string().replace("-", "_");
			Ok(syn::Ident::new(&name, Span::call_site()))
		},
		Ok(FoundCrate::Name(name)) => Ok(Ident::new(&name, Span::call_site())),
		Err(e) => Err(Error::new(Span::call_site(), e)),
	}?;

	Ok(syn::Path::from(ident))
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &str, def_crate: &str) -> TokenStream {
	let mod_name = generate_hidden_includes_mod_name(unique_id);

	if let Ok(FoundCrate::Name(name)) = crate_name(&"frame") {
		let path = format!("{}::deps::{}", name, def_crate.to_string().replace("-", "_"));
		let path = syn::parse_str::<syn::Path>(&path).expect("is a valid path; qed");
		return quote::quote!(
			#[doc(hidden)]
			mod #mod_name {
				pub use #path as hidden_include;
			}
		)
	}

	match crate_name(def_crate) {
		Ok(FoundCrate::Itself) => quote!(),
		Ok(FoundCrate::Name(name)) => {
			let name = Ident::new(&name, Span::call_site());
			quote::quote!(
				#[doc(hidden)]
				mod #mod_name {
					pub extern crate #name as hidden_include;
				}
			)
		},
		Err(e) => {
			let err = Error::new(Span::call_site(), e).to_compile_error();
			quote!( #err )
		},
	}
}

// fn to remove white spaces around string types
// (basically whitespaces around tokens)
pub fn clean_type_string(input: &str) -> String {
	input
		.replace(" ::", "::")
		.replace(":: ", "::")
		.replace(" ,", ",")
		.replace(" ;", ";")
		.replace(" [", "[")
		.replace("[ ", "[")
		.replace(" ]", "]")
		.replace(" (", "(")
		.replace("( ", "(")
		.replace(" )", ")")
		.replace(" <", "<")
		.replace("< ", "<")
		.replace(" >", ">")
}

/// Return all doc attributes literals found.
pub fn get_doc_literals(attrs: &[syn::Attribute]) -> Vec<syn::Expr> {
	attrs
		.iter()
		.filter_map(|attr| {
			if let syn::Meta::NameValue(meta) = &attr.meta {
				meta.path
					.get_ident()
					.filter(|ident| *ident == "doc")
					.map(|_| meta.value.clone())
			} else {
				None
			}
		})
		.collect()
}
