// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use proc_macro2::{TokenStream, Span};

use syn::{
	Result, Ident, Signature, parse_quote, Type, Pat, spanned::Spanned, FnArg, Error, token::And,
	ImplItem, ReturnType, PathArguments, Path, GenericArgument, TypePath, ItemImpl,
};

use quote::quote;

use std::env;

use proc_macro_crate::{crate_name, FoundCrate};

fn generate_hidden_includes_mod_name(unique_id: &'static str) -> Ident {
	Ident::new(&format!("sp_version_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &'static str) -> TokenStream {
	let mod_name = generate_hidden_includes_mod_name(unique_id);
	match crate_name("sp-version") {
		Ok(FoundCrate::Itself) => quote!(),
		Ok(FoundCrate::Name(client_name)) => {
			let client_name = Ident::new(&client_name, Span::call_site());
			quote!(
				#[doc(hidden)]
				mod #mod_name {
					pub extern crate #client_name as sp_version;
				}
			)
		},
		Err(e) => {
			let err = Error::new(Span::call_site(), e).to_compile_error();
			quote!( #err )
		}
	}
}

/// Generates the access to the `sc_client` crate.
pub fn generate_crate_access(unique_id: &'static str) -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "sp-version" {
		quote!( sp_version )
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!( self::#mod_name::sp_version )
	}.into()
}
