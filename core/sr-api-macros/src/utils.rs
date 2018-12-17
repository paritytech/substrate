// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use proc_macro2::{TokenStream, Span};
use syn::{Result, Ident, FnDecl, parse_quote, Type};
use quote::quote;
use std::env;

/// Unwrap the given result, if it is an error, `compile_error!` will be generated.
pub fn unwrap_or_error(res: Result<TokenStream>) -> TokenStream {
	res.unwrap_or_else(|e| e.to_compile_error())
}

fn generate_hidden_includes_mod_name(unique_id: &'static str) -> Ident {
	Ident::new(&format!("sr_api_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &'static str) -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-client" {
		TokenStream::new()
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!(
			#[doc(hidden)]
			mod #mod_name {
				pub extern crate substrate_client as sr_api_client;
			}
		)
	}.into()
}

/// Generates the access to the `subtrate_client` crate.
pub fn generate_crate_access(unique_id: &'static str) -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-client" {
		quote!( crate )
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!( self::#mod_name::sr_api_client )
	}.into()
}

/// Generates the name of the module that contains the trait declaration for the runtime.
pub fn generate_runtime_mod_name_for_trait(trait_: &Ident) -> Ident {
	Ident::new(&format!("runtime_decl_for_{}", trait_.to_string()), Span::call_site())
}

/// Fold the given `FnDecl` to make it usable on the client side.
pub fn fold_fn_decl_for_client_side(
	mut input: FnDecl,
	block_id: &TokenStream,
	crate_: &TokenStream
) -> FnDecl {
	// Add `&self, at:& BlockId` as parameters to each function at the beginning.
	input.inputs.insert(0, parse_quote!( at: &#block_id ));
	input.inputs.insert(0, parse_quote!( &self ));

	// Wrap the output in a `Result`
	input.output = {
		let generate_result = |ty: &Type| {
			parse_quote!( -> ::std::result::Result<#ty, #crate_::error::Error> )
		};

		match &input.output {
			syn::ReturnType::Default => generate_result(&parse_quote!( () )),
			syn::ReturnType::Type(_, ref ty) => generate_result(&ty),
		}
	};

	input
}
