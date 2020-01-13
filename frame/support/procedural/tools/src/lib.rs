// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Proc macro helpers for procedural macros
// end::description[]

// reexport proc macros
pub use frame_support_procedural_tools_derive::*;

use proc_macro_crate::crate_name;
use syn::parse::Error;
use quote::quote;

pub mod syn_ext;

// FIXME #1569, remove the following functions, which are copied from sp-api-macros
use proc_macro2::{TokenStream, Span};
use syn::Ident;

fn generate_hidden_includes_mod_name(unique_id: &str) -> Ident {
	Ident::new(&format!("sp_api_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the access to the `frame-support` crate.
pub fn generate_crate_access(unique_id: &str, def_crate: &str) -> TokenStream {
	if std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		quote::quote!( frame_support )
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote::quote!( self::#mod_name::hidden_include )
	}
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &str, def_crate: &str) -> TokenStream {
	if std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		TokenStream::new()
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);

		match crate_name(def_crate) {
			Ok(name) => {
				let name = Ident::new(&name, Span::call_site());
				quote::quote!(
					#[doc(hidden)]
					mod #mod_name {
						pub extern crate #name as hidden_include;
					}
				)
			},
			Err(e) => {
				let err = Error::new(Span::call_site(), &e).to_compile_error();
				quote!( #err )
			}
		}

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
