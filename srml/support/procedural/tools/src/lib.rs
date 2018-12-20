// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

extern crate syn;
#[macro_use]
extern crate quote;
extern crate proc_macro2;

extern crate proc_macro;

#[macro_use] extern crate srml_support_procedural_tools_derive;

// reexport proc macros
pub use srml_support_procedural_tools_derive::*;

pub mod syn_ext;

#[macro_export]
macro_rules! custom_keyword_impl {
	($name:ident, $keyident:expr, $keydisp:expr) => {

		impl CustomKeyword for $name {
			fn ident() -> &'static str { $keyident }
			fn display() -> &'static str { $keydisp }
		}

	}
}

#[macro_export]
macro_rules! custom_keyword {
	($name:ident, $keyident:expr, $keydisp:expr) => {

		#[derive(Debug)]
		struct $name;

		custom_keyword_impl!($name, $keyident, $keydisp);

	}
}


// TODO following functions are copied from sr-api-macros : do a merge to get a unique procedural
// macro tooling crate (this crate path does not look good for it)

use proc_macro2::{TokenStream, Span};
use syn::Ident;

fn generate_hidden_includes_mod_name(unique_id: &str) -> Ident {
	Ident::new(&format!("sr_api_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the access to the `subtrate_client` crate.
pub fn generate_crate_access(unique_id: &str, def_crate: &str) -> TokenStream {
	if ::std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		quote!( crate )
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!( self::#mod_name::hidden_include )
	}.into()
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &str, def_crate: &str, crate_id: &str) -> TokenStream {
	let crate_id = Ident::new(crate_id, Span::call_site());
	if ::std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		TokenStream::new()
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!(
			#[doc(hidden)]
			mod #mod_name {
				pub extern crate #crate_id as hidden_include;
			}
		)
	}.into()
}

// fn to remove white spaces arount string types
// (basically whitespaces arount tokens)
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
