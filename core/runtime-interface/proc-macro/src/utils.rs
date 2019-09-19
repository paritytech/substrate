// Copyright 2019 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>

//! Util function used by this crate.

use proc_macro2::{TokenStream, Span};

use syn::{Ident, Error};

use proc_macro_crate::crate_name;

use std::env;

use quote::quote;

/// Generates the include for the runtime-interface crate.
pub fn generate_runtime_interface_include() -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-runtime-interface" {
		TokenStream::new()
	} else {
		match crate_name("substrate-runtime-interface") {
			Ok(crate_name) => {
				let crate_name = Ident::new(&crate_name, Span::call_site());
				quote!(
					#[doc(hidden)]
					extern crate #crate_name as proc_macro_runtime_interface;
				)
			},
			Err(e) => {
				let err = Error::new(Span::call_site(), &e).to_compile_error();
				quote!( #err )
			}
		}
	}
}

/// Generates the access to the `substrate-runtime-interface` crate.
pub fn generate_crate_access() -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-runtime-interface" {
		quote!( crate )
	} else {
		quote!( proc_macro_runtime_interface )
	}
}

/// Create the host function identifier for the given function name.
pub fn create_host_function_ident(name: &Ident) -> Ident {
	Ident::new(&format!("ext_{}", name), Span::call_site())
}
