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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Procedural macros for generating runtime interfaces.

extern crate proc_macro;

use proc_macro2::{Span, TokenStream};

use syn::{parse_macro_input, Ident, ItemTrait, Result};

use quote::quote;

use inflector::Inflector;

use utils::generate_runtime_interface_include;

mod bare_function_interface;
mod host_function_interface;
mod trait_decl_impl;
mod utils;

#[proc_macro_attribute]
pub fn runtime_interface(
	_: proc_macro::TokenStream,
	input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let trait_def = parse_macro_input!(input as ItemTrait);

	runtime_interface_impl(trait_def).unwrap_or_else(|e| e.to_compile_error()).into()
}

fn runtime_interface_impl(trait_def: ItemTrait) -> Result<TokenStream> {
	let bare_functions = bare_function_interface::generate(&trait_def)?;
	let crate_include = generate_runtime_interface_include();
	let mod_name = Ident::new(&trait_def.ident.to_string().to_snake_case(), Span::call_site());
	let trait_decl_impl = trait_decl_impl::process(&trait_def)?;
	let host_functions = host_function_interface::generate(&trait_def)?;

	let res = quote! {
		pub mod #mod_name {
			use super::*;
			#crate_include

			#bare_functions

			#trait_decl_impl

			#host_functions
		}
	};

	println!("{}", res);

	Ok(res)
}
