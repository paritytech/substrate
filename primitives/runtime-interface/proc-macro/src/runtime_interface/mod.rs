// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use crate::utils::generate_runtime_interface_include;

use proc_macro2::{Span, TokenStream};

use syn::{Ident, ItemTrait, Result};

use inflector::Inflector;

use quote::quote;

mod bare_function_interface;
mod host_function_interface;
mod trait_decl_impl;

/// Custom keywords supported by the `runtime_interface` attribute.
pub mod keywords {
	// Custom keyword `wasm_only` that can be given as attribute to [`runtime_interface`].
	syn::custom_keyword!(wasm_only);
	// Disable tracing-macros added to the [`runtime_interface`] by specifying this optional entry
	syn::custom_keyword!(no_tracing);
}

/// Implementation of the `runtime_interface` attribute.
///
/// It expects the trait definition the attribute was put above and if this should be an wasm only
/// interface.
pub fn runtime_interface_impl(
	trait_def: ItemTrait,
	is_wasm_only: bool,
	tracing: bool,
) -> Result<TokenStream> {
	let bare_functions = bare_function_interface::generate(&trait_def, is_wasm_only, tracing)?;
	let crate_include = generate_runtime_interface_include();
	let mod_name = Ident::new(&trait_def.ident.to_string().to_snake_case(), Span::call_site());
	let trait_decl_impl = trait_decl_impl::process(&trait_def, is_wasm_only)?;
	let host_functions = host_function_interface::generate(&trait_def, is_wasm_only)?;
	let vis = trait_def.vis;
	let attrs = &trait_def.attrs;

	let res = quote! {
		#( #attrs )*
		#vis mod #mod_name {
			use super::*;
			#crate_include

			#bare_functions

			#trait_decl_impl

			#host_functions
		}
	};

	Ok(res)
}
