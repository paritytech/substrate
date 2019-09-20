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

//! Generates the extern host function for wasm and the host functions interface for native.

use crate::utils::{
	generate_crate_access, create_host_function_ident, get_function_argument_names,
	get_function_argument_types_without_ref,
};

use syn::{ItemTrait, TraitItemMethod, Result, ReturnType, Ident, TraitItem};

use proc_macro2::TokenStream;

use quote::quote;

/// Generate the interface.
pub fn generate(trait_def: &ItemTrait) -> Result<TokenStream> {
	let trait_name = &trait_def.ident;
	trait_def
		.items
		.iter()
		.filter_map(|i| match i {
			TraitItem::Method(ref method) => Some(method),
			_ => None,
		})
		.try_fold(TokenStream::new(), |mut t, m| {
			t.extend(generate_extern_host_function(m, trait_name)?);
			Ok(t)
		})
}

/// Generate the extern host function for the given method.
fn generate_extern_host_function(method: &TraitItemMethod, trait_name: &Ident) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let arg_types = get_function_argument_types_without_ref(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let function = create_host_function_ident(&method.sig.ident, trait_name);

	let output = match method.sig.output {
		ReturnType::Default => quote!(),
		ReturnType::Type(_, ref ty) => quote! {
			-> <#ty as #crate_::AsFFIArg>::FFIType
		}
	};

	Ok(
		quote! {
			#[cfg(not(feature = "std"))]
			extern "C" {
				pub fn #function (
					#( #arg_names: <#arg_types as #crate_::AsFFIArg>::FFIType ),*
				) #output;
			}
		}
	)
}
