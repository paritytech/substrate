// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
use syn::{Result, Ident, FnDecl, parse_quote, Type, Pat, spanned::Spanned, FnArg, Error};
use quote::quote;
use std::env;
use proc_macro_crate::crate_name;

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
		match crate_name("substrate-client") {
			Ok(client_name) => {
				let client_name = Ident::new(&client_name, Span::call_site());
				quote!(
					#[doc(hidden)]
					mod #mod_name {
						pub extern crate #client_name as sr_api_client;
					}
				)
			},
			Err(e) => {
				let err = Error::new(Span::call_site(), &e).to_compile_error();
				quote!( #err )
			}
		}

	}.into()
}

/// Generates the access to the `substrate_client` crate.
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

/// Generates a name for a method that needs to be implemented in the runtime for the client side.
pub fn generate_method_runtime_api_impl_name(trait_: &Ident, method: &Ident) -> Ident {
	Ident::new(&format!("{}_{}_runtime_api_impl", trait_, method), Span::call_site())
}

/// Get the type of a `syn::ReturnType`.
pub fn return_type_extract_type(rt: &syn::ReturnType) -> Type {
	match rt {
		syn::ReturnType::Default => parse_quote!( () ),
		syn::ReturnType::Type(_, ref ty) => *ty.clone(),
	}
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
		let ty = return_type_extract_type(&input.output);
		parse_quote!( -> ::std::result::Result<#ty, #crate_::error::Error> )
	};

	input
}

/// Generate an unique pattern based on the given counter, if the given pattern is a `_`.
pub fn generate_unique_pattern(pat: Pat, counter: &mut u32) -> Pat {
	match pat {
		Pat::Wild(_) => {
			let generated_name = Ident::new(
				&format!("runtime_api_generated_name_{}", counter),
				pat.span()
			);
			*counter += 1;

			parse_quote!( #generated_name )
		},
		_ => pat,
	}
}

/// Extracts the name, the type and `&` or ``(if it is a reference or not)
/// for each parameter in the given function declaration.
pub fn extract_parameter_names_types_and_borrows(fn_decl: &FnDecl)
	-> Result<Vec<(Pat, Type, TokenStream)>>
{
	let mut result = Vec::new();
	let mut generated_pattern_counter = 0;
	for input in fn_decl.inputs.iter() {
		match input {
			FnArg::Captured(arg) => {
				let (ty, borrow) = match &arg.ty {
					Type::Reference(t) => {
						let ty = &t.elem;
						(parse_quote!( #ty ), quote!( & ))
					},
					t => { (t.clone(), quote!()) },
				};

				let name =
					generate_unique_pattern(arg.pat.clone(), &mut generated_pattern_counter);
				result.push((name, ty, borrow));
			},
			_ => {
				return Err(
					Error::new(
						input.span(),
						"Only function arguments with the following \
						pattern are accepted: `name: type`!"
					)
				)
			}
		}
	}

	Ok(result)
}

/// Generates the name for the native call generator function.
pub fn generate_native_call_generator_fn_name(fn_name: &Ident) -> Ident {
	Ident::new(&format!("{}_native_call_generator", fn_name.to_string()), Span::call_site())
}

/// Generates the name for the call api at function.
pub fn generate_call_api_at_fn_name(fn_name: &Ident) -> Ident {
	Ident::new(&format!("{}_call_api_at", fn_name.to_string()), Span::call_site())
}

/// Prefix the given function with the trait name.
pub fn prefix_function_with_trait<F: ToString>(trait_: &Ident, function: &F) -> String {
	format!("{}_{}", trait_.to_string(), function.to_string())
}
