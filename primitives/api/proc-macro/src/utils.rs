// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
	Ident::new(&format!("sp_api_hidden_includes_{}", unique_id), Span::call_site())
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
pub fn generate_hidden_includes(unique_id: &'static str) -> TokenStream {
	let mod_name = generate_hidden_includes_mod_name(unique_id);
	match crate_name("sp-api") {
		Ok(FoundCrate::Itself) => quote!(),
		Ok(FoundCrate::Name(client_name)) => {
			let client_name = Ident::new(&client_name, Span::call_site());
			quote!(
				#[doc(hidden)]
				mod #mod_name {
					pub extern crate #client_name as sp_api;
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
	if env::var("CARGO_PKG_NAME").unwrap() == "sp-api" {
		quote!( sp_api )
	} else {
		let mod_name = generate_hidden_includes_mod_name(unique_id);
		quote!( self::#mod_name::sp_api )
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
pub fn return_type_extract_type(rt: &ReturnType) -> Type {
	match rt {
		ReturnType::Default => parse_quote!( () ),
		ReturnType::Type(_, ref ty) => *ty.clone(),
	}
}

/// Replace the `_` (wild card) parameter names in the given signature with unique identifiers.
pub fn replace_wild_card_parameter_names(input: &mut Signature) {
	let mut generated_pattern_counter = 0;
	input.inputs.iter_mut().for_each(|arg| if let FnArg::Typed(arg) = arg {
		arg.pat = Box::new(
			generate_unique_pattern((*arg.pat).clone(), &mut generated_pattern_counter),
		);
	});
}

/// Fold the given `Signature` to make it usable on the client side.
pub fn fold_fn_decl_for_client_side(
	input: &mut Signature,
	block_id: &TokenStream,
	crate_: &TokenStream,
) {
	replace_wild_card_parameter_names(input);

	// Add `&self, at:& BlockId` as parameters to each function at the beginning.
	input.inputs.insert(0, parse_quote!( __runtime_api_at_param__: &#block_id ));
	input.inputs.insert(0, parse_quote!( &self ));

	// Wrap the output in a `Result`
	input.output = {
		let ty = return_type_extract_type(&input.output);
		parse_quote!( -> std::result::Result<#ty, #crate_::ApiError> )
	};
}

/// Generate an unique pattern based on the given counter, if the given pattern is a `_`.
pub fn generate_unique_pattern(pat: Pat, counter: &mut u32) -> Pat {
	match pat {
		Pat::Wild(_) => {
			let generated_name = Ident::new(
				&format!("__runtime_api_generated_name_{}__", counter),
				pat.span(),
			);
			*counter += 1;

			parse_quote!( #generated_name )
		},
		_ => pat,
	}
}

/// Allow `&self` in parameters of a method.
pub enum AllowSelfRefInParameters {
	/// Allows `&self` in parameters, but doesn't return it as part of the parameters.
	YesButIgnore,
	No,
}

/// Extracts the name, the type and `&` or ``(if it is a reference or not)
/// for each parameter in the given function signature.
pub fn extract_parameter_names_types_and_borrows(
	sig: &Signature,
	allow_self: AllowSelfRefInParameters,
) -> Result<Vec<(Pat, Type, Option<And>)>> {
	let mut result = Vec::new();
	let mut generated_pattern_counter = 0;
	for input in sig.inputs.iter() {
		match input {
			FnArg::Typed(arg) => {
				let (ty, borrow) = match &*arg.ty {
					Type::Reference(t) => {
						((*t.elem).clone(), Some(t.and_token))
					},
					t => { (t.clone(), None) },
				};

				let name = generate_unique_pattern(
					(*arg.pat).clone(),
					&mut generated_pattern_counter,
				);
				result.push((name, ty, borrow));
			},
			FnArg::Receiver(_) if matches!(allow_self, AllowSelfRefInParameters::No) => {
				return Err(Error::new(input.span(), "`self` parameter not supported!"))
			},
			FnArg::Receiver(recv) => {
				if recv.mutability.is_some() || recv.reference.is_none() {
					return Err(Error::new(recv.span(), "Only `&self` is supported!"))
				}
			},
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

/// Extract all types that appear in signatures in the given `ImplItem`'s.
///
/// If a type is a reference, the inner type is extracted (without the reference).
pub fn extract_all_signature_types(items: &[ImplItem]) -> Vec<Type> {
	items.iter()
		.filter_map(|i| match i {
			ImplItem::Method(method) => Some(&method.sig),
			_ => None,
		})
		.flat_map(|sig| {
			let ret_ty = match &sig.output {
				ReturnType::Default => None,
				ReturnType::Type(_, ty) => Some((**ty).clone()),
			};

			sig.inputs.iter().filter_map(|i| match i {
				FnArg::Typed(arg) => Some(&arg.ty),
				_ => None,
			}).map(|ty| match &**ty {
				Type::Reference(t) => (*t.elem).clone(),
				_ => (**ty).clone(),
			}).chain(ret_ty)
		})
		.collect()
}

/// Extracts the block type from a trait path.
///
/// It is expected that the block type is the first type in the generic arguments.
pub fn extract_block_type_from_trait_path(trait_: &Path) -> Result<&TypePath> {
	let span = trait_.span();
	let generics = trait_
		.segments
		.last()
		.ok_or_else(|| Error::new(span, "Empty path not supported"))?;

	match &generics.arguments {
		PathArguments::AngleBracketed(ref args) => {
			args.args.first().and_then(|v| match v {
				GenericArgument::Type(Type::Path(ref block)) => Some(block),
				_ => None
			}).ok_or_else(|| Error::new(args.span(), "Missing `Block` generic parameter."))
		},
		PathArguments::None => {
			let span = trait_.segments.last().as_ref().unwrap().span();
			Err(Error::new(span, "Missing `Block` generic parameter."))
		},
		PathArguments::Parenthesized(_) => {
			Err(Error::new(generics.arguments.span(), "Unexpected parentheses in path!"))
		},
	}
}

/// Should a qualified trait path be required?
///
/// e.g. `path::Trait` is qualified and `Trait` is not.
pub enum RequireQualifiedTraitPath {
	Yes,
	No,
}

/// Extract the trait that is implemented by the given `ItemImpl`.
pub fn extract_impl_trait<'a>(
	impl_: &'a ItemImpl,
	require: RequireQualifiedTraitPath,
) -> Result<&'a Path> {
	impl_.trait_.as_ref().map(|v| &v.1).ok_or_else(
		|| Error::new(impl_.span(), "Only implementation of traits are supported!")
	).and_then(|p| {
		if p.segments.len() > 1 || matches!(require, RequireQualifiedTraitPath::No) {
			Ok(p)
		} else {
			Err(
				Error::new(
					p.span(),
					"The implemented trait has to be referenced with a path, \
					e.g. `impl client::Core for Runtime`."
				)
			)
		}
	})
}
