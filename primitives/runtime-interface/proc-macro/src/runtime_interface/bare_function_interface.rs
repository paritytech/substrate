// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Generates the bare function interface for a given trait definition.
//!
//! The bare functions are the ones that will be called by the user. On the native/host side, these
//! functions directly execute the provided implementation. On the wasm side, these
//! functions will prepare the parameters for the FFI boundary, call the external host function
//! exported into wasm and convert back the result.
//!
//! [`generate`] is the entry point for generating for each
//! trait method one bare function.
//!
//! [`function_for_method`] generates the bare
//! function per trait method. Each bare function contains both implementations. The implementations
//! are feature-gated, so that one is compiled for the native and the other for the wasm side.

use crate::utils::{
	create_exchangeable_host_function_ident, create_function_ident_with_version,
	generate_crate_access, get_function_argument_names, get_function_arguments,
	get_runtime_interface,
};

use syn::{
	parse_quote, spanned::Spanned, FnArg, Ident, ItemTrait, Result, Signature, TraitItemMethod,
};

use proc_macro2::{Span, TokenStream};

use quote::{quote, quote_spanned};

use std::iter;

fn not_feature_force_version(
	feature_force_version: &Vec<(String, String, u32)>,
	method: &TraitItemMethod,
) -> TokenStream {
	let method = method.sig.ident.to_string();
	for (feature, method_patch, _version_patch) in feature_force_version {
		if &method == method_patch {
			return quote! {
				#[cfg(not(feature=#feature))]
			}
		}
	}
	quote! {}
}

/// Generate one bare function per trait method. The name of the bare function is equal to the name
/// of the trait method.
pub fn generate(
	trait_def: &ItemTrait,
	is_wasm_only: bool,
	tracing: bool,
	feature_force_version: &Vec<(String, String, u32)>,
) -> Result<TokenStream> {
	let trait_name = &trait_def.ident;
	let runtime_interface = get_runtime_interface(trait_def)?;

	// latest version dispatch
	let token_stream: Result<TokenStream> = runtime_interface.latest_versions().try_fold(
		TokenStream::new(),
		|mut t, (latest_version, method)| {
			t.extend(function_for_method(
				method,
				latest_version,
				is_wasm_only,
				not_feature_force_version(&feature_force_version, &method),
			)?);
			Ok(t)
		},
	);

	// forced version
	let token_stream: Result<TokenStream> = feature_force_version.iter().try_fold(
		token_stream?,
		|mut t, (feature, method, force_version)| {
			// lookup method
			let (_, full_method) = runtime_interface
				.all_versions()
				.find(|(version, full_method)| {
					version == force_version && &full_method.sig.ident.to_string() == method
				})
				.expect("Force version not found");

			let feature_check = quote!(#[cfg(feature=#feature)]);
			t.extend(function_for_method(
				full_method,
				*force_version,
				is_wasm_only,
				feature_check,
			)?);
			Ok(t)
		},
	);

	// earlier versions compatibility dispatch (only std variant)
	let result: Result<TokenStream> =
		runtime_interface
			.all_versions()
			.try_fold(token_stream?, |mut t, (version, method)| {
				t.extend(function_std_impl(trait_name, method, version, is_wasm_only, tracing)?);
				Ok(t)
			});

	result
}

/// Generates the bare function implementation for the given method for the host and wasm side.
fn function_for_method(
	method: &TraitItemMethod,
	latest_version: u32,
	is_wasm_only: bool,
	feature_check: TokenStream,
) -> Result<TokenStream> {
	let std_impl = if !is_wasm_only {
		function_std_latest_impl(method, latest_version, &feature_check)?
	} else {
		quote!()
	};

	let no_std_impl = function_no_std_impl(method, feature_check)?;

	Ok(quote! {
		#std_impl

		#no_std_impl
	})
}

/// Generates the bare function implementation for `cfg(not(feature = "std"))`.
fn function_no_std_impl(
	method: &TraitItemMethod,
	feature_check: TokenStream,
) -> Result<TokenStream> {
	let function_name = &method.sig.ident;
	let host_function_name = create_exchangeable_host_function_ident(&method.sig.ident);
	let args = get_function_arguments(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let return_value = &method.sig.output;
	let attrs = method.attrs.iter().filter(|a| !a.path.is_ident("version"));

	Ok(quote! {
		#feature_check
		#[cfg(not(feature = "std"))]
		#( #attrs )*
		pub fn #function_name( #( #args, )* ) #return_value {
			// Call the host function
			#host_function_name.get()( #( #arg_names, )* )
		}
	})
}

/// Generate call to latest function version for `cfg((feature = "std")`
///
/// This should generate simple `fn func(..) { func_version_<latest_version>(..) }`.
fn function_std_latest_impl(
	method: &TraitItemMethod,
	latest_version: u32,
	feature_check: &TokenStream,
) -> Result<TokenStream> {
	let function_name = &method.sig.ident;
	let args = get_function_arguments(&method.sig).map(FnArg::Typed);
	let arg_names = get_function_argument_names(&method.sig).collect::<Vec<_>>();
	let return_value = &method.sig.output;
	let attrs = method.attrs.iter().filter(|a| !a.path.is_ident("version"));
	let latest_function_name =
		create_function_ident_with_version(&method.sig.ident, latest_version);

	Ok(quote_spanned! { method.span() =>
		#feature_check
		#[cfg(feature = "std")]
		#( #attrs )*
		pub fn #function_name( #( #args, )* ) #return_value {
			#latest_function_name(
				#( #arg_names, )*
			)
		}
	})
}

/// Generates the bare function implementation for `cfg(feature = "std")`.
fn function_std_impl(
	trait_name: &Ident,
	method: &TraitItemMethod,
	version: u32,
	is_wasm_only: bool,
	tracing: bool,
) -> Result<TokenStream> {
	let function_name = create_function_ident_with_version(&method.sig.ident, version);
	let function_name_str = function_name.to_string();

	let crate_ = generate_crate_access();
	let args = get_function_arguments(&method.sig).map(FnArg::Typed).chain(
		// Add the function context as last parameter when this is a wasm only interface.
		iter::from_fn(|| {
			if is_wasm_only {
				Some(parse_quote!(
					mut __function_context__: &mut dyn #crate_::sp_wasm_interface::FunctionContext
				))
			} else {
				None
			}
		})
		.take(1),
	);
	let return_value = &method.sig.output;
	let attrs = method.attrs.iter().filter(|a| !a.path.is_ident("version"));
	// Don't make the function public accessible when this is a wasm only interface.
	let call_to_trait = generate_call_to_trait(trait_name, method, version, is_wasm_only);
	let call_to_trait = if !tracing {
		call_to_trait
	} else {
		parse_quote!(
			#crate_::sp_tracing::within_span! { #crate_::sp_tracing::trace_span!(#function_name_str);
				#call_to_trait
			}
		)
	};

	Ok(quote_spanned! { method.span() =>
		#[cfg(feature = "std")]
		#( #attrs )*
		fn #function_name( #( #args, )* ) #return_value {
			#call_to_trait
		}
	})
}

/// Generate the call to the interface trait.
fn generate_call_to_trait(
	trait_name: &Ident,
	method: &TraitItemMethod,
	version: u32,
	is_wasm_only: bool,
) -> TokenStream {
	let crate_ = generate_crate_access();
	let method_name = create_function_ident_with_version(&method.sig.ident, version);
	let expect_msg =
		format!("`{}` called outside of an Externalities-provided environment.", method_name);
	let arg_names = get_function_argument_names(&method.sig);

	if takes_self_argument(&method.sig) {
		let instance = if is_wasm_only {
			Ident::new("__function_context__", Span::call_site())
		} else {
			Ident::new("__externalities__", Span::call_site())
		};

		let impl_ = quote!( #trait_name::#method_name(&mut #instance, #( #arg_names, )*) );

		if is_wasm_only {
			quote_spanned! { method.span() => #impl_ }
		} else {
			quote_spanned! { method.span() =>
				#crate_::with_externalities(|mut #instance| #impl_).expect(#expect_msg)
			}
		}
	} else {
		// The name of the trait the interface trait is implemented for
		let impl_trait_name = if is_wasm_only {
			quote!( #crate_::sp_wasm_interface::FunctionContext )
		} else {
			quote!( #crate_::Externalities )
		};

		quote_spanned! { method.span() =>
			<&mut dyn #impl_trait_name as #trait_name>::#method_name(
				#( #arg_names, )*
			)
		}
	}
}

/// Returns if the given `Signature` takes a `self` argument.
fn takes_self_argument(sig: &Signature) -> bool {
	matches!(sig.inputs.first(), Some(FnArg::Receiver(_)))
}
