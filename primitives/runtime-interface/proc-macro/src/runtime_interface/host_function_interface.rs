// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Generates the extern host functions and the implementation for these host functions.
//!
//! The extern host functions will be called by the bare function interface from the Wasm side.
//! The implementation of these host functions will be called on the host side from the Wasm
//! executor. These implementations call the bare function interface.

use crate::utils::{
	generate_crate_access, create_host_function_ident, get_function_argument_names,
	get_function_argument_types_without_ref, get_function_argument_types_ref_and_mut,
	get_function_argument_names_and_types_without_ref, get_function_arguments,
	get_function_argument_types, create_exchangeable_host_function_ident, get_runtime_interface,
	create_function_ident_with_version,
};

use syn::{
	ItemTrait, TraitItemMethod, Result, ReturnType, Ident, Pat, Error, Signature, spanned::Spanned,
};

use proc_macro2::{TokenStream, Span};

use quote::{quote, ToTokens};

use inflector::Inflector;

use std::iter::{Iterator, self};

/// Generate the extern host functions for wasm and the `HostFunctions` struct that provides the
/// implementations for the host functions on the host.
pub fn generate(trait_def: &ItemTrait, is_wasm_only: bool) -> Result<TokenStream> {
	let trait_name = &trait_def.ident;
	let extern_host_function_impls = get_runtime_interface(trait_def)?
		.latest_versions()
		.try_fold(TokenStream::new(), |mut t, (version, method)| {
			t.extend(generate_extern_host_function(method, version, trait_name)?);
			Ok::<_, Error>(t)
		})?;
	let exchangeable_host_functions = get_runtime_interface(trait_def)?
		.latest_versions()
		.try_fold(TokenStream::new(), |mut t, (_, m)| {
			t.extend(generate_exchangeable_host_function(m)?);
			Ok::<_, Error>(t)
		})?;
	let host_functions_struct = generate_host_functions_struct(trait_def, is_wasm_only)?;

	Ok(
		quote! {
			/// The implementations of the extern host functions. This special implementation module
			/// is required to change the extern host functions signature to
			/// `unsafe fn name(args) -> ret` to make the function implementations exchangeable.
			#[cfg(not(feature = "std"))]
			mod extern_host_function_impls {
				use super::*;

				#extern_host_function_impls
			}

			#exchangeable_host_functions

			#host_functions_struct
		}
	)
}

/// Generate the extern host function for the given method.
fn generate_extern_host_function(method: &TraitItemMethod, version: u32, trait_name: &Ident) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let args = get_function_arguments(&method.sig);
	let arg_types = get_function_argument_types_without_ref(&method.sig);
	let arg_types2 = get_function_argument_types_without_ref(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let arg_names2 = get_function_argument_names(&method.sig);
	let arg_names3 = get_function_argument_names(&method.sig);
	let function = &method.sig.ident;
	let ext_function = create_host_function_ident(&method.sig.ident, version, trait_name);
	let doc_string = format!(
		" Default extern host function implementation for [`super::{}`].",
		method.sig.ident,
	);
	let return_value = &method.sig.output;

	let ffi_return_value = match method.sig.output {
		ReturnType::Default => quote!(),
		ReturnType::Type(_, ref ty) => quote! {
			-> <#ty as #crate_::RIType>::FFIType
		},
	};

	let convert_return_value = match return_value {
		ReturnType::Default => quote!(),
		ReturnType::Type(_, ref ty) => quote! {
			<#ty as #crate_::wasm::FromFFIValue>::from_ffi_value(result)
		}
	};

	Ok(
		quote! {
			#[doc = #doc_string]
			pub fn #function ( #( #args ),* ) #return_value {
				extern "C" {
					/// The extern function.
					pub fn #ext_function (
						#( #arg_names: <#arg_types as #crate_::RIType>::FFIType ),*
					) #ffi_return_value;
				}

				// Generate all wrapped ffi values.
				#(
					let #arg_names2 = <#arg_types2 as #crate_::wasm::IntoFFIValue>::into_ffi_value(
						&#arg_names2,
					);
				)*

				let result = unsafe { #ext_function( #( #arg_names3.get() ),* ) };

				#convert_return_value
			}
		}
	)
}

/// Generate the host exchangeable function for the given method.
fn generate_exchangeable_host_function(method: &TraitItemMethod) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let arg_types = get_function_argument_types(&method.sig);
	let function = &method.sig.ident;
	let exchangeable_function = create_exchangeable_host_function_ident(&method.sig.ident);
	let doc_string = format!(" Exchangeable host function used by [`{}`].", method.sig.ident);
	let output = &method.sig.output;

	Ok(
		quote! {
			#[cfg(not(feature = "std"))]
			#[allow(non_upper_case_globals)]
			#[doc = #doc_string]
			pub static #exchangeable_function : #crate_::wasm::ExchangeableFunction<
				fn ( #( #arg_types ),* ) #output
			> = #crate_::wasm::ExchangeableFunction::new(extern_host_function_impls::#function);
		}
	)
}

/// Generate the `HostFunctions` struct that implements `wasm-interface::HostFunctions` to provide
/// implementations for the extern host functions.
fn generate_host_functions_struct(trait_def: &ItemTrait, is_wasm_only: bool) -> Result<TokenStream> {
	let crate_ = generate_crate_access();

	let host_functions = get_runtime_interface(trait_def)?
		.all_versions()
		.map(|(version, method)|
			generate_host_function_implementation(&trait_def.ident, method, version, is_wasm_only)
		)
		.collect::<Result<Vec<_>>>()?;

	Ok(
		quote! {
			/// Provides implementations for the extern host functions.
			#[cfg(feature = "std")]
			pub struct HostFunctions;

			#[cfg(feature = "std")]
			impl #crate_::sp_wasm_interface::HostFunctions for HostFunctions {
				fn host_functions() -> Vec<&'static dyn #crate_::sp_wasm_interface::Function> {
					vec![ #( #host_functions ),* ]
				}
			}
		}
	)
}

/// Generates the host function struct that implements `wasm_interface::Function` and returns a static
/// reference to this struct.
///
/// When calling from wasm into the host, we will call the `execute` function that calls the native
/// implementation of the function.
fn generate_host_function_implementation(
	trait_name: &Ident,
	method: &TraitItemMethod,
	version: u32,
	is_wasm_only: bool,
) -> Result<TokenStream> {
	let name = create_host_function_ident(&method.sig.ident, version, trait_name).to_string();
	let struct_name = Ident::new(&name.to_pascal_case(), Span::call_site());
	let crate_ = generate_crate_access();
	let signature = generate_wasm_interface_signature_for_host_function(&method.sig)?;
	let wasm_to_ffi_values = generate_wasm_to_ffi_values(
		&method.sig,
		trait_name,
	).collect::<Result<Vec<_>>>()?;
	let ffi_to_host_values = generate_ffi_to_host_value(&method.sig).collect::<Result<Vec<_>>>()?;
	let host_function_call = generate_host_function_call(&method.sig, version, is_wasm_only);
	let into_preallocated_ffi_value = generate_into_preallocated_ffi_value(&method.sig)?;
	let convert_return_value = generate_return_value_into_wasm_value(&method.sig);

	Ok(
		quote! {
			{
				struct #struct_name;

				impl #crate_::sp_wasm_interface::Function for #struct_name {
					fn name(&self) -> &str {
						#name
					}

					fn signature(&self) -> #crate_::sp_wasm_interface::Signature {
						#signature
					}

					fn execute(
						&self,
						__function_context__: &mut dyn #crate_::sp_wasm_interface::FunctionContext,
						args: &mut dyn Iterator<Item = #crate_::sp_wasm_interface::Value>,
					) -> std::result::Result<Option<#crate_::sp_wasm_interface::Value>, String> {
						#( #wasm_to_ffi_values )*
						#( #ffi_to_host_values )*
						#host_function_call
						#into_preallocated_ffi_value
						#convert_return_value
					}
				}

				&#struct_name as &dyn #crate_::sp_wasm_interface::Function
			}
		}
	)
}

/// Generate the `wasm_interface::Signature` for the given host function `sig`.
fn generate_wasm_interface_signature_for_host_function(sig: &Signature) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let return_value = match &sig.output {
		ReturnType::Type(_, ty) =>
			quote! {
				Some( <<#ty as #crate_::RIType>::FFIType as #crate_::sp_wasm_interface::IntoValue>::VALUE_TYPE )
			},
		ReturnType::Default => quote!( None ),
	};
	let arg_types = get_function_argument_types_without_ref(sig)
		.map(|ty| quote! {
			<<#ty as #crate_::RIType>::FFIType as #crate_::sp_wasm_interface::IntoValue>::VALUE_TYPE
		});

	Ok(
		quote! {
			#crate_::sp_wasm_interface::Signature {
				args: std::borrow::Cow::Borrowed(&[ #( #arg_types ),* ][..]),
				return_value: #return_value,
			}
		}
	)
}

/// Generate the code that converts the wasm values given to `HostFunctions::execute` into the FFI
/// values.
fn generate_wasm_to_ffi_values<'a>(
	sig: &'a Signature,
	trait_name: &'a Ident,
) -> impl Iterator<Item = Result<TokenStream>> + 'a {
	let crate_ = generate_crate_access();
	let function_name = &sig.ident;
	let error_message = format!(
		"Number of arguments given to `{}` does not match the expected number of arguments!",
		function_name,
	);

	get_function_argument_names_and_types_without_ref(sig)
		.map(move |(name, ty)| {
			let try_from_error = format!(
				"Could not instantiate `{}` from wasm value while executing `{}` from interface `{}`!",
				name.to_token_stream(),
				function_name,
				trait_name,
			);

			let var_name = generate_ffi_value_var_name(&name)?;

			Ok(quote! {
				let val = args.next().ok_or_else(|| #error_message)?;
				let #var_name = <
					<#ty as #crate_::RIType>::FFIType as #crate_::sp_wasm_interface::TryFromValue
				>::try_from_value(val).ok_or_else(|| #try_from_error)?;
			})
		})
}

/// Generate the code to convert the ffi values on the host to the host values using `FromFFIValue`.
fn generate_ffi_to_host_value<'a>(
	sig: &'a Signature,
) -> impl Iterator<Item = Result<TokenStream>> + 'a {
	let mut_access = get_function_argument_types_ref_and_mut(sig);
	let crate_ = generate_crate_access();

	get_function_argument_names_and_types_without_ref(sig)
		.zip(mut_access.map(|v| v.and_then(|m| m.1)))
		.map(move |((name, ty), mut_access)| {
			let ffi_value_var_name = generate_ffi_value_var_name(&name)?;

			Ok(
				quote! {
					let #mut_access #name = <#ty as #crate_::host::FromFFIValue>::from_ffi_value(
						__function_context__,
						#ffi_value_var_name,
					)?;
				}
			)
		})
}

/// Generate the code to call the host function and the ident that stores the result.
fn generate_host_function_call(sig: &Signature, version: u32, is_wasm_only: bool) -> TokenStream {
	let host_function_name = create_function_ident_with_version(&sig.ident, version);
	let result_var_name = generate_host_function_result_var_name(&sig.ident);
	let ref_and_mut = get_function_argument_types_ref_and_mut(sig).map(|ram|
		ram.map(|(vr, vm)| quote!(#vr #vm))
	);
	let names = get_function_argument_names(sig);

	let var_access = names.zip(ref_and_mut)
		.map(|(n, ref_and_mut)| {
			quote!( #ref_and_mut #n )
		})
		// If this is a wasm only interface, we add the function context as last parameter.
		.chain(
			iter::from_fn(|| if is_wasm_only { Some(quote!(__function_context__)) } else { None })
				.take(1)
		);

	quote! {
		let #result_var_name = #host_function_name ( #( #var_access ),* );
	}
}

/// Generate the variable name that stores the result of the host function.
fn generate_host_function_result_var_name(name: &Ident) -> Ident {
	Ident::new(&format!("{}_result", name), Span::call_site())
}

/// Generate the variable name that stores the FFI value.
fn generate_ffi_value_var_name(pat: &Pat) -> Result<Ident> {
	match pat {
		Pat::Ident(pat_ident) => {
			if let Some(by_ref) = pat_ident.by_ref {
				Err(Error::new(by_ref.span(), "`ref` not supported!"))
			} else if let Some(sub_pattern) = &pat_ident.subpat {
				Err(Error::new(sub_pattern.0.span(), "Not supported!"))
			} else {
				Ok(Ident::new(&format!("{}_ffi_value", pat_ident.ident), Span::call_site()))
			}
		}
		_ => Err(Error::new(pat.span(), "Not supported as variable name!"))
	}
}

/// Generate code that copies data from the host back to preallocated wasm memory.
///
/// Any argument that is given as `&mut` is interpreted as preallocated memory and it is expected
/// that the type implements `IntoPreAllocatedFFIValue`.
fn generate_into_preallocated_ffi_value(sig: &Signature) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let ref_and_mut = get_function_argument_types_ref_and_mut(sig).map(|ram|
		ram.and_then(|(vr, vm)| vm.map(|v| (vr, v)))
	);
	let names_and_types = get_function_argument_names_and_types_without_ref(sig);

	ref_and_mut.zip(names_and_types)
		.filter_map(|(ram, (name, ty))| ram.map(|_| (name, ty)))
		.map(|(name, ty)| {
			let ffi_var_name = generate_ffi_value_var_name(&name)?;

			Ok(
				quote! {
					<#ty as #crate_::host::IntoPreallocatedFFIValue>::into_preallocated_ffi_value(
						#name,
						__function_context__,
						#ffi_var_name,
					)?;
				}
			)
		})
		.collect()
}

/// Generate the code that converts the return value into the appropriate wasm value.
fn generate_return_value_into_wasm_value(sig: &Signature) -> TokenStream {
	let crate_ = generate_crate_access();

	match &sig.output {
		ReturnType::Default => quote!( Ok(None) ),
		ReturnType::Type(_, ty) => {
			let result_var_name = generate_host_function_result_var_name(&sig.ident);

			quote! {
				<#ty as #crate_::host::IntoFFIValue>::into_ffi_value(
					#result_var_name,
					__function_context__,
				).map(#crate_::sp_wasm_interface::IntoValue::into_value).map(Some)
			}
		}
	}
}
