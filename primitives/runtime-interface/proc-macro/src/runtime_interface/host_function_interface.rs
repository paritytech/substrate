// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	create_exchangeable_host_function_ident, create_function_ident_with_version,
	create_host_function_ident, generate_crate_access, get_function_argument_names,
	get_function_argument_names_and_types_without_ref, get_function_argument_types,
	get_function_argument_types_ref_and_mut, get_function_argument_types_without_ref,
	get_function_arguments, get_runtime_interface, RuntimeInterfaceFunction,
};

use syn::{
	spanned::Spanned, Error, Ident, ItemTrait, Pat, Result, ReturnType, Signature, TraitItemFn,
};

use proc_macro2::{Span, TokenStream};

use quote::quote;

use inflector::Inflector;

use std::iter::Iterator;

/// Generate the extern host functions for wasm and the `HostFunctions` struct that provides the
/// implementations for the host functions on the host.
pub fn generate(trait_def: &ItemTrait, is_wasm_only: bool) -> Result<TokenStream> {
	let trait_name = &trait_def.ident;
	let extern_host_function_impls = get_runtime_interface(trait_def)?
		.latest_versions_to_call()
		.try_fold(TokenStream::new(), |mut t, (version, method)| {
			t.extend(generate_extern_host_function(method, version, trait_name)?);
			Ok::<_, Error>(t)
		})?;
	let exchangeable_host_functions = get_runtime_interface(trait_def)?
		.latest_versions_to_call()
		.try_fold(TokenStream::new(), |mut t, (_, m)| {
		t.extend(generate_exchangeable_host_function(m)?);
		Ok::<_, Error>(t)
	})?;
	let host_functions_struct = generate_host_functions_struct(trait_def, is_wasm_only)?;

	Ok(quote! {
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
	})
}

/// Generate the extern host function for the given method.
fn generate_extern_host_function(
	method: &TraitItemFn,
	version: u32,
	trait_name: &Ident,
) -> Result<TokenStream> {
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
		},
	};

	Ok(quote! {
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
	})
}

/// Generate the host exchangeable function for the given method.
fn generate_exchangeable_host_function(method: &TraitItemFn) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let arg_types = get_function_argument_types(&method.sig);
	let function = &method.sig.ident;
	let exchangeable_function = create_exchangeable_host_function_ident(&method.sig.ident);
	let doc_string = format!(" Exchangeable host function used by [`{}`].", method.sig.ident);
	let output = &method.sig.output;

	Ok(quote! {
		#[cfg(not(feature = "std"))]
		#[allow(non_upper_case_globals)]
		#[doc = #doc_string]
		pub static #exchangeable_function : #crate_::wasm::ExchangeableFunction<
			fn ( #( #arg_types ),* ) #output
		> = #crate_::wasm::ExchangeableFunction::new(extern_host_function_impls::#function);
	})
}

/// Generate the `HostFunctions` struct that implements `wasm-interface::HostFunctions` to provide
/// implementations for the extern host functions.
fn generate_host_functions_struct(
	trait_def: &ItemTrait,
	is_wasm_only: bool,
) -> Result<TokenStream> {
	let crate_ = generate_crate_access();

	let mut host_function_impls = Vec::new();
	let mut host_function_names = Vec::new();
	let mut register_bodies = Vec::new();
	for (version, method) in get_runtime_interface(trait_def)?.all_versions() {
		let (implementation, name, register_body) =
			generate_host_function_implementation(&trait_def.ident, method, version, is_wasm_only)?;
		host_function_impls.push(implementation);
		host_function_names.push(name);
		register_bodies.push(register_body);
	}

	Ok(quote! {
		#(#host_function_impls)*

		/// Provides implementations for the extern host functions.
		#[cfg(feature = "std")]
		pub struct HostFunctions;

		#[cfg(feature = "std")]
		impl #crate_::sp_wasm_interface::HostFunctions for HostFunctions {
			fn host_functions() -> Vec<&'static dyn #crate_::sp_wasm_interface::Function> {
				vec![ #( &#host_function_names as &dyn #crate_::sp_wasm_interface::Function ),* ]
			}

			#crate_::sp_wasm_interface::if_wasmtime_is_enabled! {
				fn register_static<T>(registry: &mut T) -> core::result::Result<(), T::Error>
					where T: #crate_::sp_wasm_interface::HostFunctionRegistry
				{
					#(#register_bodies)*
					Ok(())
				}
			}
		}
	})
}

/// Generates the host function struct that implements `wasm_interface::Function` and returns a
/// static reference to this struct.
///
/// When calling from wasm into the host, we will call the `execute` function that calls the native
/// implementation of the function.
fn generate_host_function_implementation(
	trait_name: &Ident,
	method: &RuntimeInterfaceFunction,
	version: u32,
	is_wasm_only: bool,
) -> Result<(TokenStream, Ident, TokenStream)> {
	let name = create_host_function_ident(&method.sig.ident, version, trait_name).to_string();
	let struct_name = Ident::new(&name.to_pascal_case(), Span::call_site());
	let crate_ = generate_crate_access();
	let signature = generate_wasm_interface_signature_for_host_function(&method.sig)?;

	let fn_name = create_function_ident_with_version(&method.sig.ident, version);
	let ref_and_mut = get_function_argument_types_ref_and_mut(&method.sig);

	// List of variable names containing WASM FFI-compatible arguments.
	let mut ffi_names = Vec::new();

	// List of `$name: $ty` tokens containing WASM FFI-compatible arguments.
	let mut ffi_args_prototype = Vec::new();

	// List of variable names containing arguments already converted into native Rust types.
	// Also includes the preceding `&` or `&mut`. To be used to call the actual implementation of
	// the host function.
	let mut host_names_with_ref = Vec::new();

	// List of code snippets to copy over the results returned from a host function through
	// any `&mut` arguments back into WASM's linear memory.
	let mut copy_data_into_ref_mut_args = Vec::new();

	// List of code snippets to convert dynamic FFI args (`Value` enum) into concrete static FFI
	// types (`u32`, etc.).
	let mut convert_args_dynamic_ffi_to_static_ffi = Vec::new();

	// List of code snippets to convert static FFI args (`u32`, etc.) into native Rust types.
	let mut convert_args_static_ffi_to_host = Vec::new();

	for ((host_name, host_ty), ref_and_mut) in
		get_function_argument_names_and_types_without_ref(&method.sig).zip(ref_and_mut)
	{
		let ffi_name = generate_ffi_value_var_name(&host_name)?;
		let host_name_ident = match *host_name {
			Pat::Ident(ref pat_ident) => pat_ident.ident.clone(),
			_ => unreachable!("`generate_ffi_value_var_name` above would return an error on `Pat` != `Ident`; qed"),
		};

		let ffi_ty = quote! { <#host_ty as #crate_::RIType>::FFIType };
		ffi_args_prototype.push(quote! { #ffi_name: #ffi_ty });
		ffi_names.push(quote! { #ffi_name });

		let convert_arg_error = format!(
			"could not marshal the '{}' argument through the WASM FFI boundary while executing '{}' from interface '{}'",
			host_name_ident,
			method.sig.ident,
			trait_name
		);
		convert_args_static_ffi_to_host.push(quote! {
			let mut #host_name = <#host_ty as #crate_::host::FromFFIValue>::from_ffi_value(__function_context__, #ffi_name)
				.map_err(|err| format!("{}: {}", err, #convert_arg_error))?;
		});

		let ref_and_mut_tokens =
			ref_and_mut.map(|(token_ref, token_mut)| quote!(#token_ref #token_mut));

		host_names_with_ref.push(quote! { #ref_and_mut_tokens #host_name });

		if ref_and_mut.map(|(_, token_mut)| token_mut.is_some()).unwrap_or(false) {
			copy_data_into_ref_mut_args.push(quote! {
				<#host_ty as #crate_::host::IntoPreallocatedFFIValue>::into_preallocated_ffi_value(
					#host_name,
					__function_context__,
					#ffi_name,
				)?;
			});
		}

		let arg_count_mismatch_error = format!(
			"missing argument '{}': number of arguments given to '{}' from interface '{}' does not match the expected number of arguments",
			host_name_ident,
			method.sig.ident,
			trait_name
		);
		convert_args_dynamic_ffi_to_static_ffi.push(quote! {
			let #ffi_name = args.next().ok_or_else(|| #arg_count_mismatch_error.to_owned())?;
			let #ffi_name: #ffi_ty = #crate_::sp_wasm_interface::TryFromValue::try_from_value(#ffi_name)
				.ok_or_else(|| #convert_arg_error.to_owned())?;
		});
	}

	let ffi_return_ty = match &method.sig.output {
		ReturnType::Type(_, ty) => quote! { <#ty as #crate_::RIType>::FFIType },
		ReturnType::Default => quote! { () },
	};

	let convert_return_value_host_to_static_ffi = match &method.sig.output {
		ReturnType::Type(_, ty) => quote! {
			let __result__ = <#ty as #crate_::host::IntoFFIValue>::into_ffi_value(
				__result__,
				__function_context__
			);
		},
		ReturnType::Default => quote! {
			let __result__ = Ok(__result__);
		},
	};

	let convert_return_value_static_ffi_to_dynamic_ffi = match &method.sig.output {
		ReturnType::Type(_, _) => quote! {
			let __result__ = Ok(Some(#crate_::sp_wasm_interface::IntoValue::into_value(__result__)));
		},
		ReturnType::Default => quote! {
			let __result__ = Ok(None);
		},
	};

	if is_wasm_only {
		host_names_with_ref.push(quote! {
			__function_context__
		});
	}

	let implementation = quote! {
		#[cfg(feature = "std")]
		struct #struct_name;

		#[cfg(feature = "std")]
		impl #struct_name {
			fn call(
				__function_context__: &mut dyn #crate_::sp_wasm_interface::FunctionContext,
				#(#ffi_args_prototype),*
			) -> std::result::Result<#ffi_return_ty, String> {
				#(#convert_args_static_ffi_to_host)*
				let __result__ = #fn_name(#(#host_names_with_ref),*);
				#(#copy_data_into_ref_mut_args)*
				#convert_return_value_host_to_static_ffi
				__result__
			}
		}

		#[cfg(feature = "std")]
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
				#(#convert_args_dynamic_ffi_to_static_ffi)*
				let __result__ = Self::call(
					__function_context__,
					#(#ffi_names),*
				)?;
				#convert_return_value_static_ffi_to_dynamic_ffi
				__result__
			}
		}
	};

	let register_body = quote! {
		registry.register_static(
			#crate_::sp_wasm_interface::Function::name(&#struct_name),
			|mut caller: #crate_::sp_wasm_interface::wasmtime::Caller<T::State>, #(#ffi_args_prototype),*|
				-> std::result::Result<#ffi_return_ty, #crate_::sp_wasm_interface::anyhow::Error>
			{
				T::with_function_context(caller, move |__function_context__| {
					let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
						#struct_name::call(
							__function_context__,
							#(#ffi_names,)*
						).map_err(#crate_::sp_wasm_interface::anyhow::Error::msg)
					}));
					match result {
						Ok(result) => result,
						Err(panic) => {
							let message =
								if let Some(message) = panic.downcast_ref::<String>() {
									format!("host code panicked while being called by the runtime: {}", message)
								} else if let Some(message) = panic.downcast_ref::<&'static str>() {
									format!("host code panicked while being called by the runtime: {}", message)
								} else {
									"host code panicked while being called by the runtime".to_owned()
								};
							return Err(#crate_::sp_wasm_interface::anyhow::Error::msg(message));
						}
					}
				})
			}
		)?;
	};

	Ok((implementation, struct_name, register_body))
}

/// Generate the `wasm_interface::Signature` for the given host function `sig`.
fn generate_wasm_interface_signature_for_host_function(sig: &Signature) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let return_value = match &sig.output {
		ReturnType::Type(_, ty) => quote! {
			Some( <<#ty as #crate_::RIType>::FFIType as #crate_::sp_wasm_interface::IntoValue>::VALUE_TYPE )
		},
		ReturnType::Default => quote!(None),
	};
	let arg_types = get_function_argument_types_without_ref(sig).map(|ty| {
		quote! {
			<<#ty as #crate_::RIType>::FFIType as #crate_::sp_wasm_interface::IntoValue>::VALUE_TYPE
		}
	});

	Ok(quote! {
		#crate_::sp_wasm_interface::Signature {
			args: std::borrow::Cow::Borrowed(&[ #( #arg_types ),* ][..]),
			return_value: #return_value,
		}
	})
}

/// Generate the variable name that stores the FFI value.
fn generate_ffi_value_var_name(pat: &Pat) -> Result<Ident> {
	match pat {
		Pat::Ident(pat_ident) =>
			if let Some(by_ref) = pat_ident.by_ref {
				Err(Error::new(by_ref.span(), "`ref` not supported!"))
			} else if let Some(sub_pattern) = &pat_ident.subpat {
				Err(Error::new(sub_pattern.0.span(), "Not supported!"))
			} else {
				Ok(Ident::new(&format!("{}_ffi_value", pat_ident.ident), Span::call_site()))
			},
		_ => Err(Error::new(pat.span(), "Not supported as variable name!")),
	}
}
