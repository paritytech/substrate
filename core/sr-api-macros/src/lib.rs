// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Macros for declaring and implementing runtime apis.

#![recursion_limit = "128"]
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;

use proc_macro2::{Span, TokenStream};

use quote::quote;
use syn::parse::{Parse, ParseStream, Result, Error};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Ident, Token, Type, ItemImpl, MethodSig, FnArg, Path, ImplItem};

use std::{env, iter};

/// The structure used for parsing the runtime api implementations.
struct RuntimeApiImpls {
	impls: Vec<ItemImpl>,
}

impl Parse for RuntimeApiImpls {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut impls = Vec::new();

		while input.peek(Token![impl]) {
			impls.push(ItemImpl::parse(input)?);
		}

		Ok(Self { impls })
	}
}

/// Generates the hidden includes that are required to make the macro independent from its scope.
fn generate_hidden_includes() -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-client" {
        TokenStream::new()
    } else {
        quote!(
			#[doc(hidden)]
			mod sr_api_hidden_includes {
				pub extern crate substrate_client as sr_api_client;
			}
		)
    }.into()
}

/// Generates the access to the `subtrate_client` crate.
fn generate_crate_access() -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "substrate-client" {
        quote!( crate )
    } else {
        quote!( self::sr_api_hidden_includes::sr_api_client )
    }.into()
}

/// Generates the call to the implementation of the requested function.
/// The generated code includes decoding of the input arguments and encoding of the output.
fn generate_impl_call(
	signature: &MethodSig,
	runtime: &Type,
	input: &Ident,
	impl_trait: &Path
) -> Result<TokenStream> {
	let mut pnames = Vec::new();
	let mut ptypes = Vec::new();
	for input in signature.decl.inputs.iter() {
		match input {
			FnArg::Captured(arg) => {
				pnames.push(&arg.pat);
				ptypes.push(&arg.ty);
			},
			_ => return Err(Error::new(
				input.span(), "Only function arguments with the following \
								pattern are accepted: `name: type`!"
			)),
		}
	}

	let c = generate_crate_access();
	let c_iter = iter::repeat(&c);
	let fn_name = &signature.ident;
	let fn_name_str = iter::repeat(fn_name.to_string());
	let input = iter::repeat(input);
	let pnames2 = pnames.clone();

	Ok(
		quote!(
			#(
				let #pnames : #ptypes = match #c_iter::runtime_api::Decode::decode(&mut #input) {
					Some(input) => input,
					None => panic!("Bad input data provided to {}", #fn_name_str),
				};
			)*

			let output = <#runtime as #impl_trait>::#fn_name(#( #pnames2 ),*);
			#c::runtime_api::Encode::encode(&output)
		).into()
	)
}

/// Extract the trait that is implemented in the given `ItemImpl`.
fn extract_impl_trait<'a>(impl_: &'a ItemImpl) -> Result<&'a Path> {
	impl_.trait_.as_ref().map(|v| &v.1).ok_or_else(
		|| Error::new(impl_.span(), "Only implementation of traits are supported!")
	).and_then(|p| {
		if p.segments.len() > 1 {
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

/// Generate all the implementation calls for the given functions.
fn generate_impl_calls(impls: &[ItemImpl], input: &Ident) -> Result<Vec<(Ident, TokenStream)>> {
	let mut impl_calls = Vec::new();

	for impl_ in impls {
		let impl_trait = extract_impl_trait(impl_)?;

		for item in &impl_.items {
			match item {
				ImplItem::Method(method) => {
					let impl_call = generate_impl_call(
						&method.sig,
						&impl_.self_ty,
						input,
						impl_trait
					)?;

					impl_calls.push((method.sig.ident.clone(), impl_call));
				},
				_ => {},
			}
		}
	}

	Ok(impl_calls)
}

/// Generate the dispatch function that is used in native to call into the runtime.
fn generate_dispatch_function(impls: &[ItemImpl]) -> Result<TokenStream> {
	let data = Ident::new("data", Span::call_site());
	let impl_calls = generate_impl_calls(impls, &data)?.into_iter().map(|(fn_name, impl_)| {
		let fn_name = fn_name.to_string();
		quote!( #fn_name => Some({ #impl_ }), )
	});

	Ok(quote!(
		#[cfg(feature = "std")]
		pub fn dispatch(method: &str, mut #data: &[u8]) -> Option<Vec<u8>> {
			match method {
				#( #impl_calls )*
				_ => None,
			}
		}
	).into())
}

/// Generate the interface functions that are used to call into the runtime in wasm.
fn generate_wasm_interface(impls: &[ItemImpl]) -> Result<TokenStream> {
	let input = Ident::new("input", Span::call_site());
	let c = generate_crate_access();
	let impl_calls = generate_impl_calls(impls, &input)?.into_iter().map(|(fn_name, impl_)| {
		quote!(
			#[cfg(not(feature = "std"))]
			#[no_mangle]
			pub fn #fn_name(input_data: *mut u8, input_len: usize) -> u64 {
				let mut #input = if input_len == 0 {
					&[0u8; 0]
				} else {
					unsafe {
						#c::runtime_api::slice::from_raw_parts(input_data, input_len)
					}
				};

				let output = { #impl_ };
				let res = output.as_ptr() as u64 + ((output.len() as u64) << 32);

				// Leak the output vector to avoid it being freed.
				// This is fine in a WASM context since the heap
				// will be discarded after the call.
				::core::mem::forget(output);
				res
			}
		)
	});

	Ok(quote!( #( #impl_calls )* ))
}

fn generate_get_node_block_ty(runtime: &Type) -> TokenStream {
	let crate_ = generate_crate_access();

	quote!( <#runtime as #crate_::runtime_api::GetNodeBlockType>::NodeBlock )
}

fn generate_runtime_api_base_structures(impls: &[ItemImpl]) -> Result<TokenStream> {
	let crate_ = generate_crate_access();
	let runtime = &impls.get(0).ok_or_else(||
		Error::new(Span::call_site(), "No api implementation given!")
	)?.self_ty;
	let block = generate_get_node_block_ty(runtime);
	let block_id = quote!( #crate_::runtime_api::BlockId<#block> );

	Ok(quote!(
		/// The struct that implements all runtime apis for a runtime.
		#[cfg(feature = "std")]
		pub struct RuntimeApi {
			call: ::std::ptr::NonNull<client::runtime_api::CallApiAt<#block>>,
			commit_on_success: ::std::cell::RefCell<bool>,
			initialised_block: ::std::cell::RefCell<Option<#block_id>>,
			changes: ::std::cell::RefCell<#crate_::runtime_api::OverlayedChanges>,
		}

		// `RuntimeApi` itself is not threadsafe. However, an instance is only available in a
		// `ApiRef` object and `ApiRef` also has an associated lifetime. This lifetimes makes it
		// impossible to move `RuntimeApi` into another thread.
		#[cfg(feature = "std")]
		unsafe impl Send for RuntimeApi {}
		#[cfg(feature = "std")]
		unsafe impl Sync for RuntimeApi {}

		#[cfg(feature = "std")]
		impl #crate_::runtime_api::ApiExt for RuntimeApi {
			fn map_api_result<F: FnOnce(&Self) -> Result<R, E>, R, E>(
				&self,
				map_call: F
			) -> Result<R, E> {
				*self.commit_on_success.borrow_mut() = false;
				let res = map_call(self);
				*self.commit_on_success.borrow_mut() = true;

				self.commit_on_ok(&res);

				res
			}
		}

		#[cfg(feature = "std")]
		impl #crate_::runtime_api::ConstructRuntimeApi<#block> for RuntimeApi {
			fn construct_runtime_api<'a, T: client::runtime_api::CallApiAt<#block>>(
				call: &'a T
			) -> #crate_::runtime_api::ApiRef<'a, Self> {
				RuntimeApi {
					call: unsafe {
						::std::ptr::NonNull::new_unchecked(
							call as &client::runtime_api::CallApiAt<#block> as *const _ as *mut _
						)
					},
					commit_on_success: true.into(),
					initialised_block: None.into(),
					changes: Default::default(),
				}.into()
			}
		}

		#[cfg(feature = "std")]
		impl RuntimeApi {
			fn call_api_at<A: Encode, R: Decode>(
				&self,
				at: &#block_id,
				function: &'static str,
				args: &A
			) -> client::error::Result<R> {
				let res = unsafe {
					self.call.as_ref().call_api_at(
						at,
						function,
						args.encode(),
						&mut *self.changes.borrow_mut(),
						&mut *self.initialised_block.borrow_mut()
					).and_then(|r|
						R::decode(&mut &r[..])
							.ok_or_else(||
								#crate_::error::ErrorKind::CallResultDecode(function).into()
							)
					)
				};

				self.commit_on_ok(&res);
				res
			}

			fn commit_on_ok<R, E>(&self, res: &Result<R, E>) {
				if *self.commit_on_success.borrow() {
					if res.is_err() {
						self.changes.borrow_mut().discard_prospective();
					} else {
						self.changes.borrow_mut().commit_prospective();
					}
				}
			}
		}
	))
}

/// Unwrap the given result, if it is an error, `compile_error!` will be generated.
fn unwrap_or_error(res: Result<TokenStream>) -> TokenStream {
	res.unwrap_or_else(|e| e.to_compile_error())
}

#[proc_macro]
pub fn impl_runtime_apis(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all impl blocks
	let RuntimeApiImpls { impls: api_impls } = parse_macro_input!(input as RuntimeApiImpls);
	let dispatch_impl = unwrap_or_error(generate_dispatch_function(&api_impls));
	let wasm_interface = unwrap_or_error(generate_wasm_interface(&api_impls));
	let hidden_includes = generate_hidden_includes();
	let base_runtime_api = unwrap_or_error(generate_runtime_api_base_structures(&api_impls));

	quote!(
		#hidden_includes

		#base_runtime_api

		#( #api_impls )*

		pub mod api {
			use super::*;

			#dispatch_impl

			#wasm_interface
		}
	).into()
}
