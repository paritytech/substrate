// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use crate::utils::{
	extract_all_signature_types, extract_block_type_from_trait_path, extract_impl_trait,
	extract_parameter_names_types_and_borrows, generate_crate_access, generate_hidden_includes,
	generate_runtime_mod_name_for_trait, parse_runtime_api_version, prefix_function_with_trait,
	versioned_trait_name, AllowSelfRefInParameters, RequireQualifiedTraitPath,
};

use crate::common::API_VERSION_ATTRIBUTE;

use proc_macro2::{Span, TokenStream};

use quote::quote;

use syn::{
	fold::{self, Fold},
	parse::{Error, Parse, ParseStream, Result},
	parse_macro_input, parse_quote,
	spanned::Spanned,
	Attribute, Ident, ImplItem, ItemImpl, Path, Signature, Type, TypePath,
};

use std::collections::HashSet;

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "IMPL_RUNTIME_APIS";

/// The structure used for parsing the runtime api implementations.
struct RuntimeApiImpls {
	impls: Vec<ItemImpl>,
}

impl Parse for RuntimeApiImpls {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut impls = Vec::new();

		while !input.is_empty() {
			impls.push(ItemImpl::parse(input)?);
		}

		if impls.is_empty() {
			Err(Error::new(Span::call_site(), "No api implementation given!"))
		} else {
			Ok(Self { impls })
		}
	}
}

/// Generates the call to the implementation of the requested function.
/// The generated code includes decoding of the input arguments and encoding of the output.
fn generate_impl_call(
	signature: &Signature,
	runtime: &Type,
	input: &Ident,
	impl_trait: &Path,
) -> Result<TokenStream> {
	let params =
		extract_parameter_names_types_and_borrows(signature, AllowSelfRefInParameters::No)?;

	let c = generate_crate_access(HIDDEN_INCLUDES_ID);
	let fn_name = &signature.ident;
	let fn_name_str = fn_name.to_string();
	let pnames = params.iter().map(|v| &v.0);
	let pnames2 = params.iter().map(|v| &v.0);
	let ptypes = params.iter().map(|v| &v.1);
	let pborrow = params.iter().map(|v| &v.2);

	Ok(quote!(
		let (#( #pnames ),*) : ( #( #ptypes ),* ) =
			match #c::DecodeLimit::decode_all_with_depth_limit(
				#c::MAX_EXTRINSIC_DEPTH,
				&mut #input,
			) {
				Ok(res) => res,
				Err(e) => panic!("Bad input data provided to {}: {}", #fn_name_str, e),
			};

		#[allow(deprecated)]
		<#runtime as #impl_trait>::#fn_name(#( #pborrow #pnames2 ),*)
	))
}

/// Generate all the implementation calls for the given functions.
fn generate_impl_calls(
	impls: &[ItemImpl],
	input: &Ident,
) -> Result<Vec<(Ident, Ident, TokenStream, Vec<Attribute>)>> {
	let mut impl_calls = Vec::new();

	for impl_ in impls {
		let trait_api_ver = extract_api_version(&impl_.attrs, impl_.span())?;
		let impl_trait_path = extract_impl_trait(impl_, RequireQualifiedTraitPath::Yes)?;
		let impl_trait = extend_with_runtime_decl_path(impl_trait_path.clone());
		let impl_trait = extend_with_api_version(impl_trait, trait_api_ver);
		let impl_trait_ident = &impl_trait_path
			.segments
			.last()
			.ok_or_else(|| Error::new(impl_trait_path.span(), "Empty trait path not possible!"))?
			.ident;

		for item in &impl_.items {
			if let ImplItem::Method(method) = item {
				let impl_call =
					generate_impl_call(&method.sig, &impl_.self_ty, input, &impl_trait)?;

				impl_calls.push((
					impl_trait_ident.clone(),
					method.sig.ident.clone(),
					impl_call,
					filter_cfg_attrs(&impl_.attrs),
				));
			}
		}
	}

	Ok(impl_calls)
}

/// Generate the dispatch function that is used in native to call into the runtime.
fn generate_dispatch_function(impls: &[ItemImpl]) -> Result<TokenStream> {
	let data = Ident::new("__sp_api__input_data", Span::call_site());
	let c = generate_crate_access(HIDDEN_INCLUDES_ID);
	let impl_calls =
		generate_impl_calls(impls, &data)?
			.into_iter()
			.map(|(trait_, fn_name, impl_, attrs)| {
				let name = prefix_function_with_trait(&trait_, &fn_name);
				quote!(
					#( #attrs )*
					#name => Some(#c::Encode::encode(&{ #impl_ })),
				)
			});

	Ok(quote!(
		#[cfg(feature = "std")]
		pub fn dispatch(method: &str, mut #data: &[u8]) -> Option<Vec<u8>> {
			match method {
				#( #impl_calls )*
				_ => None,
			}
		}
	))
}

/// Generate the interface functions that are used to call into the runtime in wasm.
fn generate_wasm_interface(impls: &[ItemImpl]) -> Result<TokenStream> {
	let input = Ident::new("input", Span::call_site());
	let c = generate_crate_access(HIDDEN_INCLUDES_ID);

	let impl_calls =
		generate_impl_calls(impls, &input)?
			.into_iter()
			.map(|(trait_, fn_name, impl_, attrs)| {
				let fn_name =
					Ident::new(&prefix_function_with_trait(&trait_, &fn_name), Span::call_site());

				quote!(
					#( #attrs )*
					#[cfg(not(feature = "std"))]
					#[no_mangle]
					pub unsafe fn #fn_name(input_data: *mut u8, input_len: usize) -> u64 {
						let mut #input = if input_len == 0 {
							&[0u8; 0]
						} else {
							unsafe {
								#c::slice::from_raw_parts(input_data, input_len)
							}
						};

						#c::init_runtime_logger();

						let output = (move || { #impl_ })();
						#c::to_substrate_wasm_fn_return_value(&output)
					}
				)
			});

	Ok(quote!( #( #impl_calls )* ))
}

fn generate_runtime_api_base_structures() -> Result<TokenStream> {
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	Ok(quote!(
		pub struct RuntimeApi {}
		/// Implements all runtime apis for the client side.
		#[cfg(any(feature = "std", test))]
		pub struct RuntimeApiImpl<Block: #crate_::BlockT, C: #crate_::CallApiAt<Block> + 'static> {
			call: &'static C,
			commit_on_success: std::cell::RefCell<bool>,
			changes: std::cell::RefCell<#crate_::OverlayedChanges>,
			storage_transaction_cache: std::cell::RefCell<
				#crate_::StorageTransactionCache<Block, C::StateBackend>
			>,
			recorder: std::option::Option<#crate_::ProofRecorder<Block>>,
		}

		// `RuntimeApi` itself is not threadsafe. However, an instance is only available in a
		// `ApiRef` object and `ApiRef` also has an associated lifetime. This lifetimes makes it
		// impossible to move `RuntimeApi` into another thread.
		#[cfg(any(feature = "std", test))]
		unsafe impl<Block: #crate_::BlockT, C: #crate_::CallApiAt<Block>> Send
			for RuntimeApiImpl<Block, C>
		{}

		#[cfg(any(feature = "std", test))]
		unsafe impl<Block: #crate_::BlockT, C: #crate_::CallApiAt<Block>> Sync
			for RuntimeApiImpl<Block, C>
		{}

		#[cfg(any(feature = "std", test))]
		impl<Block: #crate_::BlockT, C: #crate_::CallApiAt<Block>> #crate_::ApiExt<Block> for
			RuntimeApiImpl<Block, C>
		{
			type StateBackend = C::StateBackend;

			fn execute_in_transaction<F: FnOnce(&Self) -> #crate_::TransactionOutcome<R>, R>(
				&self,
				call: F,
			) -> R where Self: Sized {
				#crate_::OverlayedChanges::start_transaction(&mut std::cell::RefCell::borrow_mut(&self.changes));
				*std::cell::RefCell::borrow_mut(&self.commit_on_success) = false;
				let res = call(self);
				*std::cell::RefCell::borrow_mut(&self.commit_on_success) = true;

				self.commit_or_rollback(std::matches!(res, #crate_::TransactionOutcome::Commit(_)));

				res.into_inner()
			}

			fn has_api<A: #crate_::RuntimeApiInfo + ?Sized>(
				&self,
				at: &#crate_::BlockId<Block>,
			) -> std::result::Result<bool, #crate_::ApiError> where Self: Sized {
				#crate_::CallApiAt::<Block>::runtime_version_at(self.call, at)
					.map(|v| #crate_::RuntimeVersion::has_api_with(&v, &A::ID, |v| v == A::VERSION))
			}

			fn has_api_with<A: #crate_::RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
				&self,
				at: &#crate_::BlockId<Block>,
				pred: P,
			) -> std::result::Result<bool, #crate_::ApiError> where Self: Sized {
				#crate_::CallApiAt::<Block>::runtime_version_at(self.call, at)
					.map(|v| #crate_::RuntimeVersion::has_api_with(&v, &A::ID, pred))
			}

			fn api_version<A: #crate_::RuntimeApiInfo + ?Sized>(
				&self,
				at: &#crate_::BlockId<Block>,
			) -> std::result::Result<Option<u32>, #crate_::ApiError> where Self: Sized {
				#crate_::CallApiAt::<Block>::runtime_version_at(self.call, at)
					.map(|v| #crate_::RuntimeVersion::api_version(&v, &A::ID))
			}

			fn record_proof(&mut self) {
				self.recorder = std::option::Option::Some(std::default::Default::default());
			}

			fn proof_recorder(&self) -> std::option::Option<#crate_::ProofRecorder<Block>> {
				std::clone::Clone::clone(&self.recorder)
			}

			fn extract_proof(
				&mut self,
			) -> std::option::Option<#crate_::StorageProof> {
				let recorder = std::option::Option::take(&mut self.recorder);
				std::option::Option::map(recorder, |recorder| {
					#crate_::ProofRecorder::<Block>::drain_storage_proof(recorder)
				})
			}

			fn into_storage_changes(
				&self,
				backend: &Self::StateBackend,
				parent_hash: Block::Hash,
			) -> core::result::Result<
				#crate_::StorageChanges<C::StateBackend, Block>,
				String
			> where Self: Sized {
				let at = #crate_::BlockId::Hash(std::clone::Clone::clone(&parent_hash));
				let state_version = #crate_::CallApiAt::<Block>::runtime_version_at(self.call, &at)
					.map(|v| #crate_::RuntimeVersion::state_version(&v))
					.map_err(|e| format!("Failed to get state version: {}", e))?;

				#crate_::OverlayedChanges::into_storage_changes(
					std::cell::RefCell::take(&self.changes),
					backend,
					core::cell::RefCell::take(&self.storage_transaction_cache),
					state_version,
				)
			}
		}

		#[cfg(any(feature = "std", test))]
		impl<Block: #crate_::BlockT, C> #crate_::ConstructRuntimeApi<Block, C>
			for RuntimeApi
				where
					C: #crate_::CallApiAt<Block> + 'static,
		{
			type RuntimeApi = RuntimeApiImpl<Block, C>;

			fn construct_runtime_api<'a>(
				call: &'a C,
			) -> #crate_::ApiRef<'a, Self::RuntimeApi> {
				RuntimeApiImpl {
					call: unsafe { std::mem::transmute(call) },
					commit_on_success: true.into(),
					changes: std::default::Default::default(),
					recorder: std::default::Default::default(),
					storage_transaction_cache: std::default::Default::default(),
				}.into()
			}
		}

		#[cfg(any(feature = "std", test))]
		impl<Block: #crate_::BlockT, C: #crate_::CallApiAt<Block>> RuntimeApiImpl<Block, C> {
			fn commit_or_rollback(&self, commit: bool) {
				let proof = "\
					We only close a transaction when we opened one ourself.
					Other parts of the runtime that make use of transactions (state-machine)
					also balance their transactions. The runtime cannot close client initiated
					transactions; qed";
				if *std::cell::RefCell::borrow(&self.commit_on_success) {
					let res = if commit {
						#crate_::OverlayedChanges::commit_transaction(
							&mut std::cell::RefCell::borrow_mut(&self.changes)
						)
					} else {
						#crate_::OverlayedChanges::rollback_transaction(
							&mut std::cell::RefCell::borrow_mut(&self.changes)
						)
					};

					std::result::Result::expect(res, proof);
				}
			}
		}
	))
}

/// Extend the given trait path with module that contains the declaration of the trait for the
/// runtime.
fn extend_with_runtime_decl_path(mut trait_: Path) -> Path {
	let runtime = {
		let trait_name = &trait_
			.segments
			.last()
			.as_ref()
			.expect("Trait path should always contain at least one item; qed")
			.ident;

		generate_runtime_mod_name_for_trait(trait_name)
	};

	let pos = trait_.segments.len() - 1;
	trait_.segments.insert(pos, runtime.into());
	trait_
}

fn extend_with_api_version(mut trait_: Path, version: Option<u64>) -> Path {
	let version = if let Some(v) = version {
		v
	} else {
		// nothing to do
		return trait_
	};

	let trait_name = &mut trait_
		.segments
		.last_mut()
		.expect("Trait path should always contain at least one item; qed")
		.ident;
	*trait_name = versioned_trait_name(trait_name, version);

	trait_
}

/// Generates the implementations of the apis for the runtime.
fn generate_api_impl_for_runtime(impls: &[ItemImpl]) -> Result<TokenStream> {
	let mut impls_prepared = Vec::new();

	// We put `runtime` before each trait to get the trait that is intended for the runtime and
	// we put the `RuntimeBlock` as first argument for the trait generics.
	for impl_ in impls.iter() {
		let trait_api_ver = extract_api_version(&impl_.attrs, impl_.span())?;

		let mut impl_ = impl_.clone();
		let trait_ = extract_impl_trait(&impl_, RequireQualifiedTraitPath::Yes)?.clone();
		let trait_ = extend_with_runtime_decl_path(trait_);
		let trait_ = extend_with_api_version(trait_, trait_api_ver);

		impl_.trait_.as_mut().unwrap().1 = trait_;
		impl_.attrs = filter_cfg_attrs(&impl_.attrs);
		impls_prepared.push(impl_);
	}

	Ok(quote!( #( #impls_prepared )* ))
}

/// Auxiliary data structure that is used to convert `impl Api for Runtime` to
/// `impl Api for RuntimeApi`.
/// This requires us to replace the runtime `Block` with the node `Block`,
/// `impl Api for Runtime` with `impl Api for RuntimeApi` and replace the method implementations
/// with code that calls into the runtime.
struct ApiRuntimeImplToApiRuntimeApiImpl<'a> {
	runtime_block: &'a TypePath,
}

impl<'a> ApiRuntimeImplToApiRuntimeApiImpl<'a> {
	/// Process the given item implementation.
	fn process(mut self, input: ItemImpl) -> ItemImpl {
		let mut input = self.fold_item_impl(input);

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

		// Delete all functions, because all of them are default implemented by
		// `decl_runtime_apis!`. We only need to implement the `__runtime_api_internal_call_api_at`
		// function.
		input.items.clear();
		input.items.push(parse_quote! {
			fn __runtime_api_internal_call_api_at(
				&self,
				at: &#crate_::BlockId<__SR_API_BLOCK__>,
				context: #crate_::ExecutionContext,
				params: std::vec::Vec<u8>,
				fn_name: &dyn Fn(#crate_::RuntimeVersion) -> &'static str,
			) -> std::result::Result<std::vec::Vec<u8>, #crate_::ApiError> {
				if *std::cell::RefCell::borrow(&self.commit_on_success) {
					#crate_::OverlayedChanges::start_transaction(
						&mut std::cell::RefCell::borrow_mut(&self.changes)
					);
				}

				let res = (|| {
				let version = #crate_::CallApiAt::<__SR_API_BLOCK__>::runtime_version_at(self.call, at)?;

				let params = #crate_::CallApiAtParams::<_, fn() -> _, _> {
					at,
					function: (*fn_name)(version),
					native_call: None,
					arguments: params,
					overlayed_changes: &self.changes,
					storage_transaction_cache: &self.storage_transaction_cache,
					context,
					recorder: &self.recorder,
				};

				#crate_::CallApiAt::<__SR_API_BLOCK__>::call_api_at::<#crate_::NeverNativeValue, _>(
					self.call,
					params,
				)
			})();

				self.commit_or_rollback(std::result::Result::is_ok(&res));

				res.map(#crate_::NativeOrEncoded::into_encoded)
			}
		});

		input
	}
}

impl<'a> Fold for ApiRuntimeImplToApiRuntimeApiImpl<'a> {
	fn fold_type_path(&mut self, input: TypePath) -> TypePath {
		let new_ty_path =
			if input == *self.runtime_block { parse_quote!(__SR_API_BLOCK__) } else { input };

		fold::fold_type_path(self, new_ty_path)
	}

	fn fold_item_impl(&mut self, mut input: ItemImpl) -> ItemImpl {
		// All this `UnwindSafe` magic below here is required for this rust bug:
		// https://github.com/rust-lang/rust/issues/24159
		// Before we directly had the final block type and rust could determine that it is unwind
		// safe, but now we just have a generic parameter `Block`.

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

		// Implement the trait for the `RuntimeApiImpl`
		input.self_ty =
			Box::new(parse_quote!( RuntimeApiImpl<__SR_API_BLOCK__, RuntimeApiImplCall> ));

		input.generics.params.push(parse_quote!(
			__SR_API_BLOCK__: #crate_::BlockT + std::panic::UnwindSafe +
				std::panic::RefUnwindSafe
		));
		input.generics.params.push(
			parse_quote!( RuntimeApiImplCall: #crate_::CallApiAt<__SR_API_BLOCK__> + 'static ),
		);

		let where_clause = input.generics.make_where_clause();

		where_clause.predicates.push(parse_quote! {
			RuntimeApiImplCall::StateBackend:
				#crate_::StateBackend<#crate_::HashFor<__SR_API_BLOCK__>>
		});

		// Require that all types used in the function signatures are unwind safe.
		extract_all_signature_types(&input.items).iter().for_each(|i| {
			where_clause.predicates.push(parse_quote! {
				#i: std::panic::UnwindSafe + std::panic::RefUnwindSafe
			});
		});

		where_clause.predicates.push(parse_quote! {
			__SR_API_BLOCK__::Header: std::panic::UnwindSafe + std::panic::RefUnwindSafe
		});

		input.attrs = filter_cfg_attrs(&input.attrs);

		// The implementation for the `RuntimeApiImpl` is only required when compiling with
		// the feature `std` or `test`.
		input.attrs.push(parse_quote!( #[cfg(any(feature = "std", test))] ));

		fold::fold_item_impl(self, input)
	}
}

/// Generate the implementations of the runtime apis for the `RuntimeApi` type.
fn generate_api_impl_for_runtime_api(impls: &[ItemImpl]) -> Result<TokenStream> {
	let mut result = Vec::with_capacity(impls.len());

	for impl_ in impls {
		let impl_trait_path = extract_impl_trait(impl_, RequireQualifiedTraitPath::Yes)?;
		let runtime_block = extract_block_type_from_trait_path(impl_trait_path)?;
		let mut runtime_mod_path = extend_with_runtime_decl_path(impl_trait_path.clone());
		// remove the trait to get just the module path
		runtime_mod_path.segments.pop();

		let processed_impl =
			ApiRuntimeImplToApiRuntimeApiImpl { runtime_block }.process(impl_.clone());

		result.push(processed_impl);
	}
	Ok(quote!( #( #result )* ))
}

fn populate_runtime_api_versions(
	result: &mut Vec<TokenStream>,
	sections: &mut Vec<TokenStream>,
	attrs: Vec<Attribute>,
	id: Path,
	version: TokenStream,
	crate_access: &TokenStream,
) {
	result.push(quote!(
			#( #attrs )*
			(#id, #version)
	));

	sections.push(quote!(
		#( #attrs )*
		const _: () = {
			// All sections with the same name are going to be merged by concatenation.
			#[cfg(not(feature = "std"))]
			#[link_section = "runtime_apis"]
			static SECTION_CONTENTS: [u8; 12] = #crate_access::serialize_runtime_api_info(#id, #version);
		};
	));
}

/// Generates `RUNTIME_API_VERSIONS` that holds all version information about the implemented
/// runtime apis.
fn generate_runtime_api_versions(impls: &[ItemImpl]) -> Result<TokenStream> {
	let mut result = Vec::<TokenStream>::with_capacity(impls.len());
	let mut sections = Vec::<TokenStream>::with_capacity(impls.len());
	let mut processed_traits = HashSet::new();

	let c = generate_crate_access(HIDDEN_INCLUDES_ID);

	for impl_ in impls {
		let api_ver = extract_api_version(&impl_.attrs, impl_.span())?.map(|a| a as u32);

		let mut path = extend_with_runtime_decl_path(
			extract_impl_trait(impl_, RequireQualifiedTraitPath::Yes)?.clone(),
		);
		// Remove the trait
		let trait_ = path
			.segments
			.pop()
			.expect("extract_impl_trait already checks that this is valid; qed")
			.into_value()
			.ident;

		let span = trait_.span();
		if !processed_traits.insert(trait_) {
			return Err(Error::new(
				span,
				"Two traits with the same name detected! \
					The trait name is used to generate its ID. \
					Please rename one trait at the declaration!",
			))
		}

		let id: Path = parse_quote!( #path ID );
		let version = quote!( #path VERSION );
		let attrs = filter_cfg_attrs(&impl_.attrs);

		let api_ver = api_ver.map(|a| quote!( #a )).unwrap_or_else(|| version);
		populate_runtime_api_versions(&mut result, &mut sections, attrs, id, api_ver, &c)
	}

	Ok(quote!(
		const RUNTIME_API_VERSIONS: #c::ApisVec = #c::create_apis_vec!([ #( #result ),* ]);

		#( #sections )*
	))
}

/// The implementation of the `impl_runtime_apis!` macro.
pub fn impl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all impl blocks
	let RuntimeApiImpls { impls: api_impls } = parse_macro_input!(input as RuntimeApiImpls);

	impl_runtime_apis_impl_inner(&api_impls)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn impl_runtime_apis_impl_inner(api_impls: &[ItemImpl]) -> Result<TokenStream> {
	let dispatch_impl = generate_dispatch_function(api_impls)?;
	let api_impls_for_runtime = generate_api_impl_for_runtime(api_impls)?;
	let base_runtime_api = generate_runtime_api_base_structures()?;
	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let runtime_api_versions = generate_runtime_api_versions(api_impls)?;
	let wasm_interface = generate_wasm_interface(api_impls)?;
	let api_impls_for_runtime_api = generate_api_impl_for_runtime_api(api_impls)?;

	Ok(quote!(
		#hidden_includes

		#base_runtime_api

		#api_impls_for_runtime

		#api_impls_for_runtime_api

		#runtime_api_versions

		pub mod api {
			use super::*;

			#dispatch_impl

			#wasm_interface
		}
	))
}

// Filters all attributes except the cfg ones.
fn filter_cfg_attrs(attrs: &[Attribute]) -> Vec<Attribute> {
	attrs.iter().filter(|a| a.path.is_ident("cfg")).cloned().collect()
}

// Extracts the value of `API_VERSION_ATTRIBUTE` and handles errors.
// Returns:
// - Err if the version is malformed
// - Some(u64) if the version is set
// - None if the version is not set (this is valid).
fn extract_api_version(attrs: &Vec<Attribute>, span: Span) -> Result<Option<u64>> {
	// First fetch all `API_VERSION_ATTRIBUTE` values (should be only one)
	let api_ver = attrs
		.iter()
		.filter(|a| a.path.is_ident(API_VERSION_ATTRIBUTE))
		.collect::<Vec<_>>();

	if api_ver.len() > 1 {
		return Err(Error::new(
			span,
			format!(
				"Found multiple #[{}] attributes for an API implementation. \
				Each runtime API can have only one version.",
				API_VERSION_ATTRIBUTE
			),
		))
	}

	// Parse the runtime version if there exists one.
	api_ver.first().map(|v| parse_runtime_api_version(v)).transpose()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn filter_non_cfg_attributes() {
		let cfg_std: Attribute = parse_quote!(#[cfg(feature = "std")]);
		let cfg_benchmarks: Attribute = parse_quote!(#[cfg(feature = "runtime-benchmarks")]);

		let attrs = vec![
			cfg_std.clone(),
			parse_quote!(#[derive(Debug)]),
			parse_quote!(#[test]),
			cfg_benchmarks.clone(),
			parse_quote!(#[allow(non_camel_case_types)]),
		];

		let filtered = filter_cfg_attrs(&attrs);
		assert_eq!(filtered.len(), 2);
		assert_eq!(cfg_std, filtered[0]);
		assert_eq!(cfg_benchmarks, filtered[1]);
	}
}
