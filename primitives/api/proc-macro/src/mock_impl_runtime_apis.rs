// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
	extract_block_type_from_trait_path, extract_impl_trait,
	extract_parameter_names_types_and_borrows, generate_crate_access, generate_hidden_includes,
	return_type_extract_type, AllowSelfRefInParameters, RequireQualifiedTraitPath,
};

use proc_macro2::{Span, TokenStream};

use quote::{quote, quote_spanned};

use syn::{
	fold::{self, Fold},
	parse::{Error, Parse, ParseStream, Result},
	parse_macro_input, parse_quote,
	spanned::Spanned,
	Attribute, ItemImpl, Pat, Type, TypePath,
};

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "MOCK_IMPL_RUNTIME_APIS";

/// The `advanced` attribute.
///
/// If this attribute is given to a function, the function gets access to the `Hash` as first
/// parameter and needs to return a `Result` with the appropriate error type.
const ADVANCED_ATTRIBUTE: &str = "advanced";

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

/// Implement the `ApiExt` trait and the `Core` runtime api.
fn implement_common_api_traits(block_type: TypePath, self_ty: Type) -> Result<TokenStream> {
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	Ok(quote!(
		impl #crate_::ApiExt<#block_type> for #self_ty {
			type StateBackend = #crate_::InMemoryBackend<#crate_::HashFor<#block_type>>;

			fn execute_in_transaction<F: FnOnce(&Self) -> #crate_::TransactionOutcome<R>, R>(
				&self,
				call: F,
			) -> R where Self: Sized {
				call(self).into_inner()
			}

			fn has_api<A: #crate_::RuntimeApiInfo + ?Sized>(
				&self,
				_: <Block as #crate_::BlockT>::Hash,
			) -> std::result::Result<bool, #crate_::ApiError> where Self: Sized {
				Ok(true)
			}

			fn has_api_with<A: #crate_::RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
				&self,
				_: <Block as #crate_::BlockT>::Hash,
				pred: P,
			) -> std::result::Result<bool, #crate_::ApiError> where Self: Sized {
				Ok(pred(A::VERSION))
			}

			fn api_version<A: #crate_::RuntimeApiInfo + ?Sized>(
				&self,
				_: <Block as #crate_::BlockT>::Hash,
			) -> std::result::Result<Option<u32>, #crate_::ApiError> where Self: Sized {
				Ok(Some(A::VERSION))
			}

			fn record_proof(&mut self) {
				unimplemented!("`record_proof` not implemented for runtime api mocks")
			}

			fn extract_proof(
				&mut self,
			) -> Option<#crate_::StorageProof> {
				unimplemented!("`extract_proof` not implemented for runtime api mocks")
			}

			fn proof_recorder(&self) -> Option<#crate_::ProofRecorder<#block_type>> {
				unimplemented!("`proof_recorder` not implemented for runtime api mocks")
			}

			fn into_storage_changes(
				&self,
				_: &Self::StateBackend,
				_: <#block_type as #crate_::BlockT>::Hash,
			) -> std::result::Result<
				#crate_::StorageChanges<Self::StateBackend, #block_type>,
				String
			> where Self: Sized {
				unimplemented!("`into_storage_changes` not implemented for runtime api mocks")
			}
		}

		impl #crate_::Core<#block_type> for #self_ty {
			fn __runtime_api_internal_call_api_at(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #crate_::ExecutionContext,
				_: std::vec::Vec<u8>,
				_: &dyn Fn(#crate_::RuntimeVersion) -> &'static str,
			) -> std::result::Result<std::vec::Vec<u8>, #crate_::ApiError> {
				unimplemented!("`__runtime_api_internal_call_api_at` not implemented for runtime api mocks")
			}

			fn version(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
			) -> std::result::Result<#crate_::RuntimeVersion, #crate_::ApiError> {
				unimplemented!("`Core::version` not implemented for runtime api mocks")
			}

			fn version_with_context(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #crate_::ExecutionContext,
			) -> std::result::Result<#crate_::RuntimeVersion, #crate_::ApiError> {
				unimplemented!("`Core::version` not implemented for runtime api mocks")
			}

			fn execute_block(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #block_type,
			) -> std::result::Result<(), #crate_::ApiError> {
				unimplemented!("`Core::execute_block` not implemented for runtime api mocks")
			}

			fn execute_block_with_context(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #crate_::ExecutionContext,
				_: #block_type,
			) -> std::result::Result<(), #crate_::ApiError> {
				unimplemented!("`Core::execute_block` not implemented for runtime api mocks")
			}

			fn initialize_block(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: &<#block_type as #crate_::BlockT>::Header,
			) -> std::result::Result<(), #crate_::ApiError> {
				unimplemented!("`Core::initialize_block` not implemented for runtime api mocks")
			}

			fn initialize_block_with_context(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #crate_::ExecutionContext,
				_: &<#block_type as #crate_::BlockT>::Header,
			) -> std::result::Result<(), #crate_::ApiError> {
				unimplemented!("`Core::initialize_block` not implemented for runtime api mocks")
			}
		}
	))
}

/// Returns if the advanced attribute is present in the given `attributes`.
///
/// If the attribute was found, it will be automatically removed from the vec.
fn has_advanced_attribute(attributes: &mut Vec<Attribute>) -> bool {
	let mut found = false;
	attributes.retain(|attr| {
		if attr.path.is_ident(ADVANCED_ATTRIBUTE) {
			found = true;
			false
		} else {
			true
		}
	});

	found
}

/// Get the name and type of the `at` parameter that is passed to a runtime api function.
///
/// If `is_advanced` is `false`, the name is `_`.
fn get_at_param_name(
	is_advanced: bool,
	param_names: &mut Vec<Pat>,
	param_types_and_borrows: &mut Vec<(TokenStream, bool)>,
	function_span: Span,
	default_hash_type: &TokenStream,
) -> Result<(TokenStream, TokenStream)> {
	if is_advanced {
		if param_names.is_empty() {
			return Err(Error::new(
				function_span,
				format!(
					"If using the `{}` attribute, it is required that the function \
					 takes at least one argument, the `Hash`.",
					ADVANCED_ATTRIBUTE,
				),
			))
		}

		// `param_names` and `param_types` have the same length, so if `param_names` is not empty
		// `param_types` can not be empty as well.
		let ptype_and_borrows = param_types_and_borrows.remove(0);
		let span = ptype_and_borrows.1.span();
		if ptype_and_borrows.1 {
			return Err(Error::new(span, "`Hash` needs to be taken by value and not by reference!"))
		}

		let name = param_names.remove(0);
		Ok((quote!( #name ), ptype_and_borrows.0))
	} else {
		Ok((quote!(_), default_hash_type.clone()))
	}
}

/// Auxiliary structure to fold a runtime api trait implementation into the expected format.
///
/// This renames the methods, changes the method parameters and extracts the error type.
struct FoldRuntimeApiImpl<'a> {
	/// The block type that is being used.
	block_type: &'a TypePath,
}

impl<'a> FoldRuntimeApiImpl<'a> {
	/// Process the given [`syn::ItemImpl`].
	fn process(mut self, impl_item: syn::ItemImpl) -> syn::ItemImpl {
		let mut impl_item = self.fold_item_impl(impl_item);

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

		// We also need to overwrite all the `_with_context` methods. To do this,
		// we clone all methods and add them again with the new name plus one more argument.
		impl_item.items.extend(impl_item.items.clone().into_iter().filter_map(|i| {
			if let syn::ImplItem::Method(mut m) = i {
				m.sig.ident = quote::format_ident!("{}_with_context", m.sig.ident);
				m.sig.inputs.insert(2, parse_quote!( _: #crate_::ExecutionContext ));

				Some(m.into())
			} else {
				None
			}
		}));

		let block_type = self.block_type;

		impl_item.items.push(parse_quote! {
			fn __runtime_api_internal_call_api_at(
				&self,
				_: <#block_type as #crate_::BlockT>::Hash,
				_: #crate_::ExecutionContext,
				_: std::vec::Vec<u8>,
				_: &dyn Fn(#crate_::RuntimeVersion) -> &'static str,
			) -> std::result::Result<std::vec::Vec<u8>, #crate_::ApiError> {
				unimplemented!(
					"`__runtime_api_internal_call_api_at` not implemented for runtime api mocks. \
					 Calling deprecated methods is not supported by mocked runtime api."
				)
			}
		});

		impl_item
	}
}

impl<'a> Fold for FoldRuntimeApiImpl<'a> {
	fn fold_impl_item_method(&mut self, mut input: syn::ImplItemMethod) -> syn::ImplItemMethod {
		let block = {
			let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
			let is_advanced = has_advanced_attribute(&mut input.attrs);
			let mut errors = Vec::new();

			let (mut param_names, mut param_types_and_borrows) =
				match extract_parameter_names_types_and_borrows(
					&input.sig,
					AllowSelfRefInParameters::YesButIgnore,
				) {
					Ok(res) => (
						res.iter().map(|v| v.0.clone()).collect::<Vec<_>>(),
						res.iter()
							.map(|v| {
								let ty = &v.1;
								let borrow = &v.2;
								(quote_spanned!(ty.span() => #borrow #ty ), v.2.is_some())
							})
							.collect::<Vec<_>>(),
					),
					Err(e) => {
						errors.push(e.to_compile_error());

						(Default::default(), Default::default())
					},
				};

			let block_type = &self.block_type;
			let hash_type = quote!( <#block_type as #crate_::BlockT>::Hash );

			let (at_param_name, hash_type) = match get_at_param_name(
				is_advanced,
				&mut param_names,
				&mut param_types_and_borrows,
				input.span(),
				&hash_type,
			) {
				Ok(res) => res,
				Err(e) => {
					errors.push(e.to_compile_error());
					(quote!(_), hash_type)
				},
			};

			let param_types = param_types_and_borrows.iter().map(|v| &v.0);
			// Rewrite the input parameters.
			input.sig.inputs = parse_quote! {
				&self,
				#at_param_name: #hash_type,
				#( #param_names: #param_types ),*
			};

			// When using advanced, the user needs to declare the correct return type on its own,
			// otherwise do it for the user.
			if !is_advanced {
				let ret_type = return_type_extract_type(&input.sig.output);

				// Generate the correct return type.
				input.sig.output = parse_quote!(
					-> std::result::Result<#ret_type, #crate_::ApiError>
				);
			}

			let orig_block = input.block.clone();

			let construct_return_value = if is_advanced {
				quote!( (move || #orig_block)() )
			} else {
				quote! {
					let __fn_implementation__ = move || #orig_block;

					Ok(__fn_implementation__())
				}
			};

			// Generate the new method implementation that calls into the runtime.
			parse_quote!(
				{
					// Get the error to the user (if we have one).
					#( #errors )*

					#construct_return_value
				}
			)
		};

		let mut input = fold::fold_impl_item_method(self, input);
		// We need to set the block, after we modified the rest of the ast, otherwise we would
		// modify our generated block as well.
		input.block = block;
		input
	}
}

/// Result of [`generate_runtime_api_impls`].
struct GeneratedRuntimeApiImpls {
	/// All the runtime api implementations.
	impls: TokenStream,
	/// The block type that is being used by the runtime apis.
	block_type: TypePath,
	/// The type the traits are implemented for.
	self_ty: Type,
}

/// Generate the runtime api implementations from the given trait implementations.
///
/// This folds the method names, changes the method parameters, method return type,
/// extracts the error type, self type and the block type.
fn generate_runtime_api_impls(impls: &[ItemImpl]) -> Result<GeneratedRuntimeApiImpls> {
	let mut result = Vec::with_capacity(impls.len());
	let mut global_block_type: Option<TypePath> = None;
	let mut self_ty: Option<Box<Type>> = None;

	for impl_ in impls {
		let impl_trait_path = extract_impl_trait(impl_, RequireQualifiedTraitPath::No)?;
		let block_type = extract_block_type_from_trait_path(impl_trait_path)?;

		self_ty = match self_ty.take() {
			Some(self_ty) =>
				if self_ty == impl_.self_ty {
					Some(self_ty)
				} else {
					let mut error = Error::new(
						impl_.self_ty.span(),
						"Self type should not change between runtime apis",
					);

					error.combine(Error::new(self_ty.span(), "First self type found here"));

					return Err(error)
				},
			None => Some(impl_.self_ty.clone()),
		};

		global_block_type = match global_block_type.take() {
			Some(global_block_type) =>
				if global_block_type == *block_type {
					Some(global_block_type)
				} else {
					let mut error = Error::new(
						block_type.span(),
						"Block type should be the same between all runtime apis.",
					);

					error.combine(Error::new(
						global_block_type.span(),
						"First block type found here",
					));

					return Err(error)
				},
			None => Some(block_type.clone()),
		};

		result.push(FoldRuntimeApiImpl { block_type }.process(impl_.clone()));
	}

	Ok(GeneratedRuntimeApiImpls {
		impls: quote!( #( #result )* ),
		block_type: global_block_type.expect("There is a least one runtime api; qed"),
		self_ty: *self_ty.expect("There is at least one runtime api; qed"),
	})
}

/// The implementation of the `mock_impl_runtime_apis!` macro.
pub fn mock_impl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all impl blocks
	let RuntimeApiImpls { impls: api_impls } = parse_macro_input!(input as RuntimeApiImpls);

	mock_impl_runtime_apis_impl_inner(&api_impls)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn mock_impl_runtime_apis_impl_inner(api_impls: &[ItemImpl]) -> Result<TokenStream> {
	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let GeneratedRuntimeApiImpls { impls, block_type, self_ty } =
		generate_runtime_api_impls(api_impls)?;
	let api_traits = implement_common_api_traits(block_type, self_ty)?;

	Ok(quote!(
		#hidden_includes

		#impls

		#api_traits
	))
}
