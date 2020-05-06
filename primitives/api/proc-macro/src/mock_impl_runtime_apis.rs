// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::utils::{
	generate_crate_access, generate_hidden_includes,
	generate_method_runtime_api_impl_name, extract_parameter_names_types_and_borrows,
	return_type_extract_type, extract_block_type_from_trait_path, extract_impl_trait,
	AllowSelfRefInParameters, RequireQualifiedTraitPath,
};

use proc_macro2::{Span, TokenStream};

use quote::quote;

use syn::{
	spanned::Spanned, parse_macro_input, Ident, Type, ItemImpl, ImplItem, TypePath, parse_quote,
	parse::{Parse, ParseStream, Result, Error}, fold::{self, Fold},
};

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "MOCK_IMPL_RUNTIME_APIS";

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

/// Implement the `ApiExt` trait, `ApiErrorExt` trait and the `Core` runtime api.
fn implement_common_api_traits(
	error_type: Option<Type>,
	block_type: TypePath,
	self_ty: Type,
) -> Result<TokenStream> {
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	let error_type = error_type.map(|e| quote!(#e)).unwrap_or_else(|| quote!(String));

	Ok(quote!(
		impl #crate_::ApiErrorExt for #self_ty {
			type Error = #error_type;
		}

		impl #crate_::ApiExt<#block_type> for #self_ty {
			type StateBackend = #crate_::InMemoryBackend<#crate_::HashFor<#block_type>>;

			fn map_api_result<F: FnOnce(&Self) -> std::result::Result<R, E>, R, E>(
				&self,
				map_call: F,
			) -> std::result::Result<R, E> where Self: Sized {
				map_call(self)
			}

			fn has_api<A: #crate_::RuntimeApiInfo + ?Sized>(
				&self,
				_: &#crate_::BlockId<#block_type>,
			) -> std::result::Result<bool, #error_type> where Self: Sized {
				Ok(true)
			}

			fn has_api_with<A: #crate_::RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
				&self,
				at: &#crate_::BlockId<#block_type>,
				pred: P,
			) -> std::result::Result<bool, #error_type> where Self: Sized {
				Ok(pred(A::VERSION))
			}

			fn record_proof(&mut self) {
				unimplemented!("`record_proof` not implemented for runtime api mocks")
			}

			fn extract_proof(&mut self) -> Option<#crate_::StorageProof> {
				unimplemented!("`extract_proof` not implemented for runtime api mocks")
			}

			fn into_storage_changes(
				&self,
				_: &Self::StateBackend,
				_: Option<&#crate_::ChangesTrieState<
					#crate_::HashFor<#block_type>,
					#crate_::NumberFor<#block_type>,
				>>,
				_: <#block_type as #crate_::BlockT>::Hash,
			) -> std::result::Result<
				#crate_::StorageChanges<Self::StateBackend, #block_type>,
				String
			> where Self: Sized {
				unimplemented!("`into_storage_changes` not implemented for runtime api mocks")
			}
		}

		impl #crate_::Core<#block_type> for #self_ty {
			fn Core_version_runtime_api_impl(
				&self,
				_: &#crate_::BlockId<#block_type>,
				_: #crate_::ExecutionContext,
				_: Option<()>,
				_: Vec<u8>,
			) -> std::result::Result<#crate_::NativeOrEncoded<#crate_::RuntimeVersion>, #error_type> {
				unimplemented!("Not required for testing!")
			}

			fn Core_execute_block_runtime_api_impl(
				&self,
				_: &#crate_::BlockId<#block_type>,
				_: #crate_::ExecutionContext,
				_: Option<#block_type>,
				_: Vec<u8>,
			) -> std::result::Result<#crate_::NativeOrEncoded<()>, #error_type> {
				unimplemented!("Not required for testing!")
			}

			fn Core_initialize_block_runtime_api_impl(
				&self,
				_: &#crate_::BlockId<#block_type>,
				_: #crate_::ExecutionContext,
				_: Option<&<#block_type as #crate_::BlockT>::Header>,
				_: Vec<u8>,
			) -> std::result::Result<#crate_::NativeOrEncoded<()>, #error_type> {
				unimplemented!("Not required for testing!")
			}
		}
	))
}

/// Auxialiry structure to fold a runtime api trait implementation into the expected format.
///
/// This renames the methods, changes the method parameters and extracts the error type.
struct FoldRuntimeApiImpl<'a> {
	/// The block type that is being used.
	block_type: &'a TypePath,
	/// The identifier of the trait being implemented.
	impl_trait: &'a Ident,
	/// Stores the error type that is being found in the trait implementation as associated type
	/// with the name `Error`.
	error_type: &'a mut Option<Type>,
}

impl<'a> Fold for FoldRuntimeApiImpl<'a> {
	fn fold_impl_item_method(&mut self, mut input: syn::ImplItemMethod) -> syn::ImplItemMethod {
		let block = {
			let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

			let (param_names, param_types, error) = match extract_parameter_names_types_and_borrows(
				&input.sig,
				AllowSelfRefInParameters::YesButIgnore,
			) {
				Ok(res) => (
					res.iter().map(|v| v.0.clone()).collect::<Vec<_>>(),
					res.iter().map(|v| {
						let ty = &v.1;
						let borrow = &v.2;
						quote!( #borrow #ty )
					}).collect::<Vec<_>>(),
					None
				),
				Err(e) => (Vec::new(), Vec::new(), Some(e.to_compile_error())),
			};

			let block_type = &self.block_type;

			// Rewrite the input parameters.
			input.sig.inputs = parse_quote! {
				&self,
				_: &#crate_::BlockId<#block_type>,
				_: #crate_::ExecutionContext,
				params: Option<( #( #param_types ),* )>,
				_: Vec<u8>,
			};

			input.sig.ident = generate_method_runtime_api_impl_name(
				&self.impl_trait,
				&input.sig.ident,
			);
			let ret_type = return_type_extract_type(&input.sig.output);

			// Generate the correct return type.
			input.sig.output = parse_quote!(
				-> std::result::Result<#crate_::NativeOrEncoded<#ret_type>, Self::Error>
			);

			let orig_block = input.block.clone();

			// Generate the new method implementation that calls into the runtime.
			parse_quote!(
				{
					// Get the error to the user (if we have one).
					#error

					let (#( #param_names ),*) = params
						.expect("Mocked runtime apis don't support calling deprecated api versions");

					let __fn_implementation__ = move || #orig_block;

					Ok(#crate_::NativeOrEncoded::Native(__fn_implementation__()))
				}
			)
		};

		let mut input = fold::fold_impl_item_method(self, input);
		// We need to set the block, after we modified the rest of the ast, otherwise we would
		// modify our generated block as well.
		input.block = block;
		input
	}

	fn fold_impl_item(&mut self, input: ImplItem) -> ImplItem {
		match input {
			ImplItem::Type(ty) => {
				if ty.ident == "Error" {
					if let Some(error_type) = self.error_type {
						if *error_type != ty.ty {
							let error = Error::new(
								ty.span(),
								"Error type can not change between runtime apis",
							);
							ImplItem::Verbatim(error.to_compile_error())
						} else {
							ImplItem::Verbatim(Default::default())
						}
					} else {
						*self.error_type = Some(ty.ty);
						ImplItem::Verbatim(Default::default())
					}
				} else {
					let error = Error::new(
						ty.span(),
						"Only associated type with name `Error` is allowed",
					);
					ImplItem::Verbatim(error.to_compile_error())
				}
			},
			o => fold::fold_impl_item(self, o),
		}
	}
}

/// Result of [`generate_runtime_api_impls`].
struct GeneratedRuntimeApiImpls {
	/// All the runtime api implementations.
	impls: TokenStream,
	/// The error type that should be used by the runtime apis.
	error_type: Option<Type>,
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
	let mut error_type = None;
	let mut global_block_type: Option<TypePath> = None;
	let mut self_ty: Option<Box<Type>> = None;

	for impl_ in impls {
		let impl_trait_path = extract_impl_trait(&impl_, RequireQualifiedTraitPath::No)?;
		let impl_trait = &impl_trait_path
			.segments
			.last()
			.ok_or_else(|| Error::new(impl_trait_path.span(), "Empty trait path not possible!"))?
			.clone();
		let block_type = extract_block_type_from_trait_path(impl_trait_path)?;

		self_ty = match self_ty.take() {
			Some(self_ty) => {
				if self_ty == impl_.self_ty {
					Some(self_ty)
				} else {
					let mut error =Error::new(
						impl_.self_ty.span(),
						"Self type should not change between runtime apis",
					);

					error.combine(Error::new(
						self_ty.span(),
						"First self type found here",
					));

					return Err(error)
				}
			},
			None => Some(impl_.self_ty.clone()),
		};

		global_block_type = match global_block_type.take() {
			Some(global_block_type) => {
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
				}
			},
			None => Some(block_type.clone()),
		};

		let mut visitor = FoldRuntimeApiImpl {
			block_type,
			impl_trait: &impl_trait.ident,
			error_type: &mut error_type,
		};

		result.push(visitor.fold_item_impl(impl_.clone()));
	}

	Ok(GeneratedRuntimeApiImpls {
		impls: quote!( #( #result )* ),
		error_type,
		block_type: global_block_type.expect("There is a least one runtime api; qed"),
		self_ty: *self_ty.expect("There is at least one runtime api; qed"),
	})
}

/// The implementation of the `mock_impl_runtime_apis!` macro.
pub fn mock_impl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all impl blocks
	let RuntimeApiImpls { impls: api_impls } = parse_macro_input!(input as RuntimeApiImpls);

	mock_impl_runtime_apis_impl_inner(&api_impls).unwrap_or_else(|e| e.to_compile_error()).into()
}

fn mock_impl_runtime_apis_impl_inner(api_impls: &[ItemImpl]) -> Result<TokenStream> {
	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let GeneratedRuntimeApiImpls { impls, error_type, block_type, self_ty } =
		generate_runtime_api_impls(api_impls)?;
	let api_traits = implement_common_api_traits(error_type, block_type, self_ty)?;

	Ok(quote!(
		#hidden_includes

		#impls

		#api_traits
	))
}
