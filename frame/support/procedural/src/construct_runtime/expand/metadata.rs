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
// limitations under the License

use crate::construct_runtime::{parse::PalletPath, Pallet};
use proc_macro2::TokenStream;
use quote::quote;
use std::str::FromStr;
use syn::{Ident, TypePath};

pub fn expand_runtime_metadata(
	runtime: &Ident,
	pallet_declarations: &[Pallet],
	scrate: &TokenStream,
	extrinsic: &TypePath,
	system_path: &PalletPath,
) -> TokenStream {
	let pallets = pallet_declarations
		.iter()
		.filter_map(|pallet_declaration| {
			pallet_declaration.find_part("Pallet").map(|_| {
				let filtered_names: Vec<_> = pallet_declaration
					.pallet_parts()
					.iter()
					.filter(|part| part.name() != "Pallet")
					.map(|part| part.name())
					.collect();
				(pallet_declaration, filtered_names)
			})
		})
		.map(|(decl, filtered_names)| {
			let name = &decl.name;
			let index = &decl.index;
			let storage = expand_pallet_metadata_storage(&filtered_names, runtime, decl);
			let calls = expand_pallet_metadata_calls(&filtered_names, runtime, decl);
			let event = expand_pallet_metadata_events(&filtered_names, runtime, scrate, decl);
			let constants = expand_pallet_metadata_constants(runtime, decl);
			let errors = expand_pallet_metadata_errors(runtime, decl);
			let docs = expand_pallet_metadata_docs(runtime, decl);
			let attr = decl.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
				let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
					.expect("was successfully parsed before; qed");
				quote! {
					#acc
					#attr
				}
			});

			quote! {
				#attr
				#scrate::metadata_ir::PalletMetadataIR {
					name: stringify!(#name),
					index: #index,
					storage: #storage,
					calls: #calls,
					event: #event,
					constants: #constants,
					error: #errors,
					docs: #docs,
				}
			}
		})
		.collect::<Vec<_>>();

	quote! {
		impl #runtime {
			fn metadata_ir() -> #scrate::metadata_ir::MetadataIR {
				// Each runtime must expose the `runtime_metadata()` to fetch the runtime API metadata.
				// The function is implemented by calling `impl_runtime_apis!`.
				//
				// However, the `construct_runtime!` may be called without calling `impl_runtime_apis!`.
				// Rely on the `Deref` trait to differentiate between a runtime that implements
				// APIs (by macro impl_runtime_apis!) and a runtime that is simply created (by macro construct_runtime!).
				//
				// Both `InternalConstructRuntime` and `InternalImplRuntimeApis` expose a `runtime_metadata()` function.
				// `InternalConstructRuntime` is implemented by the `construct_runtime!` for Runtime references (`& Runtime`),
				// while `InternalImplRuntimeApis` is implemented by the `impl_runtime_apis!` for Runtime (`Runtime`).
				//
				// Therefore, the `Deref` trait will resolve the `runtime_metadata` from `impl_runtime_apis!`
				// when both macros are called; and will resolve an empty `runtime_metadata` when only the `construct_runtime!`
				// is called.
				//
				// `Deref` needs a reference for resolving the function call.
				let rt = #runtime;

				let ty = #scrate::scale_info::meta_type::<#extrinsic>();
				let address_ty = #scrate::scale_info::meta_type::<
						<<#extrinsic as #scrate::sp_runtime::traits::Extrinsic>::SignaturePayload as #scrate::sp_runtime::traits::SignaturePayload>::SignatureAddress
					>();
				let call_ty = #scrate::scale_info::meta_type::<
					<#extrinsic as #scrate::sp_runtime::traits::Extrinsic>::Call
					>();
				let signature_ty = #scrate::scale_info::meta_type::<
						<<#extrinsic as #scrate::sp_runtime::traits::Extrinsic>::SignaturePayload as #scrate::sp_runtime::traits::SignaturePayload>::Signature
					>();
				let extra_ty = #scrate::scale_info::meta_type::<
						<<#extrinsic as #scrate::sp_runtime::traits::Extrinsic>::SignaturePayload as #scrate::sp_runtime::traits::SignaturePayload>::SignatureExtra
					>();

				#scrate::metadata_ir::MetadataIR {
					pallets: #scrate::sp_std::vec![ #(#pallets),* ],
					extrinsic: #scrate::metadata_ir::ExtrinsicMetadataIR {
						ty,
						version: <#extrinsic as #scrate::sp_runtime::traits::ExtrinsicMetadata>::VERSION,
						address_ty,
						call_ty,
						signature_ty,
						extra_ty,
						signed_extensions: <
								<
									#extrinsic as #scrate::sp_runtime::traits::ExtrinsicMetadata
								>::SignedExtensions as #scrate::sp_runtime::traits::SignedExtension
							>::metadata()
								.into_iter()
								.map(|meta| #scrate::metadata_ir::SignedExtensionMetadataIR {
									identifier: meta.identifier,
									ty: meta.ty,
									additional_signed: meta.additional_signed,
								})
								.collect(),
					},
					ty: #scrate::scale_info::meta_type::<#runtime>(),
					apis: (&rt).runtime_metadata(),
					outer_enums: #scrate::metadata_ir::OuterEnumsIR {
						call_enum_ty: #scrate::scale_info::meta_type::<
								<#runtime as #system_path::Config>::RuntimeCall
							>(),
						event_enum_ty: #scrate::scale_info::meta_type::<RuntimeEvent>(),
						error_enum_ty: #scrate::scale_info::meta_type::<RuntimeError>(),
					}
				}
			}

			pub fn metadata() -> #scrate::metadata::RuntimeMetadataPrefixed {
				// Note: this always returns the V14 version. The runtime API function
				// must be deprecated.
				#scrate::metadata_ir::into_v14(#runtime::metadata_ir())
			}

			pub fn metadata_at_version(version: u32) -> Option<#scrate::OpaqueMetadata> {
				#scrate::metadata_ir::into_version(#runtime::metadata_ir(), version).map(|prefixed| {
					#scrate::OpaqueMetadata::new(prefixed.into())
				})
			}

			pub fn metadata_versions() -> #scrate::sp_std::vec::Vec<u32> {
				#scrate::metadata_ir::supported_versions()
			}
		}
	}
}

fn expand_pallet_metadata_storage(
	filtered_names: &[&'static str],
	runtime: &Ident,
	decl: &Pallet,
) -> TokenStream {
	if filtered_names.contains(&"Storage") {
		let instance = decl.instance.as_ref().into_iter();
		let path = &decl.path;

		quote! {
			Some(#path::Pallet::<#runtime #(, #path::#instance)*>::storage_metadata())
		}
	} else {
		quote!(None)
	}
}

fn expand_pallet_metadata_calls(
	filtered_names: &[&'static str],
	runtime: &Ident,
	decl: &Pallet,
) -> TokenStream {
	if filtered_names.contains(&"Call") {
		let instance = decl.instance.as_ref().into_iter();
		let path = &decl.path;

		quote! {
			Some(#path::Pallet::<#runtime #(, #path::#instance)*>::call_functions())
		}
	} else {
		quote!(None)
	}
}

fn expand_pallet_metadata_events(
	filtered_names: &[&'static str],
	runtime: &Ident,
	scrate: &TokenStream,
	decl: &Pallet,
) -> TokenStream {
	if filtered_names.contains(&"Event") {
		let path = &decl.path;
		let part_is_generic = !decl
			.find_part("Event")
			.expect("Event part exists; qed")
			.generics
			.params
			.is_empty();
		let pallet_event = match (decl.instance.as_ref(), part_is_generic) {
			(Some(inst), true) => quote!(#path::Event::<#runtime, #path::#inst>),
			(Some(inst), false) => quote!(#path::Event::<#path::#inst>),
			(None, true) => quote!(#path::Event::<#runtime>),
			(None, false) => quote!(#path::Event),
		};

		quote! {
			Some(
				#scrate::metadata_ir::PalletEventMetadataIR {
					ty: #scrate::scale_info::meta_type::<#pallet_event>()
				}
			)
		}
	} else {
		quote!(None)
	}
}

fn expand_pallet_metadata_constants(runtime: &Ident, decl: &Pallet) -> TokenStream {
	let path = &decl.path;
	let instance = decl.instance.as_ref().into_iter();

	quote! {
		#path::Pallet::<#runtime #(, #path::#instance)*>::pallet_constants_metadata()
	}
}

fn expand_pallet_metadata_errors(runtime: &Ident, decl: &Pallet) -> TokenStream {
	let path = &decl.path;
	let instance = decl.instance.as_ref().into_iter();

	quote! {
		#path::Pallet::<#runtime #(, #path::#instance)*>::error_metadata()
	}
}

fn expand_pallet_metadata_docs(runtime: &Ident, decl: &Pallet) -> TokenStream {
	let path = &decl.path;
	let instance = decl.instance.as_ref().into_iter();

	quote! {
		#path::Pallet::<#runtime #(, #path::#instance)*>::pallet_documentation_metadata()
	}
}
