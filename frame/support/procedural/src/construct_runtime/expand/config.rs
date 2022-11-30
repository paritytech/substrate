// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::construct_runtime::Pallet;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

pub fn expand_outer_config(
	runtime: &Ident,
	pallet_decls: &[Pallet],
	scrate: &TokenStream,
) -> TokenStream {
	let mut types = TokenStream::new();
	let mut fields = TokenStream::new();
	let mut build_storage_calls = TokenStream::new();

	for decl in pallet_decls {
		if let Some(pallet_entry) = decl.find_part("Config") {
			let config = format_ident!("{}Config", decl.name);
			let mod_name = decl.pallet.mod_name();
			let field_name = if let Some(inst) = decl.instance.as_ref() {
				format_ident!("{}_{}", mod_name, inst)
			} else {
				mod_name
			};
			let part_is_generic = !pallet_entry.generics.params.is_empty();

			types.extend(expand_config_types(runtime, decl, &config, part_is_generic));
			fields.extend(quote!(pub #field_name: #config,));
			build_storage_calls.extend(expand_config_build_storage_call(scrate, runtime, decl, &field_name));
		}
	}

	quote!{
		#types

		#[cfg(any(feature = "std", test))]
		use #scrate::serde as __genesis_config_serde_import__;
		#[cfg(any(feature = "std", test))]
		#[derive(#scrate::serde::Serialize, #scrate::serde::Deserialize, Default)]
		#[serde(rename_all = "camelCase")]
		#[serde(deny_unknown_fields)]
		#[serde(crate = "__genesis_config_serde_import__")]
		#[allow(non_snake_case)]
		pub struct GenesisConfig {
			#fields
		}

		#[cfg(any(feature = "std", test))]
		impl #scrate::sp_runtime::BuildStorage for GenesisConfig {
			fn assimilate_storage(
				&self,
				storage: &mut #scrate::sp_runtime::Storage,
			) -> std::result::Result<(), String> {
				#build_storage_calls

				#scrate::BasicExternalities::execute_with_storage(storage, || {
					<AllPalletsWithSystem as #scrate::traits::OnGenesis>::on_genesis();
				});

				Ok(())
			}
		}
	}
}

fn expand_config_types(
	runtime: &Ident,
	decl: &Pallet,
	config: &Ident,
	part_is_generic: bool,
) -> TokenStream {
	let path = &decl.pallet;

	match (decl.instance.as_ref(), part_is_generic) {
		(Some(inst), true) => quote!{
			#[cfg(any(feature = "std", test))]
			pub type #config = #path::GenesisConfig<#runtime, #path::#inst>;
		},
		(None, true) => quote!{
			#[cfg(any(feature = "std", test))]
			pub type #config = #path::GenesisConfig<#runtime>;
		},
		(_, false) => quote!{
			#[cfg(any(feature = "std", test))]
			pub type #config = #path::GenesisConfig;
		},
	}
}

fn expand_config_build_storage_call(
	scrate: &TokenStream,
	runtime: &Ident,
	decl: &Pallet,
	field_name: &Ident,
) -> TokenStream {
	let path = &decl.pallet;
	let instance = if let Some(inst) = decl.instance.as_ref() {
		quote!(#path::#inst)
	} else {
		quote!(#path::__InherentHiddenInstance)
	};

	quote!{
		#scrate::sp_runtime::BuildModuleGenesisStorage::
			<#runtime, #instance>::build_module_genesis_storage(&self.#field_name, storage)?;
	}
}
