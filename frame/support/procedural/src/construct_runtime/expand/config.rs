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

use crate::construct_runtime::Pallet;
use inflector::Inflector;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::str::FromStr;
use syn::Ident;

pub fn expand_outer_config(
	runtime: &Ident,
	pallet_decls: &[Pallet],
	scrate: &TokenStream,
) -> TokenStream {
	let mut types = TokenStream::new();
	let mut fields = TokenStream::new();
	let mut genesis_build_calls = TokenStream::new();
	let mut query_genesis_config_part_macros = Vec::new();

	for decl in pallet_decls {
		if let Some(pallet_entry) = decl.find_part("Config") {
			let path = &decl.path;
			let pallet_name = &decl.name;
			let path_str = path.into_token_stream().to_string();
			let config = format_ident!("{}Config", pallet_name);
			let field_name =
				&Ident::new(&pallet_name.to_string().to_snake_case(), decl.name.span());
			let part_is_generic = !pallet_entry.generics.params.is_empty();
			let attr = &decl.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
				let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
					.expect("was successfully parsed before; qed");
				quote! {
					#acc
					#attr
				}
			});

			types.extend(expand_config_types(attr, runtime, decl, &config, part_is_generic));
			fields.extend(quote!(#attr pub #field_name: #config,));
			genesis_build_calls
				.extend(expand_config_build_storage_call(scrate, &config, attr, field_name));
			query_genesis_config_part_macros.push(quote! {
				#path::__substrate_genesis_config_check::is_genesis_config_defined!(#pallet_name);
				#[cfg(feature = "std")]
				#path::__substrate_genesis_config_check::is_std_enabled_for_genesis!(#pallet_name, #path_str);
			});
		}
	}

	quote! {
		#( #query_genesis_config_part_macros )*

		#types

		use #scrate::__private::serde as __genesis_config_serde_import__;
		#[derive(#scrate::__private::serde::Serialize, #scrate::__private::serde::Deserialize, Default)]
		#[serde(rename_all = "camelCase")]
		#[serde(deny_unknown_fields)]
		#[serde(crate = "__genesis_config_serde_import__")]
		pub struct RuntimeGenesisConfig {
			#fields
		}

		#[cfg(any(feature = "std", test))]
		#[deprecated(note = "GenesisConfig is planned to be removed in December 2023. Use `RuntimeGenesisConfig` instead.")]
		pub type GenesisConfig = RuntimeGenesisConfig;

		#[cfg(any(feature = "std", test))]
		impl #scrate::sp_runtime::BuildStorage for RuntimeGenesisConfig {
			fn assimilate_storage(
				&self,
				storage: &mut #scrate::sp_runtime::Storage,
			) -> std::result::Result<(), String> {
				#scrate::__private::BasicExternalities::execute_with_storage(storage, || {
					<Self as #scrate::traits::BuildGenesisConfig>::build(&self);
					Ok(())
				})
			}
		}

		impl #scrate::traits::BuildGenesisConfig for RuntimeGenesisConfig {
			fn build(&self) {
				#genesis_build_calls
				<AllPalletsWithSystem as #scrate::traits::OnGenesis>::on_genesis();
			}
		}
	}
}

fn expand_config_types(
	attr: &TokenStream,
	runtime: &Ident,
	decl: &Pallet,
	config: &Ident,
	part_is_generic: bool,
) -> TokenStream {
	let path = &decl.path;

	match (decl.instance.as_ref(), part_is_generic) {
		(Some(inst), true) => quote! {
			#attr
			pub type #config = #path::GenesisConfig<#runtime, #path::#inst>;
		},
		(None, true) => quote! {
			#attr
			pub type #config = #path::GenesisConfig<#runtime>;
		},
		(_, false) => quote! {
			#attr
			pub type #config = #path::GenesisConfig;
		},
	}
}

fn expand_config_build_storage_call(
	scrate: &TokenStream,
	pallet_genesis_config: &Ident,
	attr: &TokenStream,
	field_name: &Ident,
) -> TokenStream {
	quote! {
		#attr
		<#pallet_genesis_config as #scrate::traits::BuildGenesisConfig>::build(&self.#field_name);
	}
}
