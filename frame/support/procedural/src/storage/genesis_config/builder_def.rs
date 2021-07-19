// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Builder logic definition used to build genesis storage.

use frame_support_procedural_tools::syn_ext as ext;
use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use quote::{quote, quote_spanned};
use super::super::{DeclStorageDefExt, StorageLineTypeDef};

/// Definition of builder blocks, each block insert some value in the storage.
/// They must be called inside externalities, and with `self` being the genesis config.
pub struct BuilderDef {
	/// Contains:
	/// * build block for storage with build attribute.
	/// * build block for storage with config attribute and no build attribute.
	/// * build block for extra genesis build expression.
	pub blocks: Vec<TokenStream>,
	/// The build blocks requires generic traits.
	pub is_generic: bool,
}

impl BuilderDef {
	pub fn from_def(scrate: &TokenStream, def: &DeclStorageDefExt) -> Self {
		let mut blocks = Vec::new();
		let mut is_generic = false;

		for line in def.storage_lines.iter() {
			let storage_struct = &line.storage_struct;
			let storage_trait = &line.storage_trait;
			let value_type = &line.value_type;

			// Defines the data variable to use for insert at genesis either from build or config.
			let mut data = None;

			if let Some(builder) = &line.build {
				is_generic |= ext::expr_contains_ident(&builder, &def.module_runtime_generic);
				is_generic |= line.is_generic;

				data = Some(match &line.storage_type {
					StorageLineTypeDef::Simple(_) if line.is_option =>
						quote_spanned!(builder.span() =>
							// NOTE: the type of `data` is specified when used later in the code
							let builder: fn(&Self) -> _ = #builder;
							let data = builder(self);
							let data = Option::as_ref(&data);
						),
					_ => quote_spanned!(builder.span() =>
						// NOTE: the type of `data` is specified when used later in the code
						let builder: fn(&Self) -> _ = #builder;
						let data = &builder(self);
					),
				});
			} else if let Some(config) = &line.config {
				is_generic |= line.is_generic;

				data = Some(match &line.storage_type {
					StorageLineTypeDef::Simple(_) if line.is_option =>
						quote!( let data = Some(&self.#config); ),
					_ => quote!( let data = &self.#config; ),
				});
			};

			if let Some(data) = data {
				blocks.push(match &line.storage_type {
					StorageLineTypeDef::Simple(_) if line.is_option => {
						quote!{{
							#data
							let v: Option<&#value_type>= data;
							if let Some(v) = v {
								<#storage_struct as #scrate::#storage_trait>::put::<&#value_type>(v);
							}
						}}
					},
					StorageLineTypeDef::Simple(_) if !line.is_option => {
						quote!{{
							#data
							let v: &#value_type = data;
							<#storage_struct as #scrate::#storage_trait>::put::<&#value_type>(v);
						}}
					},
					StorageLineTypeDef::Simple(_) => unreachable!(),
					StorageLineTypeDef::Map(map) => {
						let key = &map.key;
						quote!{{
							#data
							let data: &#scrate::sp_std::vec::Vec<(#key, #value_type)> = data;
							data.iter().for_each(|(k, v)| {
								<#storage_struct as #scrate::#storage_trait>::insert::<
									&#key, &#value_type
								>(k, v);
							});
						}}
					},
					StorageLineTypeDef::DoubleMap(map) => {
						let key1 = &map.key1;
						let key2 = &map.key2;
						quote!{{
							#data
							let data: &#scrate::sp_std::vec::Vec<(#key1, #key2, #value_type)> = data;
							data.iter().for_each(|(k1, k2, v)| {
								<#storage_struct as #scrate::#storage_trait>::insert::<
									&#key1, &#key2, &#value_type
								>(k1, k2, v);
							});
						}}
					},
					StorageLineTypeDef::NMap(map) => {
						let key_tuple = map.to_key_tuple();
						let key_arg = if map.keys.len() == 1 {
							quote!((k,))
						} else {
							quote!(k)
						};
						quote!{{
							#data
							let data: &#scrate::sp_std::vec::Vec<(#key_tuple, #value_type)> = data;
							data.iter().for_each(|(k, v)| {
								<#storage_struct as #scrate::#storage_trait>::insert(#key_arg, v);
							});
						}}
					},
				});
			}
		}

		if let Some(builder) = def.extra_genesis_build.as_ref() {
			is_generic |= ext::expr_contains_ident(&builder, &def.module_runtime_generic);

			blocks.push(quote_spanned! { builder.span() =>
				let extra_genesis_builder: fn(&Self) = #builder;
				extra_genesis_builder(self);
			});
		}


		Self {
			blocks,
			is_generic,
		}
	}
}
