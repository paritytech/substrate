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

//! Implementation of getters on module structure.

use proc_macro2::TokenStream;
use quote::quote;
use super::{DeclStorageDefExt, StorageLineTypeDef};

pub fn impl_getters(def: &DeclStorageDefExt) -> TokenStream {
	let scrate = &def.hidden_crate;
	let mut getters = TokenStream::new();

	for (get_fn, line) in def.storage_lines.iter()
		.filter_map(|line| line.getter.as_ref().map(|get_fn| (get_fn, line)))
	{
		let attrs = &line.doc_attrs;

		let storage_struct = &line.storage_struct;
		let storage_trait = &line.storage_trait;

		let getter = match &line.storage_type {
			StorageLineTypeDef::Simple(value) => {
				quote!{
					#( #[ #attrs ] )*
					pub fn #get_fn() -> #value {
						<#storage_struct as #scrate::#storage_trait>::get()
					}
				}
			},
			StorageLineTypeDef::Map(map) => {
				let key = &map.key;
				let value = &map.value;
				quote!{
					#( #[ #attrs ] )*
					pub fn #get_fn<K: #scrate::codec::EncodeLike<#key>>(key: K) -> #value {
						<#storage_struct as #scrate::#storage_trait>::get(key)
					}
				}
			},
			StorageLineTypeDef::DoubleMap(map) => {
				let key1 = &map.key1;
				let key2 = &map.key2;
				let value = &map.value;
				quote!{
					pub fn #get_fn<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> #value
					where
						KArg1: #scrate::codec::EncodeLike<#key1>,
						KArg2: #scrate::codec::EncodeLike<#key2>,
					{
						<#storage_struct as #scrate::#storage_trait>::get(k1, k2)
					}
				}
			},
			StorageLineTypeDef::NMap(map) => {
				let keygen = map.to_keygen_struct(&def.hidden_crate);
				let value = &map.value;
				quote!{
					pub fn #get_fn<KArg>(key: KArg) -> #value
					where
						KArg: #scrate::storage::types::EncodeLikeTuple<
							<#keygen as #scrate::storage::types::KeyGenerator>::KArg
						>
							+ #scrate::storage::types::TupleToEncodedIter,
					{
						<#storage_struct as #scrate::#storage_trait>::get(key)
					}
				}
			}
		};
		getters.extend(getter);
	}

	let module_struct = &def.module_struct;
	let module_impl = &def.module_impl;
	let where_clause = &def.where_clause;

	quote!(
		impl#module_impl #module_struct #where_clause {
			#getters
		}
	)
}
