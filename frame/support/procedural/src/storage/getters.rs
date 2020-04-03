// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Implementation of getters on module structure.

use proc_macro2::TokenStream;
use quote::quote;
use super::{DeclStorageDefExt, StorageLineTypeDef};

pub fn impl_getters(scrate: &TokenStream, def: &DeclStorageDefExt) -> TokenStream {
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
