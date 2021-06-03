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

//! Implementation of trait `StorageInfoTrait` on module structure.

use proc_macro2::TokenStream;
use quote::quote;
use super::DeclStorageDefExt;

pub fn impl_storage_info(def: &DeclStorageDefExt) -> TokenStream {
	if !def.generate_storage_info {
		return Default::default()
	}

	let scrate = &def.hidden_crate;

	let mut res_append_storage = TokenStream::new();

	for line in def.storage_lines.iter() {
		let storage_struct = &line.storage_struct;

		res_append_storage.extend(quote!(
			let mut storage_info = <
				#storage_struct as #scrate::traits::StorageInfoTrait
			>::storage_info();
			res.append(&mut storage_info);
		));
	}

	let module_struct = &def.module_struct;
	let module_impl = &def.module_impl;
	let where_clause = &def.where_clause;

	quote!(
		impl#module_impl #scrate::traits::StorageInfoTrait for #module_struct #where_clause {
			fn storage_info() -> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo> {
				let mut res = #scrate::sp_std::vec![];
				#res_append_storage
				res
			}
		}
	)
}
