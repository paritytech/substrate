// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::pallet::Def;
use syn::spanned::Spanned;

/// If attribute `#[pallet::generate_store(..)]` is defined then:
/// * generate Store trait with all storages,
/// * implement Store trait for Pallet.
pub fn expand_store_trait(def: &mut Def) -> proc_macro2::TokenStream {
	let (trait_vis, trait_store) = if let Some(store) = &def.pallet_struct.store {
		store
	} else {
		return Default::default()
	};

	let type_impl_gen = &def.type_impl_generics(trait_store.span());
	let type_use_gen = &def.type_use_generics(trait_store.span());
	let pallet_ident = &def.pallet_struct.pallet;

	let mut where_clauses = vec![&def.config.where_clause];
	where_clauses.extend(def.storages.iter().map(|storage| &storage.where_clause));
	let completed_where_clause = super::merge_where_clauses(&where_clauses);

	let storage_names = &def.storages.iter().map(|storage| &storage.ident).collect::<Vec<_>>();

	quote::quote_spanned!(trait_store.span() =>
		#trait_vis trait #trait_store {
			#(
				type #storage_names;
			)*
		}
		impl<#type_impl_gen> #trait_store for #pallet_ident<#type_use_gen>
			#completed_where_clause
		{
			#(
				type #storage_names = #storage_names<#type_use_gen>;
			)*
		}
	)
}
