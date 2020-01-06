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

//! Declaration of store trait and implementation on module structure.

use proc_macro2::TokenStream;
use quote::quote;
use super::DeclStorageDefExt;

pub fn decl_and_impl(def: &DeclStorageDefExt) -> TokenStream {
	let decl_store_items = def.storage_lines.iter()
		.map(|sline| &sline.name)
		.fold(TokenStream::new(), |mut items, name| {
			items.extend(quote!(type #name;));
			items
		});

	let impl_store_items = def.storage_lines.iter()
		.fold(TokenStream::new(), |mut items, line| {
			let name = &line.name;
			let storage_struct = &line.storage_struct;

			items.extend(quote!(type #name = #storage_struct;));
			items
		});

	let visibility = &def.visibility;
	let store_trait = &def.store_trait;
	let module_struct = &def.module_struct;
	let module_impl = &def.module_impl;
	let where_clause = &def.where_clause;

	quote!(
		#visibility trait #store_trait {
			#decl_store_items
		}
		impl#module_impl #store_trait for #module_struct #where_clause {
			#impl_store_items
		}
	)
}
