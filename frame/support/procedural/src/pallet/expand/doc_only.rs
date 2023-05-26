// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

use proc_macro2::Span;

use crate::pallet::Def;

pub fn expand_doc_only(def: &mut Def) -> proc_macro2::TokenStream {
	let storage_names = def.storages.iter().map(|storage| &storage.ident);
	let storage_docs = def.storages.iter().map(|storage| &storage.docs);
	let dispatchables = if let Some(call_def) = &def.call {
		let type_impl_generics = def.type_impl_generics(Span::call_site());
		call_def
			.methods
			.iter()
			.map(|method| {
				let name = &method.name;
				let args = &method
					.args
					.iter()
					.map(|(_, arg_name, arg_type)| quote::quote!( #arg_name: #arg_type, ))
					.collect::<proc_macro2::TokenStream>();
				let docs = &method.docs;
				let line_2 =
					format!(" designed to document the [`{}`][`Call::{}`] variant of", name, name);
				quote::quote!(
					#( #[doc = #docs] )*
					///
					/// ---
					///
					/// NOTE: This function is an automatically generated, doc only, uncallable stub.
					#[ doc = #line_2 ]
					/// the pallet [`Call`] enum. You should not attempt to call this function
					/// directly.
					pub fn #name<#type_impl_generics>(#args) { unreachable!(); }
				)
			})
			.collect::<proc_macro2::TokenStream>()
	} else {
		quote::quote!()
	};

	quote::quote!(
		/// Auto-generated docs-only module listing all defined storage types for this pallet.
		/// Note that members of this module cannot be used directly and are only provided for
		/// documentation purposes.
		#[cfg(doc)]
		pub mod storage_types {
			use super::*;
			#(
				#( #[doc = #storage_docs] )*
				pub struct #storage_names();
			)*
		}

		/// Auto-generated docs-only module listing all defined dispatchables for this pallet.
		/// Note that members of this module cannot be used directly and are only provided for
		/// documentation purposes.
		#[cfg(doc)]
		pub mod dispatchables {
			use super::*;
			#dispatchables
		}
	)
}
