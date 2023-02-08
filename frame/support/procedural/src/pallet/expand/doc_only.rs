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

use crate::pallet::Def;

pub fn expand_doc_only(def: &mut Def) -> proc_macro2::TokenStream {
	let storage_names = &def.storages.iter().map(|storage| &storage.ident).collect::<Vec<_>>();
	let storage_viss = &def.storages.iter().map(|storage| &storage.vis).collect::<Vec<_>>();
	let dispatchables = {
		if let Some(call_def) = &def.call {
			call_def.methods.iter().map(|method| {
				let name = &method.name;
				let args = &method.args.iter().map(|(_, arg_name, arg_type)| {
					quote::quote!( #arg_name: #arg_type, )
				}).collect::<proc_macro2::TokenStream>();
				let docs = &method.docs;

				quote::quote!(
					#( #[doc = #docs] )*
					pub fn #name(#args) { unreachable!(); }
				)
			}).collect::<proc_macro2::TokenStream>()
		} else {
			quote::quote!()
		}
	};

	quote::quote!(
		#[cfg(doc)]
		pub mod storage_types {
			use super::*;
			#(
				#storage_viss use super::#storage_names;
			)*
		}
		#[cfg(doc)]
		pub mod dispatchables {
			use super::*;
			#dispatchables
		}
	)
}
