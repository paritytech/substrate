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

use crate::{pallet::Def, COUNTER};
use frame_support_procedural_tools::get_doc_literals;

///
/// * Generate default rust doc
pub fn expand_config(def: &mut Def) -> proc_macro2::TokenStream {
	let config = &def.config;
	let config_item = {
		let item = &mut def.item.content.as_mut().expect("Checked by def parser").1[config.index];
		if let syn::Item::Trait(item) = item {
			item
		} else {
			unreachable!("Checked by config parser")
		}
	};

	if get_doc_literals(&config_item.attrs).is_empty() {
		config_item.attrs.push(syn::parse_quote!(
			#[doc = r"
			Configuration trait of this pallet.

			Implement this type for a runtime in order to customize this pallet.
			"]
		));
	}

	let (config_type_names, config_type_defaults) =
		config
			.defaults_metadata
			.iter()
			.fold((Vec::new(), Vec::new()), |mut acc, metadata| {
				acc.0.push(metadata.ident.clone());
				acc.1.push(metadata.default.clone());
				acc
			});

	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let macro_ident =
		syn::Ident::new(&format!("__use_default_config_for_{}", count), config.attr_span);

	quote::quote! {
		#[doc(hidden)]
		pub mod __substrate_config_defaults {
			#[macro_export]
			#[doc(hidden)]
			macro_rules! #macro_ident {
				#(
					(#config_type_names) => {
						type #config_type_names = #config_type_defaults;
					};
				)*
				($no_default_config_name:ident) => {
					compile_error!(concat!(
						"associated type `",
						stringify!($no_default_config_name),
						"` does not have a default type specified, or does not exist"
					));
				};
			}

			#[doc(hidden)]
			pub use #macro_ident as use_default_config_for;
		}
	}
}
