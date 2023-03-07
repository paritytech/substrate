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
// limitations under the License.

use crate::pallet::Def;
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

	if let Some(trait_items) = &config.default_sub_trait {
		let associated_type_names = config_item
			.items
			.iter()
			.filter_map(
				|i| if let syn::TraitItem::Type(t) = i { Some(t.ident.clone()) } else { None },
			)
			.collect::<Vec<_>>();

		// we rarely use const and fns in config traits anyways... maybe not supporting them is good
		// enough.
		let const_names = Vec::<syn::Ident>::default();
		let fn_names = Vec::<syn::Ident>::default();

		quote::quote!(
			pub trait DefaultConfig {
				#(#trait_items)*
			}

			#[macro_export]
			#[doc(hidden)]
			// TODO: naming probably needs to be unique
			macro_rules! tt_config_items {
				{
					$caller:tt
					frame_support = [{$($frame_support:ident)::*}]
				} => {
					$( $frame_support )*::tt_return! {
						$caller
						type_items = [{ #(#associated_type_names),* }]
						fn_items = [{  }]
						const_items = [{  }]
					}
				}
			}

			pub use tt_config_items as tt_config_items;
		)
	} else {
		Default::default()
	}
}
