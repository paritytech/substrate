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

use crate::pallet::{Def, parse::helper::get_doc_literals};

/// * add various derive trait on GenesisConfig struct.
pub fn expand_genesis_config(def: &mut Def) -> proc_macro2::TokenStream {
	let genesis_config = if let Some(genesis_config) = &def.genesis_config {
		genesis_config
	} else {
		return Default::default()
	};
	let frame_support = &def.frame_support;

	let genesis_config_item = &mut def.item.content.as_mut()
		.expect("Checked by def parser").1[genesis_config.index];

	match genesis_config_item {
		syn::Item::Enum(syn::ItemEnum { attrs, ..}) |
		syn::Item::Struct(syn::ItemStruct { attrs, .. }) |
		syn::Item::Type(syn::ItemType { attrs, .. }) => {
			if get_doc_literals(&attrs).is_empty() {
				attrs.push(syn::parse_quote!(
					#[doc = r"
					Can be used to configure the
					[genesis state](https://substrate.dev/docs/en/knowledgebase/integrate/chain-spec#the-genesis-state)
					of the contracts pallet.
					"]
				));
			}
			attrs.push(syn::parse_quote!( #[cfg(feature = "std")] ));
			attrs.push(syn::parse_quote!(
				#[derive(#frame_support::Serialize, #frame_support::Deserialize)]
			));
			attrs.push(syn::parse_quote!( #[serde(rename_all = "camelCase")] ));
			attrs.push(syn::parse_quote!( #[serde(deny_unknown_fields)] ));
			attrs.push(syn::parse_quote!( #[serde(bound(serialize = ""))] ));
			attrs.push(syn::parse_quote!( #[serde(bound(deserialize = ""))] ));
		},
		_ => unreachable!("Checked by genesis_config parser"),
	}

	Default::default()
}
