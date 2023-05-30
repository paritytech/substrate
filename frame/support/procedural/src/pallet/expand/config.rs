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
use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_quote, Item};

///
/// * Generate default rust doc
pub fn expand_config(def: &mut Def) -> TokenStream {
	let config = &def.config;
	let config_item = {
		let item = &mut def.item.content.as_mut().expect("Checked by def parser").1[config.index];
		if let Item::Trait(item) = item {
			item
		} else {
			unreachable!("Checked by config parser")
		}
	};

	config_item.attrs.insert(
		0,
		parse_quote!(
			#[doc = r"
Configuration trait of this pallet.

The main purpose of this trait is to act as an interface between this pallet and the runtime in
which it is embedded in. A type, function, or constant in this trait is essentially left to be
configured by the runtime that includes this pallet.

Consequently, a runtime that wants to include this pallet must implement this trait."
			]
		),
	);

	// we only emit `DefaultConfig` if there are trait items, so an empty `DefaultConfig` is
	// impossible consequently
	if config.default_sub_trait.len() > 0 {
		let trait_items = &config.default_sub_trait;
		quote!(
			/// Based on [`Config`]. Auto-generated by
			/// [`#[pallet::config(with_default)]`](`frame_support::pallet_macros::config`).
			/// Can be used in tandem with
			/// [`#[register_default_config]`](`frame_support::register_default_config`) and
			/// [`#[derive_impl]`](`frame_support::derive_impl`) to derive test config traits
			/// based on existing pallet config traits in a safe and developer-friendly way.
			///
			/// See [here](`frame_support::pallet_macros::config`) for more information and caveats about
			/// the auto-generated `DefaultConfig` trait and how it is generated.
			pub trait DefaultConfig {
				#(#trait_items)*
			}
		)
	} else {
		Default::default()
	}
}
