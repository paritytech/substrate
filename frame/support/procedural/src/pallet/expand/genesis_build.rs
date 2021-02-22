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

/// * implement the trait `sp_runtime::BuildModuleGenesisStorage`
/// * add #[cfg(features = "std")] to GenesisBuild implementation.
pub fn expand_genesis_build(def: &mut Def) -> proc_macro2::TokenStream {
	let genesis_config = if let Some(genesis_config) = &def.genesis_config {
		genesis_config
	} else {
		return Default::default()
	};
	let genesis_build = def.genesis_build.as_ref().expect("Checked by def parser");

	let frame_support = &def.frame_support;
	let type_impl_gen = &def.type_impl_generics(genesis_build.attr_span);
	let type_use_gen = &def.type_use_generics(genesis_build.attr_span);
	let trait_use_gen = if def.config.has_instance {
		quote::quote_spanned!(genesis_build.attr_span => T, I)
	} else {
		// `__InherentHiddenInstance` used by construct_runtime here is alias for `()`
		quote::quote_spanned!(genesis_build.attr_span => T, ())
	};
	let gen_cfg_ident = &genesis_config.genesis_config;

	let gen_cfg_use_gen = genesis_config.gen_kind.type_use_gen(genesis_build.attr_span);

	let genesis_build_item = &mut def.item.content.as_mut()
		.expect("Checked by def parser").1[genesis_build.index];

	let genesis_build_item_impl = if let syn::Item::Impl(impl_) = genesis_build_item {
		impl_
	} else {
		unreachable!("Checked by genesis_build parser")
	};

	genesis_build_item_impl.attrs.push(syn::parse_quote!( #[cfg(feature = "std")] ));
	let where_clause = &genesis_build.where_clause;

	quote::quote_spanned!(genesis_build.attr_span =>
		#[cfg(feature = "std")]
		impl<#type_impl_gen> #frame_support::sp_runtime::BuildModuleGenesisStorage<#trait_use_gen>
			for #gen_cfg_ident<#gen_cfg_use_gen> #where_clause
		{
			fn build_module_genesis_storage(
				&self,
				storage: &mut #frame_support::sp_runtime::Storage,
			) -> std::result::Result<(), std::string::String> {
				#frame_support::BasicExternalities::execute_with_storage(storage, || {
					<Self as #frame_support::traits::GenesisBuild<#type_use_gen>>::build(self);
					Ok(())
				})
			}
		}
	)
}
