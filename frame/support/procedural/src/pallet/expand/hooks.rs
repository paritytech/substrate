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

/// * implement the individual traits using the Hooks trait
pub fn expand_hooks(def: &mut Def) -> proc_macro2::TokenStream {
	let frame_support = &def.frame_support;
	let type_impl_gen = &def.type_impl_generics(def.hooks.attr_span);
	let type_use_gen = &def.type_use_generics(def.hooks.attr_span);
	let pallet_ident = &def.pallet_struct.pallet;
	let where_clause = &def.hooks.where_clause;
	let frame_system = &def.frame_system;

	quote::quote_spanned!(def.hooks.attr_span =>
		impl<#type_impl_gen>
			#frame_support::traits::OnFinalize<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_finalize(n: <T as #frame_system::Config>::BlockNumber) {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber
					>
				>::on_finalize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnInitialize<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_initialize(
				n: <T as #frame_system::Config>::BlockNumber
			) -> #frame_support::weights::Weight {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber
					>
				>::on_initialize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnRuntimeUpgrade
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_runtime_upgrade() -> #frame_support::weights::Weight {
				let result = <
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber
					>
				>::on_runtime_upgrade();

				#frame_support::crate_to_pallet_version!()
					.put_into_storage::<<T as #frame_system::Config>::PalletInfo, Self>();

				let additional_write = <
					<T as #frame_system::Config>::DbWeight as #frame_support::traits::Get<_>
				>::get().writes(1);

				result.saturating_add(additional_write)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OffchainWorker<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn offchain_worker(n: <T as #frame_system::Config>::BlockNumber) {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber
					>
				>::offchain_worker(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::IntegrityTest
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn integrity_test() {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber
					>
				>::integrity_test()
			}
		}
	)
}
