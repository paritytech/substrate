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

/// * implement the individual traits using the Hooks trait
pub fn expand_hooks(def: &mut Def) -> proc_macro2::TokenStream {
	let (where_clause, span, has_runtime_upgrade) = match def.hooks.as_ref() {
		Some(hooks) => {
			let where_clause = hooks.where_clause.clone();
			let span = hooks.attr_span;
			let has_runtime_upgrade = hooks.has_runtime_upgrade;
			(where_clause, span, has_runtime_upgrade)
		},
		None => (def.config.where_clause.clone(), def.pallet_struct.attr_span, false),
	};

	let frame_support = &def.frame_support;
	let type_impl_gen = &def.type_impl_generics(span);
	let type_use_gen = &def.type_use_generics(span);
	let pallet_ident = &def.pallet_struct.pallet;
	let frame_system = &def.frame_system;

	let log_runtime_upgrade = if has_runtime_upgrade {
		// a migration is defined here.
		quote::quote! {
			#frame_support::log::info!(
				target: #frame_support::LOG_TARGET,
				"⚠️ {} declares internal migrations (which *might* execute). \
				 On-chain `{:?}` vs current storage version `{:?}`",
				pallet_name,
				<Self as #frame_support::traits::GetStorageVersion>::on_chain_storage_version(),
				<Self as #frame_support::traits::GetStorageVersion>::current_storage_version(),
			);
		}
	} else {
		// default.
		quote::quote! {
			#frame_support::log::debug!(
				target: #frame_support::LOG_TARGET,
				"✅ no migration for {}",
				pallet_name,
			);
		}
	};

	let log_try_state = quote::quote! {
		let pallet_name = <
			<T as #frame_system::Config>::PalletInfo
			as
			#frame_support::traits::PalletInfo
		>::name::<Self>().expect("No name found for the pallet! This usually means that the pallet wasn't added to `construct_runtime!`.");
		#frame_support::log::debug!(
			target: #frame_support::LOG_TARGET,
			"🩺 try-state pallet {:?}",
			pallet_name,
		);
	};

	let hooks_impl = if def.hooks.is_none() {
		let frame_system = &def.frame_system;
		quote::quote! {
			impl<#type_impl_gen>
				#frame_support::traits::Hooks<#frame_system::pallet_prelude::BlockNumberFor::<T>>
				for #pallet_ident<#type_use_gen> #where_clause {}
		}
	} else {
		proc_macro2::TokenStream::new()
	};

	// If a storage version is set, we should ensure that the storage version on chain matches the
	// current storage version. This assumes that `Executive` is running custom migrations before
	// the pallets are called.
	let post_storage_version_check = if def.pallet_struct.storage_version.is_some() {
		quote::quote! {
			let on_chain_version = <Self as #frame_support::traits::GetStorageVersion>::on_chain_storage_version();
			let current_version = <Self as #frame_support::traits::GetStorageVersion>::current_storage_version();

			if on_chain_version != current_version {
				let pallet_name = <
					<T as #frame_system::Config>::PalletInfo
					as
					#frame_support::traits::PalletInfo
				>::name::<Self>().unwrap_or("<unknown pallet name>");

				#frame_support::log::error!(
					target: #frame_support::LOG_TARGET,
					"{}: On chain storage version {:?} doesn't match current storage version {:?}.",
					pallet_name,
					on_chain_version,
					current_version,
				);

				return Err("On chain and current storage version do not match. Missing runtime upgrade?".into());
			}
		}
	} else {
		quote::quote! {
			let on_chain_version = <Self as #frame_support::traits::GetStorageVersion>::on_chain_storage_version();

			if on_chain_version != #frame_support::traits::StorageVersion::new(0) {
				let pallet_name = <
					<T as #frame_system::Config>::PalletInfo
					as
					#frame_support::traits::PalletInfo
				>::name::<Self>().unwrap_or("<unknown pallet name>");

				#frame_support::log::error!(
					target: #frame_support::LOG_TARGET,
					"{}: On chain storage version {:?} is set to non zero, \
					 while the pallet is missing the `#[pallet::storage_version(VERSION)]` attribute.",
					pallet_name,
					on_chain_version,
				);

				return Err("On chain storage version set, while the pallet doesn't \
							have the `#[pallet::storage_version(VERSION)]` attribute.".into());
			}
		}
	};

	quote::quote_spanned!(span =>
		#hooks_impl

		impl<#type_impl_gen>
			#frame_support::traits::OnFinalize<#frame_system::pallet_prelude::BlockNumberFor::<T>>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_finalize(n: #frame_system::pallet_prelude::BlockNumberFor::<T>) {
				#frame_support::sp_tracing::enter_span!(
					#frame_support::sp_tracing::trace_span!("on_finalize")
				);
				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::on_finalize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnIdle<#frame_system::pallet_prelude::BlockNumberFor::<T>>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_idle(
				n: #frame_system::pallet_prelude::BlockNumberFor::<T>,
				remaining_weight: #frame_support::weights::Weight
			) -> #frame_support::weights::Weight {
				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::on_idle(n, remaining_weight)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnInitialize<#frame_system::pallet_prelude::BlockNumberFor::<T>>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_initialize(
				n: #frame_system::pallet_prelude::BlockNumberFor::<T>
			) -> #frame_support::weights::Weight {
				#frame_support::sp_tracing::enter_span!(
					#frame_support::sp_tracing::trace_span!("on_initialize")
				);
				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::on_initialize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnRuntimeUpgrade
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_runtime_upgrade() -> #frame_support::weights::Weight {
				#frame_support::sp_tracing::enter_span!(
					#frame_support::sp_tracing::trace_span!("on_runtime_update")
				);

				// log info about the upgrade.
				let pallet_name = <
					<T as #frame_system::Config>::PalletInfo
					as
					#frame_support::traits::PalletInfo
				>::name::<Self>().unwrap_or("<unknown pallet name>");
				#log_runtime_upgrade

				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::on_runtime_upgrade()
			}

			#[cfg(feature = "try-runtime")]
			fn pre_upgrade() -> Result<#frame_support::sp_std::vec::Vec<u8>, #frame_support::sp_runtime::TryRuntimeError> {
				<
					Self
					as
					#frame_support::traits::Hooks<#frame_system::pallet_prelude::BlockNumberFor::<T>>
				>::pre_upgrade()
			}

			#[cfg(feature = "try-runtime")]
			fn post_upgrade(state: #frame_support::sp_std::vec::Vec<u8>) -> Result<(), #frame_support::sp_runtime::TryRuntimeError> {
				#post_storage_version_check

				<
					Self
					as
					#frame_support::traits::Hooks<#frame_system::pallet_prelude::BlockNumberFor::<T>>
				>::post_upgrade(state)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OffchainWorker<#frame_system::pallet_prelude::BlockNumberFor::<T>>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn offchain_worker(n: #frame_system::pallet_prelude::BlockNumberFor::<T>) {
				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::offchain_worker(n)
			}
		}

		// Integrity tests are only required for when `std` is enabled.
		#frame_support::std_enabled! {
			impl<#type_impl_gen>
				#frame_support::traits::IntegrityTest
			for #pallet_ident<#type_use_gen> #where_clause
			{
				fn integrity_test() {
					<
						Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
						>
						>::integrity_test()
				}
			}
		}

		#[cfg(feature = "try-runtime")]
		impl<#type_impl_gen>
			#frame_support::traits::TryState<#frame_system::pallet_prelude::BlockNumberFor::<T>>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn try_state(
				n: #frame_system::pallet_prelude::BlockNumberFor::<T>,
				_s: #frame_support::traits::TryStateSelect
			) -> Result<(), #frame_support::sp_runtime::TryRuntimeError> {
				#log_try_state
				<
					Self as #frame_support::traits::Hooks<
						#frame_system::pallet_prelude::BlockNumberFor::<T>
					>
				>::try_state(n)
			}
		}
	)
}
