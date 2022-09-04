// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
	let (where_clause, span, has_runtime_upgrade, pre_state_digest_type) = match def.hooks.as_ref()
	{
		Some(hooks) => {
			let where_clause = hooks.where_clause.clone();
			let span = hooks.attr_span;
			let has_runtime_upgrade = hooks.has_runtime_upgrade;
			let pre_state_digest_type = hooks.pre_state_digest_type.clone();
			(where_clause, span, has_runtime_upgrade, pre_state_digest_type)
		},
		None => (None, def.pallet_struct.attr_span, false, None),
	};
	// use `PreStateDigest`'s default type `()` if it is not set explicitly
	let pre_state_digest_type =
		pre_state_digest_type.map_or(quote::quote! { () }, |t| quote::quote! { #t });

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
			#frame_support::log::info!(
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
		>::name::<Self>().expect("Every active pallet has a name in the runtime; qed");
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
				#frame_support::traits::Hooks<<T as #frame_system::Config>::BlockNumber, #pre_state_digest_type>
				for Pallet<#type_use_gen> {}
		}
	} else {
		proc_macro2::TokenStream::new()
	};

	quote::quote_spanned!(span =>
		#hooks_impl

		impl<#type_impl_gen>
			#frame_support::traits::OnFinalize<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_finalize(n: <T as #frame_system::Config>::BlockNumber) {
				#frame_support::sp_tracing::enter_span!(
					#frame_support::sp_tracing::trace_span!("on_finalize")
				);
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::on_finalize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnIdle<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_idle(
				n: <T as #frame_system::Config>::BlockNumber,
				remaining_weight: #frame_support::weights::Weight
			) -> #frame_support::weights::Weight {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::on_idle(n, remaining_weight)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnInitialize<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn on_initialize(
				n: <T as #frame_system::Config>::BlockNumber
			) -> #frame_support::weights::Weight {
				#frame_support::sp_tracing::enter_span!(
					#frame_support::sp_tracing::trace_span!("on_initialize")
				);
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::on_initialize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnRuntimeUpgrade
			for #pallet_ident<#type_use_gen> #where_clause
		{
			type PreStateDigest = #pre_state_digest_type;

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
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::on_runtime_upgrade()
			}

			#[cfg(not(feature = "try-runtime"))]
			fn pre_upgrade() -> Result<Self::PreStateDigest, &'static str> {
				Ok(Self::PreStateDigest::default())
			}

			#[cfg(feature = "try-runtime")]
			fn pre_upgrade() -> Result<Self::PreStateDigest, &'static str> {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::pre_upgrade()
			}

			#[cfg(feature = "try-runtime")]
			fn post_upgrade(digest: Self::PreStateDigest) -> Result<(), &'static str> {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::post_upgrade(digest)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OffchainWorker<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn offchain_worker(n: <T as #frame_system::Config>::BlockNumber) {
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
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
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::integrity_test()
			}
		}

		#[cfg(feature = "try-runtime")]
		impl<#type_impl_gen>
			#frame_support::traits::TryState<<T as #frame_system::Config>::BlockNumber>
			for #pallet_ident<#type_use_gen> #where_clause
		{
			fn try_state(
				n: <T as #frame_system::Config>::BlockNumber,
				_s: #frame_support::traits::TryStateSelect
			) -> Result<(), &'static str> {
				#log_try_state
				<
					Self as #frame_support::traits::Hooks<
						<T as #frame_system::Config>::BlockNumber,
						#pre_state_digest_type
					>
				>::try_state(n)
			}
		}
	)
}
