// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use super::*;
use frame_support::{log, traits::OnRuntimeUpgrade};

pub mod v1 {
	use frame_support::{pallet_prelude::*, weights::Weight};

	use super::*;

	#[derive(Decode)]
	pub struct OldAssetDetails<Balance, AccountId, DepositBalance> {
		pub owner: AccountId,
		pub issuer: AccountId,
		pub admin: AccountId,
		pub freezer: AccountId,
		pub supply: Balance,
		pub deposit: DepositBalance,
		pub min_balance: Balance,
		pub is_sufficient: bool,
		pub accounts: u32,
		pub sufficients: u32,
		pub approvals: u32,
		pub is_frozen: bool,
	}

	impl<Balance, AccountId, DepositBalance> OldAssetDetails<Balance, AccountId, DepositBalance> {
		fn migrate_to_v1(self) -> AssetDetails<Balance, AccountId, DepositBalance> {
			AssetDetails {
				owner: self.owner,
				issuer: self.issuer,
				admin: self.admin,
				freezer: self.freezer,
				supply: self.supply,
				deposit: self.deposit,
				min_balance: self.min_balance,
				is_sufficient: self.is_sufficient,
				accounts: self.accounts,
				sufficients: self.sufficients,
				approvals: self.approvals,
				is_frozen: self.is_frozen,
				status: AssetStatus::Live,
			}
		}
	}

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current_version = Pallet::<T>::current_storage_version();
			let onchain_version = Pallet::<T>::on_chain_storage_version();
			if onchain_version == 0 && current_version == 1 {
				let mut translated = 0u64;
				Asset::<T>::translate::<
					OldAssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T>>,
					_,
				>(|_key, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v1())
				});
				current_version.put::<Pallet<T>>();
				log::info!(target: "runtime::assets", "Upgraded {} pools, storage to version {:?}", translated, current_version);
				T::DbWeight::get().reads_writes(translated + 1, translated + 1)
			} else {
				log::info!(target: "runtime::assets",  "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}
	}
}
