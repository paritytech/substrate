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

//! This migration unlocks all `Voter` and `SeatHolder` `stake`s, and unreserves all `Voter` and
//! `SeatHolder` `deposit`s.

use codec::{Decode, Encode};
use frame_support::traits::OnRuntimeUpgrade;

#[cfg(feature = "try-runtime")]
use frame_support::ensure;
#[cfg(feature = "try-runtime")]
use sp_std::collections::btree_map::BTreeMap;
#[cfg(feature = "try-runtime")]
use sp_std::vec::Vec;

#[derive(Debug, Encode, Decode)]
struct PreMigrationData<T: frame_system::Config> {
	account_staked_sums: BTreeMap<T::AccountId, u64>,
	account_deposited_sums: BTreeMap<T::AccountId, u64>,
	account_locked_before: BTreeMap<T::AccountId, u64>,
	account_reserved_before: BTreeMap<T::AccountId, u64>,
}

pub struct UnlockAndUnreserveAllFunds<T: crate::Config + pallet_balances::Config>(
	sp_std::marker::PhantomData<T>,
);
impl<T: crate::Config + pallet_balances::Config> OnRuntimeUpgrade
	for UnlockAndUnreserveAllFunds<T>
{
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use frame_support::traits::ReservableCurrency;
		use pallet_balances::{BalanceLock, Locks, Reasons};
		use sp_core::Get;
		use sp_runtime::{traits::Zero, SaturatedConversion};
		use sp_std::collections::btree_set::BTreeSet;

		// Get storage items containing locked and reserved balances.
		let members = crate::Members::<T>::get();
		let runner_ups = crate::RunnersUp::<T>::get();
		let voters: Vec<(T::AccountId, crate::Voter<T::AccountId, crate::BalanceOf<T>>)> =
			crate::Voting::<T>::iter().collect::<Vec<_>>();

		// Get the total amount staked and deposited for each account, across members, runners up,
		// and voters.
		let mut account_staked_sums: BTreeMap<T::AccountId, u64> = BTreeMap::new();
		let mut account_deposited_sums: BTreeMap<T::AccountId, u64> = BTreeMap::new();
		for member in members.iter().chain(runner_ups.iter()) {
			let staked_sum = account_staked_sums.entry(member.who.clone()).or_insert(0);
			*staked_sum += member.stake.saturated_into::<u64>();

			let deposited_sum = account_deposited_sums.entry(member.who.clone()).or_insert(0);
			*deposited_sum += member.deposit.saturated_into::<u64>();
		}
		for (account_id, voter) in voters.iter() {
			let staked_sum = account_staked_sums.entry(account_id.clone()).or_insert(Zero::zero());
			*staked_sum = staked_sum.saturating_add(voter.stake.saturated_into::<u64>().into());

			let deposited_sum = account_deposited_sums.entry(account_id.clone()).or_insert(0);
			*deposited_sum += voter.deposit.saturated_into::<u64>();
		}

		log::info!("staked");
		for (account_id, staked_sum) in account_staked_sums.iter() {
			log::info!("{:?}: {}", account_id, staked_sum);
		}
		log::info!("deposited");
		for (account_id, deposited_sum) in account_deposited_sums.iter() {
			log::info!("{:?}: {}", account_id, deposited_sum);
		}

		// Now get the actual locked and reserved amounts for each account *before* the migration,
		// so we can check that the amounts are reduced by the expected amounts post-migration.
		let all_accounts: BTreeSet<T::AccountId> = account_staked_sums
			.keys()
			.chain(account_deposited_sums.keys())
			.cloned()
			.collect();
		let mut account_locked_before: BTreeMap<T::AccountId, u64> = BTreeMap::new();
		let mut account_reserved_before: BTreeMap<T::AccountId, u64> = BTreeMap::new();
		let pallet_id = T::PalletId::get();
		let empty_lock =
			BalanceLock { id: pallet_id, amount: Zero::zero(), reasons: Reasons::Misc };
		for account in all_accounts {
			// Question: how does this know where to get locks just from T? what if there were
			// multiple pallet_balance implementations in the runtime?
			let locked = Locks::<T>::get(account.clone())
				.iter()
				// TODO: I think this PalletId needs to be passed as a generic param.
				.find(|l| l.id == T::PalletId::get())
				.unwrap_or(&empty_lock)
				.amount
				.saturated_into::<u64>();
			let reserved = T::Currency::reserved_balance(&account).saturated_into::<u64>();

			// Total locked for each account by this pallet must equal the sum of the amount staked.
			ensure!(locked == account_staked_sums[&account], "account locked != account staked");
			// Total deposited must be less than or equal to the total reserved.
			ensure!(
				account_deposited_sums[&account] <= reserved,
				"account deposited > account reserved"
			);

			// Record the values in the Map
			account_locked_before.insert(account.clone(), locked);
			account_reserved_before.insert(account.clone(), reserved);
		}

		// TODO: print some summary stats

		let pre_migration_data = PreMigrationData::<T> {
			account_staked_sums,
			account_deposited_sums,
			account_locked_before,
			account_reserved_before,
		};
		Ok(pre_migration_data.encode())
	}

	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		log::info!("on_runtime_upgrade");
		todo!()
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(pre_migration_data_bytes: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		let pre_migration_data = PreMigrationData::<T>::decode(&mut &pre_migration_data_bytes[..])
			.map_err(|_| "Failed to decode pre-migration data")?;

		log::info!("{:?}", pre_migration_data.account_staked_sums);
		log::info!("{:?}", pre_migration_data.account_deposited_sums);
		log::info!("{:?}", pre_migration_data.account_locked_before);
		log::info!("{:?}", pre_migration_data.account_reserved_before);
		Ok(())
	}
}
