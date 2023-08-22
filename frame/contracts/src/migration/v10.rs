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

//! Don't rely on reserved balances keeping an account alive
//! See <https://github.com/paritytech/substrate/pull/13369>.

use crate::{
	exec::AccountIdOf,
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	CodeHash, Config, Pallet, TrieId, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use core::cmp::{max, min};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage_alias,
	traits::{
		tokens::{fungible::Inspect, Fortitude::Polite, Preservation::Preserve},
		ExistenceRequirement, ReservableCurrency,
	},
	DefaultNoBound,
};
use sp_core::hexdisplay::HexDisplay;
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_runtime::{
	traits::{Hash, TrailingZeroInput, Zero},
	Perbill, Saturating,
};
use sp_std::{ops::Deref, prelude::*};

mod old {
	use super::*;

	pub type BalanceOf<T, OldCurrency> = <OldCurrency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[scale_info(skip_type_params(T, OldCurrency))]
	pub struct ContractInfo<T: Config, OldCurrency>
	where
		OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	{
		pub trie_id: TrieId,
		pub code_hash: CodeHash<T>,
		pub storage_bytes: u32,
		pub storage_items: u32,
		pub storage_byte_deposit: BalanceOf<T, OldCurrency>,
		pub storage_item_deposit: BalanceOf<T, OldCurrency>,
		pub storage_base_deposit: BalanceOf<T, OldCurrency>,
	}

	#[storage_alias]
	pub type ContractInfoOf<T: Config, OldCurrency> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		ContractInfo<T, OldCurrency>,
	>;
}

#[cfg(feature = "runtime-benchmarks")]
pub fn store_old_contract_info<T: Config, OldCurrency>(
	account: T::AccountId,
	info: crate::ContractInfo<T>,
) where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId> + 'static,
{
	let info = old::ContractInfo {
		trie_id: info.trie_id,
		code_hash: info.code_hash,
		storage_bytes: Default::default(),
		storage_items: Default::default(),
		storage_byte_deposit: Default::default(),
		storage_item_deposit: Default::default(),
		storage_base_deposit: Default::default(),
	};
	old::ContractInfoOf::<T, OldCurrency>::insert(account, info);
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebugNoBound, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct DepositAccount<T: Config>(AccountIdOf<T>);

impl<T: Config> Deref for DepositAccount<T> {
	type Target = AccountIdOf<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T, OldCurrency))]
pub struct ContractInfo<T: Config, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
{
	pub trie_id: TrieId,
	deposit_account: DepositAccount<T>,
	pub code_hash: CodeHash<T>,
	storage_bytes: u32,
	storage_items: u32,
	pub storage_byte_deposit: old::BalanceOf<T, OldCurrency>,
	storage_item_deposit: old::BalanceOf<T, OldCurrency>,
	storage_base_deposit: old::BalanceOf<T, OldCurrency>,
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config, OldCurrency = ()> {
	last_account: Option<T::AccountId>,
	_phantom: PhantomData<(T, OldCurrency)>,
}

#[storage_alias]
type ContractInfoOf<T: Config, OldCurrency> = StorageMap<
	Pallet<T>,
	Twox64Concat,
	<T as frame_system::Config>::AccountId,
	ContractInfo<T, OldCurrency>,
>;

/// Formula: `hash("contract_depo_v1" ++ contract_addr)`
fn deposit_address<T: Config>(
	contract_addr: &<T as frame_system::Config>::AccountId,
) -> <T as frame_system::Config>::AccountId {
	let entropy = (b"contract_depo_v1", contract_addr)
		.using_encoded(<T as frame_system::Config>::Hashing::hash);
	Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
		.expect("infinite length input; no invalid inputs for type; qed")
}

impl<T: Config, OldCurrency: 'static> MigrationStep for Migration<T, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>
		+ Inspect<<T as frame_system::Config>::AccountId, Balance = old::BalanceOf<T, OldCurrency>>,
{
	const VERSION: u16 = 10;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v10_migration_step()
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_account) = self.last_account.take() {
			old::ContractInfoOf::<T, OldCurrency>::iter_from(
				old::ContractInfoOf::<T, OldCurrency>::hashed_key_for(last_account),
			)
		} else {
			old::ContractInfoOf::<T, OldCurrency>::iter()
		};

		if let Some((account, contract)) = iter.next() {
			let min_balance = <OldCurrency as frame_support::traits::Currency<
				<T as frame_system::Config>::AccountId,
			>>::minimum_balance();
			log::debug!(target: LOG_TARGET, "Account: 0x{} ", HexDisplay::from(&account.encode()));

			// Get the new deposit account address
			let deposit_account: DepositAccount<T> = DepositAccount(deposit_address::<T>(&account));

			// Calculate the existing deposit, that should be reserved on the contract account
			let old_deposit = contract
				.storage_base_deposit
				.saturating_add(contract.storage_item_deposit)
				.saturating_add(contract.storage_byte_deposit);

			// Unreserve the existing deposit
			// Note we can't use repatriate_reserve, because it only works with existing accounts
			let remaining = OldCurrency::unreserve(&account, old_deposit);
			if !remaining.is_zero() {
				log::warn!(
					target: LOG_TARGET,
					"Partially unreserved. Remaining {:?} out of {:?} asked",
					remaining,
					old_deposit
				);
			}

			// Attempt to transfer the old deposit to the deposit account.
			let amount = old_deposit
				.saturating_sub(min_balance)
				.min(OldCurrency::reducible_balance(&account, Preserve, Polite));

			let new_deposit = OldCurrency::transfer(
				&account,
				&deposit_account,
				amount,
				ExistenceRequirement::KeepAlive,
			)
			.map(|_| {
				log::debug!(
					target: LOG_TARGET,
					"Transferred deposit ({:?}) to deposit account",
					amount
				);
				amount
			})
			// If it fails we fallback to minting the ED.
			.unwrap_or_else(|err| {
				log::error!(
					target: LOG_TARGET,
					"Failed to transfer the base deposit, reason: {:?}",
					err
				);
				OldCurrency::deposit_creating(&deposit_account, min_balance);
				min_balance
			});

			// Calculate the new base_deposit to store in the contract:
			// Ideally, it should be the same as the old one
			// Ideally, it should be at least 2xED (for the contract and deposit accounts).
			// It can't be more than the `new_deposit`.
			let new_base_deposit = min(
				max(contract.storage_base_deposit, min_balance.saturating_add(min_balance)),
				new_deposit,
			);

			// Calculate the ratio to adjust storage_byte and storage_item deposits.
			let new_deposit_without_base = new_deposit.saturating_sub(new_base_deposit);
			let old_deposit_without_base =
				old_deposit.saturating_sub(contract.storage_base_deposit);
			let ratio = Perbill::from_rational(new_deposit_without_base, old_deposit_without_base);

			// Calculate the new storage deposits based on the ratio
			let storage_byte_deposit = ratio.mul_ceil(contract.storage_byte_deposit);
			let storage_item_deposit = ratio.mul_ceil(contract.storage_item_deposit);

			// Recalculate the new base deposit, instead of using new_base_deposit to avoid rounding
			// errors
			let storage_base_deposit = new_deposit
				.saturating_sub(storage_byte_deposit)
				.saturating_sub(storage_item_deposit);

			let new_contract_info = ContractInfo {
				trie_id: contract.trie_id,
				deposit_account,
				code_hash: contract.code_hash,
				storage_bytes: contract.storage_bytes,
				storage_items: contract.storage_items,
				storage_byte_deposit,
				storage_item_deposit,
				storage_base_deposit,
			};

			ContractInfoOf::<T, OldCurrency>::insert(&account, new_contract_info);

			// Store last key for next migration step
			self.last_account = Some(account);

			(IsFinished::No, T::WeightInfo::v10_migration_step())
		} else {
			log::debug!(target: LOG_TARGET, "Done Migrating contract info");
			(IsFinished::Yes, T::WeightInfo::v10_migration_step())
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let sample: Vec<_> = old::ContractInfoOf::<T, OldCurrency>::iter().take(10).collect();

		log::debug!(target: LOG_TARGET, "Taking sample of {} contracts", sample.len());
		Ok(sample.encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let sample = <Vec<(T::AccountId, old::ContractInfo<T, OldCurrency>)> as Decode>::decode(
			&mut &state[..],
		)
		.expect("pre_upgrade_step provides a valid state; qed");

		log::debug!(target: LOG_TARGET, "Validating sample of {} contracts", sample.len());
		for (account, old_contract) in sample {
			log::debug!(target: LOG_TARGET, "===");
			log::debug!(target: LOG_TARGET, "Account: 0x{} ", HexDisplay::from(&account.encode()));
			let contract = ContractInfoOf::<T, OldCurrency>::get(&account).unwrap();
			ensure!(old_contract.trie_id == contract.trie_id, "invalid trie_id");
			ensure!(old_contract.code_hash == contract.code_hash, "invalid code_hash");
			ensure!(old_contract.storage_bytes == contract.storage_bytes, "invalid storage_bytes");
			ensure!(old_contract.storage_items == contract.storage_items, "invalid storage_items");

			let deposit = <OldCurrency as frame_support::traits::Currency<_>>::total_balance(
				&contract.deposit_account,
			);
			ensure!(
				deposit ==
					contract
						.storage_base_deposit
						.saturating_add(contract.storage_item_deposit)
						.saturating_add(contract.storage_byte_deposit),
				"deposit mismatch"
			);
		}

		Ok(())
	}
}
