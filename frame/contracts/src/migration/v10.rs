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

//! Update `CodeStorage` with the new `determinism` field.

use core::cmp::{max, min};

use crate::{
	address::AddressGenerator,
	exec::AccountIdOf,
	migration::{IsFinished, Migrate},
	BalanceOf, CodeHash, Config, Pallet, TrieId, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage_alias,
	traits::{
		tokens::{Fortitude::Polite, Preservation::Preserve},
		Currency, ExistenceRequirement, ReservableCurrency,
	},
	DefaultNoBound,
};

use frame_support::traits::fungible::Inspect;
use sp_runtime::{Perbill, Saturating};
use sp_std::{marker::PhantomData, ops::Deref};
mod old {
	use super::*;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[scale_info(skip_type_params(T))]
	pub struct ContractInfo<T: Config> {
		pub trie_id: TrieId,
		pub code_hash: CodeHash<T>,
		pub storage_bytes: u32,
		pub storage_items: u32,
		pub storage_byte_deposit: BalanceOf<T>,
		pub storage_item_deposit: BalanceOf<T>,
		pub storage_base_deposit: BalanceOf<T>,
	}

	#[storage_alias]
	pub type ContractInfoOf<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		ContractInfo<T>,
	>;
}

#[cfg(feature = "runtime-benchmarks")]
pub fn store_old_contrat_info<T: Config>(account: T::AccountId, info: crate::ContractInfo<T>) {
	let info = old::ContractInfo {
		trie_id: info.trie_id,
		code_hash: info.code_hash,
		storage_bytes: Default::default(),
		storage_items: Default::default(),
		storage_byte_deposit: Default::default(),
		storage_item_deposit: Default::default(),
		storage_base_deposit: Default::default(),
	};
	old::ContractInfoOf::<T>::insert(account, info);
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
#[scale_info(skip_type_params(T))]
pub struct ContractInfo<T: Config> {
	pub trie_id: TrieId,
	deposit_account: DepositAccount<T>,
	pub code_hash: CodeHash<T>,
	storage_bytes: u32,
	storage_items: u32,
	pub storage_byte_deposit: BalanceOf<T>,
	storage_item_deposit: BalanceOf<T>,
	storage_base_deposit: BalanceOf<T>,
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	last_key: Option<BoundedVec<u8, ConstU32<256>>>,
	_phantom: PhantomData<T>,
}

#[storage_alias]
type ContractInfoOf<T: Config> =
	StorageMap<Pallet<T>, Twox64Concat, <T as frame_system::Config>::AccountId, ContractInfo<T>>;

impl<T: Config> Migrate for Migration<T> {
	const VERSION: u16 = 10;

	fn max_step_weight() -> Weight {
		Weight::zero() // TODO fix
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_key) = self.last_key.take() {
			old::ContractInfoOf::<T>::iter_from(last_key.to_vec())
		} else {
			old::ContractInfoOf::<T>::iter()
		};

		if let Some((account, contract)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating contract info for account {:?}", account);
			let min_balance = Pallet::<T>::min_balance();

			// Store last key for next migration step
			self.last_key = Some(iter.last_raw_key().to_vec().try_into().unwrap());

			// Get the new deposit account address
			let deposit_account: DepositAccount<T> =
				DepositAccount(T::AddressGenerator::deposit_address(&account));

			// Calculate the existing deposit, that should be reserved on the contract account
			let old_deposit = contract
				.storage_byte_deposit
				.saturating_add(contract.storage_item_deposit)
				.saturating_add(contract.storage_base_deposit);

			// Unreserve the existing deposit, so we can transfer it to the deposit account.
			// Note we can't use repatriate_reserve, because it only works with existing accounts
			T::Currency::unreserve(&account, old_deposit);

			// Attempt to transfer it to the deposit account.
			let new_deposit = T::Currency::transfer(
				&account,
				&deposit_account,
				old_deposit,
				ExistenceRequirement::KeepAlive,
			)
			.map(|_| old_deposit)
			// If it fails, we try to transfer the account reducible balance instead.
			.or_else(|_| {
				log::error!(
					target: LOG_TARGET,
					"Failed to transfer deposit for account {:?}",
					account
				);
				let deposit = T::Currency::reducible_balance(&account, Preserve, Polite);
				T::Currency::transfer(
					&account,
					&deposit_account,
					T::Currency::reducible_balance(&account, Preserve, Polite),
					ExistenceRequirement::KeepAlive,
				)
				.map(|_| deposit)
			})
			// If it fails we fallback to minting the ED.
			.unwrap_or_else(|_| {
				log::error!(target: LOG_TARGET, "Failed to transfer ED for account {:?}", account);
				T::Currency::deposit_creating(&deposit_account, min_balance);
				min_balance
			});

			// Calculate the new base_deposit
			let new_base_deposit = min(
				max(contract.storage_base_deposit, min_balance.saturating_add(min_balance)),
				new_deposit,
			);

			let new_deposit_without_base = new_deposit.saturating_sub(new_base_deposit);
			let old_deposit_without_base =
				old_deposit.saturating_sub(contract.storage_base_deposit);
			let ratio = Perbill::from_rational(new_deposit_without_base, old_deposit_without_base);

			let new_contract_info = ContractInfo {
				trie_id: contract.trie_id,
				deposit_account,
				code_hash: contract.code_hash,
				storage_bytes: contract.storage_bytes,
				storage_items: contract.storage_items,
				storage_byte_deposit: ratio.mul_ceil(contract.storage_byte_deposit),
				storage_item_deposit: ratio.mul_ceil(contract.storage_item_deposit),
				storage_base_deposit: new_base_deposit,
			};
			ContractInfoOf::<T>::insert(&account, new_contract_info);

			(IsFinished::No, Weight::zero())
		} else {
			log::debug!(target: LOG_TARGET, "Done Migrating contract info");
			(IsFinished::Yes, Weight::zero())
		}
	}
}
