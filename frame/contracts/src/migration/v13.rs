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

//! Add `delegate_dependencies` to `ContractInfo`.
//! See <https://github.com/paritytech/substrate/pull/14079>.

use crate::{
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	AccountIdOf, BalanceOf, CodeHash, Config, Pallet, TrieId, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use frame_support::{pallet_prelude::*, storage_alias, DefaultNoBound};
use sp_runtime::BoundedBTreeMap;
use sp_std::prelude::*;

mod old {
	use super::*;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[scale_info(skip_type_params(T))]
	pub struct ContractInfo<T: Config> {
		pub trie_id: TrieId,
		pub deposit_account: AccountIdOf<T>,
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
pub fn store_old_contract_info<T: Config>(account: T::AccountId, info: crate::ContractInfo<T>) {
	use sp_runtime::traits::{Hash, TrailingZeroInput};
	let entropy = (b"contract_depo_v1", account.clone()).using_encoded(T::Hashing::hash);
	let deposit_account = Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
		.expect("infinite length input; no invalid inputs for type; qed");
	let info = old::ContractInfo {
		trie_id: info.trie_id.clone(),
		deposit_account,
		code_hash: info.code_hash,
		storage_bytes: Default::default(),
		storage_items: Default::default(),
		storage_byte_deposit: Default::default(),
		storage_item_deposit: Default::default(),
		storage_base_deposit: Default::default(),
	};
	old::ContractInfoOf::<T>::insert(account, info);
}

#[storage_alias]
pub type ContractInfoOf<T: Config> =
	StorageMap<Pallet<T>, Twox64Concat, <T as frame_system::Config>::AccountId, ContractInfo<T>>;

#[derive(Encode, Decode, CloneNoBound, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct ContractInfo<T: Config> {
	trie_id: TrieId,
	deposit_account: AccountIdOf<T>,
	code_hash: CodeHash<T>,
	storage_bytes: u32,
	storage_items: u32,
	storage_byte_deposit: BalanceOf<T>,
	storage_item_deposit: BalanceOf<T>,
	storage_base_deposit: BalanceOf<T>,
	delegate_dependencies: BoundedBTreeMap<CodeHash<T>, BalanceOf<T>, T::MaxDelegateDependencies>,
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	last_account: Option<T::AccountId>,
}

impl<T: Config> MigrationStep for Migration<T> {
	const VERSION: u16 = 13;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v13_migration_step()
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_account) = self.last_account.take() {
			old::ContractInfoOf::<T>::iter_from(old::ContractInfoOf::<T>::hashed_key_for(
				last_account,
			))
		} else {
			old::ContractInfoOf::<T>::iter()
		};

		if let Some((key, old)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating contract {:?}", key);
			let info = ContractInfo {
				trie_id: old.trie_id,
				deposit_account: old.deposit_account,
				code_hash: old.code_hash,
				storage_bytes: old.storage_bytes,
				storage_items: old.storage_items,
				storage_byte_deposit: old.storage_byte_deposit,
				storage_item_deposit: old.storage_item_deposit,
				storage_base_deposit: old.storage_base_deposit,
				delegate_dependencies: Default::default(),
			};
			ContractInfoOf::<T>::insert(key.clone(), info);
			self.last_account = Some(key);
			(IsFinished::No, T::WeightInfo::v13_migration_step())
		} else {
			log::debug!(target: LOG_TARGET, "No more contracts to migrate");
			(IsFinished::Yes, T::WeightInfo::v13_migration_step())
		}
	}
}
