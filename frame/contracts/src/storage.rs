// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! This module contains routines for accessing and altering a contract related state.

use crate::{
	exec::{AccountIdOf, StorageKey},
	weights::WeightInfo,
	CodeHash, Config, ContractInfoOf, DeletionQueue, Error, TrieId,
};
use codec::{Decode, Encode};
use frame_support::{
	dispatch::{DispatchError, DispatchResult},
	storage::child::{self, ChildInfo, KillStorageResult},
	traits::Get,
	weights::Weight,
};
use sp_core::crypto::UncheckedFrom;
use sp_io::hashing::blake2_256;
use sp_runtime::{traits::Hash, RuntimeDebug};
use sp_std::{marker::PhantomData, prelude::*};

pub type ContractInfo<T> = RawContractInfo<CodeHash<T>>;

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct RawContractInfo<CodeHash> {
	/// Unique ID for the subtree encoded as a bytes vector.
	pub trie_id: TrieId,
	/// The code associated with a given account.
	pub code_hash: CodeHash,
	/// This field is reserved for future evolution of format.
	pub _reserved: Option<()>,
}

impl<CodeHash> RawContractInfo<CodeHash> {
	/// Associated child trie unique id is built from the hash part of the trie id.
	#[cfg(test)]
	pub fn child_trie_info(&self) -> ChildInfo {
		child_trie_info(&self.trie_id[..])
	}
}

/// Associated child trie unique id is built from the hash part of the trie id.
fn child_trie_info(trie_id: &[u8]) -> ChildInfo {
	ChildInfo::new_default(trie_id)
}

#[derive(Encode, Decode)]
pub struct DeletedContract {
	pub(crate) trie_id: TrieId,
}

pub struct Storage<T>(PhantomData<T>);

impl<T> Storage<T>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	/// Reads a storage kv pair of a contract.
	///
	/// The read is performed from the `trie_id` only. The `address` is not necessary. If the
	/// contract doesn't store under the given `key` `None` is returned.
	pub fn read(trie_id: &TrieId, key: &StorageKey) -> Option<Vec<u8>> {
		child::get_raw(&child_trie_info(&trie_id), &blake2_256(key))
	}

	/// Update a storage entry into a contract's kv storage.
	///
	/// If the `opt_new_value` is `None` then the kv pair is removed.
	///
	/// This function also updates the bookkeeping info such as: number of total non-empty pairs a
	/// contract owns, the last block the storage was written to, etc. That's why, in contrast to
	/// `read`, this function also requires the `account` ID.
	pub fn write(
		new_info: &mut ContractInfo<T>,
		key: &StorageKey,
		opt_new_value: Option<Vec<u8>>,
	) -> DispatchResult {
		let hashed_key = blake2_256(key);
		let child_trie_info = &child_trie_info(&new_info.trie_id);

		match opt_new_value {
			Some(new_value) => child::put_raw(&child_trie_info, &hashed_key, &new_value[..]),
			None => child::kill(&child_trie_info, &hashed_key),
		}

		Ok(())
	}

	/// Creates a new contract descriptor in the storage with the given code hash at the given
	/// address.
	///
	/// Returns `Err` if there is already a contract at the given address.
	pub fn new_contract(
		account: &AccountIdOf<T>,
		trie_id: TrieId,
		ch: CodeHash<T>,
	) -> Result<ContractInfo<T>, DispatchError> {
		if <ContractInfoOf<T>>::contains_key(account) {
			return Err(Error::<T>::DuplicateContract.into())
		}

		let contract = ContractInfo::<T> { code_hash: ch, trie_id, _reserved: None };

		Ok(contract)
	}

	/// Push a contract's trie to the deletion queue for lazy removal.
	///
	/// You must make sure that the contract is also removed when queuing the trie for deletion.
	pub fn queue_trie_for_deletion(contract: &ContractInfo<T>) -> DispatchResult {
		if <DeletionQueue<T>>::decode_len().unwrap_or(0) >= T::DeletionQueueDepth::get() as usize {
			Err(Error::<T>::DeletionQueueFull.into())
		} else {
			<DeletionQueue<T>>::append(DeletedContract { trie_id: contract.trie_id.clone() });
			Ok(())
		}
	}

	/// Calculates the weight that is necessary to remove one key from the trie and how many
	/// of those keys can be deleted from the deletion queue given the supplied queue length
	/// and weight limit.
	pub fn deletion_budget(queue_len: usize, weight_limit: Weight) -> (u64, u32) {
		let base_weight = T::WeightInfo::on_initialize();
		let weight_per_queue_item = T::WeightInfo::on_initialize_per_queue_item(1) -
			T::WeightInfo::on_initialize_per_queue_item(0);
		let weight_per_key = T::WeightInfo::on_initialize_per_trie_key(1) -
			T::WeightInfo::on_initialize_per_trie_key(0);
		let decoding_weight = weight_per_queue_item.saturating_mul(queue_len as Weight);

		// `weight_per_key` being zero makes no sense and would constitute a failure to
		// benchmark properly. We opt for not removing any keys at all in this case.
		let key_budget = weight_limit
			.saturating_sub(base_weight)
			.saturating_sub(decoding_weight)
			.checked_div(weight_per_key)
			.unwrap_or(0) as u32;

		(weight_per_key, key_budget)
	}

	/// Delete as many items from the deletion queue possible within the supplied weight limit.
	///
	/// It returns the amount of weight used for that task.
	pub fn process_deletion_queue_batch(weight_limit: Weight) -> Weight {
		let queue_len = <DeletionQueue<T>>::decode_len().unwrap_or(0);
		if queue_len == 0 {
			return 0
		}

		let (weight_per_key, mut remaining_key_budget) =
			Self::deletion_budget(queue_len, weight_limit);

		// We want to check whether we have enough weight to decode the queue before
		// proceeding. Too little weight for decoding might happen during runtime upgrades
		// which consume the whole block before the other `on_initialize` blocks are called.
		if remaining_key_budget == 0 {
			return weight_limit
		}

		let mut queue = <DeletionQueue<T>>::get();

		if let (Some(trie), true) = (queue.get(0), remaining_key_budget > 0) {
			let outcome =
				child::kill_storage(&child_trie_info(&trie.trie_id), Some(remaining_key_budget));
			let keys_removed = match outcome {
				// This should not happen as our budget was large enough to remove all keys.
				KillStorageResult::SomeRemaining(count) => count,
				KillStorageResult::AllRemoved(count) => {
					// We do not care to preserve order. The contract is deleted already and
					// noone waits for the trie to be deleted.
					queue.swap_remove(0);
					count
				},
			};
			remaining_key_budget = remaining_key_budget.saturating_sub(keys_removed);
		}

		<DeletionQueue<T>>::put(queue);
		weight_limit.saturating_sub(weight_per_key.saturating_mul(remaining_key_budget as Weight))
	}

	/// This generator uses inner counter for account id and applies the hash over `AccountId +
	/// accountid_counter`.
	pub fn generate_trie_id(account_id: &AccountIdOf<T>, seed: u64) -> TrieId {
		let buf: Vec<_> = account_id.as_ref().iter().chain(&seed.to_le_bytes()).cloned().collect();
		T::Hashing::hash(&buf).as_ref().into()
	}

	/// Returns the code hash of the contract specified by `account` ID.
	#[cfg(test)]
	pub fn code_hash(account: &AccountIdOf<T>) -> Option<CodeHash<T>> {
		<ContractInfoOf<T>>::get(account).map(|i| i.code_hash)
	}

	/// Fill up the queue in order to exercise the limits during testing.
	#[cfg(test)]
	pub fn fill_queue_with_dummies() {
		let queue: Vec<_> = (0..T::DeletionQueueDepth::get())
			.map(|_| DeletedContract { trie_id: vec![] })
			.collect();
		<DeletionQueue<T>>::put(queue);
	}
}
