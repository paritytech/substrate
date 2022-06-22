// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

pub mod meter;

use crate::{
	exec::{AccountIdOf, StorageKey},
	weights::WeightInfo,
	BalanceOf, CodeHash, Config, ContractInfoOf, DeletionQueue, Error, TrieId, SENTINEL,
};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	dispatch::{DispatchError, DispatchResult},
	storage::child::{self, ChildInfo, KillStorageResult},
	weights::Weight,
};
use scale_info::TypeInfo;
use sp_core::crypto::UncheckedFrom;
use sp_io::hashing::blake2_256;
use sp_runtime::{
	traits::{Hash, Zero},
	RuntimeDebug,
};
use sp_std::{marker::PhantomData, prelude::*};

pub type ContractInfo<T> = RawContractInfo<CodeHash<T>, BalanceOf<T>>;

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct RawContractInfo<CodeHash, Balance> {
	/// Unique ID for the subtree encoded as a bytes vector.
	pub trie_id: TrieId,
	/// The code associated with a given account.
	pub code_hash: CodeHash,
	/// The amount of balance that is currently deposited to pay for consumed storage.
	pub storage_deposit: Balance,
}

impl<CodeHash, Balance> RawContractInfo<CodeHash, Balance> {
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

#[derive(Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct DeletedContract {
	pub(crate) trie_id: TrieId,
}

/// Information about what happended to the pre-existing value when calling [`Storage::write`].
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum WriteOutcome {
	/// No value existed at the specified key.
	New,
	/// A value of the returned length was overwritten.
	Overwritten(u32),
	/// The returned value was taken out of storage before being overwritten.
	///
	/// This is only returned when specifically requested because it causes additional work
	/// depending on the size of the pre-existing value. When not requested [`Self::Overwritten`]
	/// is returned instead.
	Taken(Vec<u8>),
}

impl WriteOutcome {
	/// Extracts the size of the overwritten value or `0` if there
	/// was no value in storage.
	pub fn old_len(&self) -> u32 {
		match self {
			Self::New => 0,
			Self::Overwritten(len) => *len,
			Self::Taken(value) => value.len() as u32,
		}
	}

	/// Extracts the size of the overwritten value or `SENTINEL` if there
	/// was no value in storage.
	///
	/// # Note
	///
	/// We cannot use `0` as sentinel value because there could be a zero sized
	/// storage entry which is different from a non existing one.
	pub fn old_len_with_sentinel(&self) -> u32 {
		match self {
			Self::New => SENTINEL,
			Self::Overwritten(len) => *len,
			Self::Taken(value) => value.len() as u32,
		}
	}
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
		child::get_raw(&child_trie_info(trie_id), &blake2_256(key))
	}

	/// Returns `Some(len)` (in bytes) if a storage item exists at `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	pub fn size(trie_id: &TrieId, key: &StorageKey) -> Option<u32> {
		child::len(&child_trie_info(trie_id), &blake2_256(key))
	}

	/// Update a storage entry into a contract's kv storage.
	///
	/// If the `new_value` is `None` then the kv pair is removed. If `take` is true
	/// a [`WriteOutcome::Taken`] is returned instead of a [`WriteOutcome::Overwritten`].
	///
	/// This function also records how much storage was created or removed if a `storage_meter`
	/// is supplied. It should only be absent for testing or benchmarking code.
	pub fn write(
		trie_id: &TrieId,
		key: &StorageKey,
		new_value: Option<Vec<u8>>,
		storage_meter: Option<&mut meter::NestedMeter<T>>,
		take: bool,
	) -> Result<WriteOutcome, DispatchError> {
		let hashed_key = blake2_256(key);
		let child_trie_info = &child_trie_info(trie_id);
		let (old_len, old_value) = if take {
			let val = child::get_raw(child_trie_info, &hashed_key);
			(val.as_ref().map(|v| v.len() as u32), val)
		} else {
			(child::len(child_trie_info, &hashed_key), None)
		};

		if let Some(storage_meter) = storage_meter {
			let mut diff = meter::Diff::default();
			match (old_len, new_value.as_ref().map(|v| v.len() as u32)) {
				(Some(old_len), Some(new_len)) =>
					if new_len > old_len {
						diff.bytes_added = new_len - old_len;
					} else {
						diff.bytes_removed = old_len - new_len;
					},
				(None, Some(new_len)) => {
					diff.bytes_added = new_len;
					diff.items_added = 1;
				},
				(Some(old_len), None) => {
					diff.bytes_removed = old_len;
					diff.items_removed = 1;
				},
				(None, None) => (),
			}
			storage_meter.charge(&diff)?;
		}

		match &new_value {
			Some(new_value) => child::put_raw(child_trie_info, &hashed_key, new_value),
			None => child::kill(child_trie_info, &hashed_key),
		}

		Ok(match (old_len, old_value) {
			(None, _) => WriteOutcome::New,
			(Some(old_len), None) => WriteOutcome::Overwritten(old_len),
			(Some(_), Some(old_value)) => WriteOutcome::Taken(old_value),
		})
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

		let contract =
			ContractInfo::<T> { code_hash: ch, trie_id, storage_deposit: <BalanceOf<T>>::zero() };

		Ok(contract)
	}

	/// Push a contract's trie to the deletion queue for lazy removal.
	///
	/// You must make sure that the contract is also removed when queuing the trie for deletion.
	pub fn queue_trie_for_deletion(contract: &ContractInfo<T>) -> DispatchResult {
		<DeletionQueue<T>>::try_append(DeletedContract { trie_id: contract.trie_id.clone() })
			.map_err(|_| <Error<T>>::DeletionQueueFull.into())
	}

	/// Calculates the weight that is necessary to remove one key from the trie and how many
	/// of those keys can be deleted from the deletion queue given the supplied queue length
	/// and weight limit.
	pub fn deletion_budget(queue_len: usize, weight_limit: Weight) -> (u64, u32) {
		let base_weight = T::WeightInfo::on_process_deletion_queue_batch();
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

		while !queue.is_empty() && remaining_key_budget > 0 {
			// Cannot panic due to loop condition
			let trie = &mut queue[0];
			let outcome =
				child::kill_storage(&child_trie_info(&trie.trie_id), Some(remaining_key_budget));
			let keys_removed = match outcome {
				// This happens when our budget wasn't large enough to remove all keys.
				KillStorageResult::SomeRemaining(count) => count,
				KillStorageResult::AllRemoved(count) => {
					// We do not care to preserve order. The contract is deleted already and
					// no one waits for the trie to be deleted.
					queue.swap_remove(0);
					count
				},
			};
			remaining_key_budget = remaining_key_budget.saturating_sub(keys_removed);
		}

		<DeletionQueue<T>>::put(queue);
		weight_limit.saturating_sub(weight_per_key.saturating_mul(remaining_key_budget as Weight))
	}

	/// Generates a unique trie id by returning  `hash(account_id ++ nonce)`.
	pub fn generate_trie_id(account_id: &AccountIdOf<T>, nonce: u64) -> TrieId {
		let buf: Vec<_> = account_id.as_ref().iter().chain(&nonce.to_le_bytes()).cloned().collect();
		T::Hashing::hash(&buf)
			.as_ref()
			.to_vec()
			.try_into()
			.expect("Runtime uses a reasonable hash size. Hence sizeof(T::Hash) <= 128; qed")
	}

	/// Returns the code hash of the contract specified by `account` ID.
	#[cfg(test)]
	pub fn code_hash(account: &AccountIdOf<T>) -> Option<CodeHash<T>> {
		<ContractInfoOf<T>>::get(account).map(|i| i.code_hash)
	}

	/// Fill up the queue in order to exercise the limits during testing.
	#[cfg(test)]
	pub fn fill_queue_with_dummies() {
		use frame_support::{traits::Get, BoundedVec};
		let queue: Vec<DeletedContract> = (0..T::DeletionQueueDepth::get())
			.map(|_| DeletedContract { trie_id: TrieId::default() })
			.collect();
		let bounded: BoundedVec<_, _> = queue.try_into().unwrap();
		<DeletionQueue<T>>::put(bounded);
	}
}
