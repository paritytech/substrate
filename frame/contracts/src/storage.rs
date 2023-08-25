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

//! This module contains routines for accessing and altering a contract related state.

pub mod meter;

use crate::{
	exec::{AccountIdOf, Key},
	weights::WeightInfo,
	BalanceOf, CodeHash, CodeInfo, Config, ContractInfoOf, DeletionQueue, DeletionQueueCounter,
	Error, Pallet, TrieId, SENTINEL,
};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	storage::child::{self, ChildInfo},
	weights::Weight,
	CloneNoBound, DefaultNoBound,
};
use scale_info::TypeInfo;
use sp_core::Get;
use sp_io::KillStorageResult;
use sp_runtime::{
	traits::{Hash, Saturating, Zero},
	BoundedBTreeMap, DispatchError, DispatchResult, RuntimeDebug,
};
use sp_std::{marker::PhantomData, prelude::*};

use self::meter::Diff;

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account.
#[derive(Encode, Decode, CloneNoBound, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct ContractInfo<T: Config> {
	/// Unique ID for the subtree encoded as a bytes vector.
	pub trie_id: TrieId,
	/// The code associated with a given account.
	pub code_hash: CodeHash<T>,
	/// How many bytes of storage are accumulated in this contract's child trie.
	storage_bytes: u32,
	/// How many items of storage are accumulated in this contract's child trie.
	storage_items: u32,
	/// This records to how much deposit the accumulated `storage_bytes` amount to.
	pub storage_byte_deposit: BalanceOf<T>,
	/// This records to how much deposit the accumulated `storage_items` amount to.
	storage_item_deposit: BalanceOf<T>,
	/// This records how much deposit is put down in order to pay for the contract itself.
	///
	/// We need to store this information separately so it is not used when calculating any refunds
	/// since the base deposit can only ever be refunded on contract termination.
	storage_base_deposit: BalanceOf<T>,
	/// Map of code hashes and deposit balances.
	///
	/// Tracks the code hash and deposit held for adding delegate dependencies. Dependencies added
	/// to the map can not be removed from the chain state and can be safely used for delegate
	/// calls.
	delegate_dependencies: BoundedBTreeMap<CodeHash<T>, BalanceOf<T>, T::MaxDelegateDependencies>,
}

impl<T: Config> ContractInfo<T> {
	/// Constructs a new contract info **without** writing it to storage.
	///
	/// This returns an `Err` if an contract with the supplied `account` already exists
	/// in storage.
	pub fn new(
		account: &AccountIdOf<T>,
		nonce: u64,
		code_hash: CodeHash<T>,
	) -> Result<Self, DispatchError> {
		if <ContractInfoOf<T>>::contains_key(account) {
			return Err(Error::<T>::DuplicateContract.into())
		}

		let trie_id = {
			let buf = (account, nonce).using_encoded(T::Hashing::hash);
			buf.as_ref()
				.to_vec()
				.try_into()
				.expect("Runtime uses a reasonable hash size. Hence sizeof(T::Hash) <= 128; qed")
		};

		let contract = Self {
			trie_id,
			code_hash,
			storage_bytes: 0,
			storage_items: 0,
			storage_byte_deposit: Zero::zero(),
			storage_item_deposit: Zero::zero(),
			storage_base_deposit: Zero::zero(),
			delegate_dependencies: Default::default(),
		};

		Ok(contract)
	}

	/// Associated child trie unique id is built from the hash part of the trie id.
	pub fn child_trie_info(&self) -> ChildInfo {
		ChildInfo::new_default(self.trie_id.as_ref())
	}

	/// The deposit paying for the accumulated storage generated within the contract's child trie.
	pub fn extra_deposit(&self) -> BalanceOf<T> {
		self.storage_byte_deposit.saturating_add(self.storage_item_deposit)
	}

	/// Same as [`Self::extra_deposit`] but including the base deposit.
	pub fn total_deposit(&self) -> BalanceOf<T> {
		self.extra_deposit()
			.saturating_add(self.storage_base_deposit)
			.saturating_sub(Pallet::<T>::min_balance())
	}

	/// Returns the storage base deposit of the contract.
	pub fn storage_base_deposit(&self) -> BalanceOf<T> {
		self.storage_base_deposit
	}

	/// Reads a storage kv pair of a contract.
	///
	/// The read is performed from the `trie_id` only. The `address` is not necessary. If the
	/// contract doesn't store under the given `key` `None` is returned.
	pub fn read(&self, key: &Key<T>) -> Option<Vec<u8>> {
		child::get_raw(&self.child_trie_info(), key.hash().as_slice())
	}

	/// Returns `Some(len)` (in bytes) if a storage item exists at `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	pub fn size(&self, key: &Key<T>) -> Option<u32> {
		child::len(&self.child_trie_info(), key.hash().as_slice())
	}

	/// Update a storage entry into a contract's kv storage.
	///
	/// If the `new_value` is `None` then the kv pair is removed. If `take` is true
	/// a [`WriteOutcome::Taken`] is returned instead of a [`WriteOutcome::Overwritten`].
	///
	/// This function also records how much storage was created or removed if a `storage_meter`
	/// is supplied. It should only be absent for testing or benchmarking code.
	pub fn write(
		&self,
		key: &Key<T>,
		new_value: Option<Vec<u8>>,
		storage_meter: Option<&mut meter::NestedMeter<T>>,
		take: bool,
	) -> Result<WriteOutcome, DispatchError> {
		let child_trie_info = &self.child_trie_info();
		let hashed_key = key.hash();
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
			storage_meter.charge(&diff);
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

	/// Sets and returns the contract base deposit.
	///
	/// The base deposit is updated when the `code_hash` of the contract changes, as it depends on
	/// the deposit paid to upload the contract's code.
	pub fn update_base_deposit(&mut self, code_info: &CodeInfo<T>) -> BalanceOf<T> {
		let ed = Pallet::<T>::min_balance();
		let info_deposit =
			Diff { bytes_added: self.encoded_size() as u32, items_added: 1, ..Default::default() }
				.update_contract::<T>(None)
				.charge_or_zero();

		// Instantiating the contract prevents its code to be deleted, therefore the base deposit
		// includes a fraction (`T::CodeHashLockupDepositPercent`) of the original storage deposit
		// to prevent abuse.
		let upload_deposit = T::CodeHashLockupDepositPercent::get().mul_ceil(code_info.deposit());

		// Instantiate needs to transfer at least the minimum balance in order to pull the
		// contract's own account into existence, as the deposit itself does not contribute to the
		// `ed`.
		let deposit = info_deposit.saturating_add(upload_deposit).saturating_add(ed);

		self.storage_base_deposit = deposit;
		deposit
	}

	/// Adds a new delegate dependency to the contract.
	/// The `amount` is the amount of funds that will be reserved for the dependency.
	///
	/// Returns an error if the maximum number of delegate_dependencies is reached or if
	/// the delegate dependency already exists.
	pub fn add_delegate_dependency(
		&mut self,
		code_hash: CodeHash<T>,
		amount: BalanceOf<T>,
	) -> DispatchResult {
		self.delegate_dependencies
			.try_insert(code_hash, amount)
			.map_err(|_| Error::<T>::MaxDelegateDependenciesReached)?
			.map_or(Ok(()), |_| Err(Error::<T>::DelegateDependencyAlreadyExists))
			.map_err(Into::into)
	}

	/// Removes the delegate dependency from the contract and returns the deposit held for this
	/// dependency.
	///
	/// Returns an error if the entry doesn't exist.
	pub fn remove_delegate_dependency(
		&mut self,
		code_hash: &CodeHash<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		self.delegate_dependencies
			.remove(code_hash)
			.ok_or(Error::<T>::DelegateDependencyNotFound.into())
	}

	/// Returns the delegate_dependencies of the contract.
	pub fn delegate_dependencies(
		&self,
	) -> &BoundedBTreeMap<CodeHash<T>, BalanceOf<T>, T::MaxDelegateDependencies> {
		&self.delegate_dependencies
	}

	/// Push a contract's trie to the deletion queue for lazy removal.
	///
	/// You must make sure that the contract is also removed when queuing the trie for deletion.
	pub fn queue_trie_for_deletion(&self) {
		DeletionQueueManager::<T>::load().insert(self.trie_id.clone());
	}

	/// Calculates the weight that is necessary to remove one key from the trie and how many
	/// of those keys can be deleted from the deletion queue given the supplied weight limit.
	pub fn deletion_budget(weight_limit: Weight) -> (Weight, u32) {
		let base_weight = T::WeightInfo::on_process_deletion_queue_batch();
		let weight_per_key = T::WeightInfo::on_initialize_per_trie_key(1) -
			T::WeightInfo::on_initialize_per_trie_key(0);

		// `weight_per_key` being zero makes no sense and would constitute a failure to
		// benchmark properly. We opt for not removing any keys at all in this case.
		let key_budget = weight_limit
			.saturating_sub(base_weight)
			.checked_div_per_component(&weight_per_key)
			.unwrap_or(0) as u32;

		(weight_per_key, key_budget)
	}

	/// Delete as many items from the deletion queue possible within the supplied weight limit.
	///
	/// It returns the amount of weight used for that task.
	pub fn process_deletion_queue_batch(weight_limit: Weight) -> Weight {
		let mut queue = <DeletionQueueManager<T>>::load();

		if queue.is_empty() {
			return Weight::zero()
		}

		let (weight_per_key, mut remaining_key_budget) = Self::deletion_budget(weight_limit);

		// We want to check whether we have enough weight to decode the queue before
		// proceeding. Too little weight for decoding might happen during runtime upgrades
		// which consume the whole block before the other `on_initialize` blocks are called.
		if remaining_key_budget == 0 {
			return weight_limit
		}

		while remaining_key_budget > 0 {
			let Some(entry) = queue.next() else { break };

			#[allow(deprecated)]
			let outcome = child::kill_storage(
				&ChildInfo::new_default(&entry.trie_id),
				Some(remaining_key_budget),
			);

			match outcome {
				// This happens when our budget wasn't large enough to remove all keys.
				KillStorageResult::SomeRemaining(_) => return weight_limit,
				KillStorageResult::AllRemoved(keys_removed) => {
					entry.remove();
					remaining_key_budget = remaining_key_budget.saturating_sub(keys_removed);
				},
			};
		}

		weight_limit.saturating_sub(weight_per_key.saturating_mul(u64::from(remaining_key_budget)))
	}

	/// Returns the code hash of the contract specified by `account` ID.
	pub fn load_code_hash(account: &AccountIdOf<T>) -> Option<CodeHash<T>> {
		<ContractInfoOf<T>>::get(account).map(|i| i.code_hash)
	}
}

/// Information about what happened to the pre-existing value when calling [`ContractInfo::write`].
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

/// Manage the removal of contracts storage that are marked for deletion.
///
/// When a contract is deleted by calling `seal_terminate` it becomes inaccessible
/// immediately, but the deletion of the storage items it has accumulated is performed
/// later by pulling the contract from the queue in the `on_idle` hook.
#[derive(Encode, Decode, TypeInfo, MaxEncodedLen, DefaultNoBound, Clone)]
#[scale_info(skip_type_params(T))]
pub struct DeletionQueueManager<T: Config> {
	/// Counter used as a key for inserting a new deleted contract in the queue.
	/// The counter is incremented after each insertion.
	insert_counter: u32,
	/// The index used to read the next element to be deleted in the queue.
	/// The counter is incremented after each deletion.
	delete_counter: u32,

	_phantom: PhantomData<T>,
}

/// View on a contract that is marked for deletion.
struct DeletionQueueEntry<'a, T: Config> {
	/// the trie id of the contract to delete.
	trie_id: TrieId,

	/// A mutable reference on the queue so that the contract can be removed, and none can be added
	/// or read in the meantime.
	queue: &'a mut DeletionQueueManager<T>,
}

impl<'a, T: Config> DeletionQueueEntry<'a, T> {
	/// Remove the contract from the deletion queue.
	fn remove(self) {
		<DeletionQueue<T>>::remove(self.queue.delete_counter);
		self.queue.delete_counter = self.queue.delete_counter.wrapping_add(1);
		<DeletionQueueCounter<T>>::set(self.queue.clone());
	}
}

impl<T: Config> DeletionQueueManager<T> {
	/// Load the `DeletionQueueCounter`, so we can perform read or write operations on the
	/// DeletionQueue storage.
	fn load() -> Self {
		<DeletionQueueCounter<T>>::get()
	}

	/// Returns `true` if the queue contains no elements.
	fn is_empty(&self) -> bool {
		self.insert_counter.wrapping_sub(self.delete_counter) == 0
	}

	/// Insert a contract in the deletion queue.
	fn insert(&mut self, trie_id: TrieId) {
		<DeletionQueue<T>>::insert(self.insert_counter, trie_id);
		self.insert_counter = self.insert_counter.wrapping_add(1);
		<DeletionQueueCounter<T>>::set(self.clone());
	}

	/// Fetch the next contract to be deleted.
	///
	/// Note:
	/// we use the delete counter to get the next value to read from the queue and thus don't pay
	/// the cost of an extra call to `sp_io::storage::next_key` to lookup the next entry in the map
	fn next(&mut self) -> Option<DeletionQueueEntry<T>> {
		if self.is_empty() {
			return None
		}

		let entry = <DeletionQueue<T>>::get(self.delete_counter);
		entry.map(|trie_id| DeletionQueueEntry { trie_id, queue: self })
	}
}

#[cfg(test)]
impl<T: Config> DeletionQueueManager<T> {
	pub fn from_test_values(insert_counter: u32, delete_counter: u32) -> Self {
		Self { insert_counter, delete_counter, _phantom: Default::default() }
	}
	pub fn as_test_tuple(&self) -> (u32, u32) {
		(self.insert_counter, self.delete_counter)
	}
}
