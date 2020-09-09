// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! This module contains routines for accessing and altering a contract related state.

use crate::{
	exec::{AccountIdOf, StorageKey},
	AliveContractInfo, BalanceOf, CodeHash, ContractInfo, ContractInfoOf, Trait, TrieId,
};
use sp_std::prelude::*;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::Bounded;
use frame_support::{storage::child, StorageMap};

/// An error that means that the account requested either doesn't exist or represents a tombstone
/// account.
#[cfg_attr(test, derive(PartialEq, Eq, Debug))]
pub struct ContractAbsentError;

/// Reads a storage kv pair of a contract.
///
/// The read is performed from the `trie_id` only. The `address` is not necessary. If the contract
/// doesn't store under the given `key` `None` is returned.
pub fn read_contract_storage(trie_id: &TrieId, key: &StorageKey) -> Option<Vec<u8>> {
	child::get_raw(&crate::child_trie_info(&trie_id), &blake2_256(key))
}

/// Update a storage entry into a contract's kv storage.
///
/// If the `opt_new_value` is `None` then the kv pair is removed.
///
/// This function also updates the bookkeeping info such as: number of total non-empty pairs a
/// contract owns, the last block the storage was written to, etc. That's why, in contrast to
/// `read_contract_storage`, this function also requires the `account` ID.
///
/// If the contract specified by the id `account` doesn't exist `Err` is returned.`
pub fn write_contract_storage<T: Trait>(
	account: &AccountIdOf<T>,
	trie_id: &TrieId,
	key: &StorageKey,
	opt_new_value: Option<Vec<u8>>,
) -> Result<(), ContractAbsentError> {
	let mut new_info = match <ContractInfoOf<T>>::get(account) {
		Some(ContractInfo::Alive(alive)) => alive,
		None | Some(ContractInfo::Tombstone(_)) => return Err(ContractAbsentError),
	};

	let hashed_key = blake2_256(key);
	let child_trie_info = &crate::child_trie_info(&trie_id);

	// In order to correctly update the book keeping we need to fetch the previous
	// value of the key-value pair.
	//
	// It might be a bit more clean if we had an API that supported getting the size
	// of the value without going through the loading of it. But at the moment of
	// writing, there is no such API.
	//
	// That's not a show stopper in any case, since the performance cost is
	// dominated by the trie traversal anyway.
	let opt_prev_value = child::get_raw(&child_trie_info, &hashed_key);

	// Update the total number of KV pairs and the number of empty pairs.
	match (&opt_prev_value, &opt_new_value) {
		(Some(prev_value), None) => {
			new_info.total_pair_count -= 1;
			if prev_value.is_empty() {
				new_info.empty_pair_count -= 1;
			}
		},
		(None, Some(new_value)) => {
			new_info.total_pair_count += 1;
			if new_value.is_empty() {
				new_info.empty_pair_count += 1;
			}
		},
		(Some(prev_value), Some(new_value)) => {
			if prev_value.is_empty() {
				new_info.empty_pair_count -= 1;
			}
			if new_value.is_empty() {
				new_info.empty_pair_count += 1;
			}
		}
		(None, None) => {}
	}

	// Update the total storage size.
	let prev_value_len = opt_prev_value
		.as_ref()
		.map(|old_value| old_value.len() as u32)
		.unwrap_or(0);
	let new_value_len = opt_new_value
		.as_ref()
		.map(|new_value| new_value.len() as u32)
		.unwrap_or(0);
	new_info.storage_size = new_info
		.storage_size
		.saturating_add(new_value_len)
		.saturating_sub(prev_value_len);

	new_info.last_write = Some(<frame_system::Module<T>>::block_number());
	<ContractInfoOf<T>>::insert(&account, ContractInfo::Alive(new_info));

	// Finally, perform the change on the storage.
	match opt_new_value {
		Some(new_value) => child::put_raw(&child_trie_info, &hashed_key, &new_value[..]),
		None => child::kill(&child_trie_info, &hashed_key),
	}

	Ok(())
}

/// Returns the rent allowance set for the contract give by the account id.
pub fn rent_allowance<T: Trait>(
	account: &AccountIdOf<T>,
) -> Result<BalanceOf<T>, ContractAbsentError> {
	<ContractInfoOf<T>>::get(account)
		.and_then(|i| i.as_alive().map(|i| i.rent_allowance))
		.ok_or(ContractAbsentError)
}

/// Set the rent allowance for the contract given by the account id.
///
/// Returns `Err` if the contract doesn't exist or is a tombstone.
pub fn set_rent_allowance<T: Trait>(
	account: &AccountIdOf<T>,
	rent_allowance: BalanceOf<T>,
) -> Result<(), ContractAbsentError> {
	<ContractInfoOf<T>>::mutate(account, |maybe_contract_info| match maybe_contract_info {
		Some(ContractInfo::Alive(ref mut alive_info)) => {
			alive_info.rent_allowance = rent_allowance;
			Ok(())
		}
		_ => Err(ContractAbsentError),
	})
}

/// Returns the code hash of the contract specified by `account` ID.
#[cfg(test)]
pub fn code_hash<T: Trait>(account: &AccountIdOf<T>) -> Result<CodeHash<T>, ContractAbsentError> {
	<ContractInfoOf<T>>::get(account)
		.and_then(|i| i.as_alive().map(|i| i.code_hash))
		.ok_or(ContractAbsentError)
}

/// Creates a new contract descriptor in the storage with the given code hash at the given address.
///
/// Returns `Err` if there is already a contract (or a tombstone) exists at the given address.
pub fn place_contract<T: Trait>(
	account: &AccountIdOf<T>,
	trie_id: TrieId,
	ch: CodeHash<T>,
) -> Result<(), &'static str> {
	<ContractInfoOf<T>>::mutate(account, |maybe_contract_info| {
		if maybe_contract_info.is_some() {
			return Err("Alive contract or tombstone already exists");
		}

		*maybe_contract_info = Some(
			AliveContractInfo::<T> {
				code_hash: ch,
				storage_size: 0,
				trie_id,
				deduct_block: <frame_system::Module<T>>::block_number(),
				rent_allowance: <BalanceOf<T>>::max_value(),
				empty_pair_count: 0,
				total_pair_count: 0,
				last_write: None,
			}
			.into(),
		);

		Ok(())
	})
}

/// Removes the contract and all the storage associated with it.
///
/// This function doesn't affect the account.
pub fn destroy_contract<T: Trait>(address: &AccountIdOf<T>, trie_id: &TrieId) {
	<ContractInfoOf<T>>::remove(address);
	child::kill_storage(&crate::child_trie_info(&trie_id));
}
