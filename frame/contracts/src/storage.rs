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

use crate::{
	exec::{AccountIdOf, StorageKey},
	AliveContractInfo, BalanceOf, CodeHash, ContractInfo, ContractInfoOf, Trait, TrieId,
};
use sp_std::prelude::*;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::Bounded;
use frame_support::{storage::child, StorageMap};

pub fn read_contract_storage(trie_id: &TrieId, key: &StorageKey) -> Option<Vec<u8>> {
	child::get_raw(&crate::child_trie_info(&trie_id), &blake2_256(key))
}

pub fn write_contract_storage<T: Trait>(
	account: &AccountIdOf<T>,
	trie_id: &TrieId,
	key: &StorageKey,
	value: Option<Vec<u8>>,
) {
	let hashed_key = blake2_256(key);

	let child_trie_info = &crate::child_trie_info(&trie_id);

	// We need to accurately track the size of the storage of the contract.
	//
	// For that we query the previous value and get its size.
	let existing_size = child::get_raw(&child_trie_info, &hashed_key)
		.map(|v| v.len())
		.unwrap_or(0);
	let new_size = match value {
		Some(v) => {
			child::put_raw(&child_trie_info, &hashed_key, &v);
			v.len()
		}
		None => {
			child::kill(&child_trie_info, &hashed_key);
			0
		}
	};

	<ContractInfoOf<T>>::mutate(account, |maybe_contract_info| {
		match maybe_contract_info {
			Some(ContractInfo::Alive(ref mut alive_info)) => {
				alive_info.storage_size -= existing_size as u32;
				alive_info.storage_size += new_size as u32;
				alive_info.last_write = Some(<frame_system::Module<T>>::block_number());
			}
			_ => panic!(), // TODO: Justify this.
		}
	});
}

pub fn rent_allowance<T: Trait>(account: &AccountIdOf<T>) -> Option<BalanceOf<T>> {
	<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.rent_allowance))
}

pub fn set_rent_allowance<T: Trait>(account: &AccountIdOf<T>, rent_allowance: BalanceOf<T>) {
	<ContractInfoOf<T>>::mutate(account, |maybe_contract_info| {
		match maybe_contract_info {
			Some(ContractInfo::Alive(ref mut alive_info)) => {
				alive_info.rent_allowance = rent_allowance
			}
			_ => panic!(), // TODO: Justify this.
		}
	})
}

pub fn code_hash<T: Trait>(account: &AccountIdOf<T>) -> Option<CodeHash<T>> {
	<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.code_hash))
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

pub fn destroy_contract<T: Trait>(address: &AccountIdOf<T>, trie_id: &TrieId) {
	<ContractInfoOf<T>>::remove(address);
	child::kill_storage(&crate::child_trie_info(&trie_id));
}
