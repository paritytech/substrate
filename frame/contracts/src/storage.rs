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
	AliveContractInfo, BalanceOf, CodeHash, ContractInfoOf, Trait, TrieId,
};
use sp_io::hashing::blake2_256;
use sp_runtime::traits::Bounded;
use support::{storage::child, traits::Get, StorageMap};

pub fn read_contract_storage(trie_id: &TrieId, key: &StorageKey) -> Option<Vec<u8>> {
	child::get_raw(trie_id, &blake2_256(key))
}

pub fn write_contract_storage(trie_id: &TrieId, key: &StorageKey, value: Option<Vec<u8>>) {
	// TODO: How do we track the size of the contract's
	let hashed_key = blake2_256(key);
	match value {
		Some(v) => child::put_raw(trie_id, &hashed_key, &v),
		None => child::kill(trie_id, &hashed_key),
	}
}

pub fn rent_allowance<T: Trait>(account: &AccountIdOf<T>) -> Option<BalanceOf<T>> {
	<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.rent_allowance))
}

pub fn set_rent_allowance<T: Trait>(account: &AccountIdOf<T>, rent_allowance: BalanceOf<T>) {
	unimplemented!()
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
				storage_size: T::StorageSizeOffset::get(),
				trie_id,
				deduct_block: <system::Module<T>>::block_number(),
				rent_allowance: <BalanceOf<T>>::max_value(),
				last_write: None,
			}
			.into(),
		);

		Ok(())
	})
}

pub fn destroy_contract<T: Trait>(address: &AccountIdOf<T>, trie_id: &TrieId) {
	<ContractInfoOf<T>>::remove(address);
	child::kill_storage(trie_id);
}
