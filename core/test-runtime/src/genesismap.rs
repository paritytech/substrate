// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tool for creating the genesis block.

use std::collections::HashMap;
use runtime_io::hashing::{blake2_256, twox_128};
use super::{AuthorityId, AccountId, WASM_BINARY, system};
use codec::{Encode, KeyedVec, Joiner};
use primitives::{ChangesTrieConfiguration, map, storage::well_known_keys};
use sr_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT};

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfig {
	changes_trie_config: Option<ChangesTrieConfiguration>,
	authorities: Vec<AuthorityId>,
	balances: Vec<(AccountId, u64)>,
	heap_pages_override: Option<u64>,
	/// Additional storage key pairs that will be added to the genesis map.
	extra_storage: HashMap<Vec<u8>, Vec<u8>>,
	child_extra_storage: HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
}

impl GenesisConfig {
	pub fn new(
		support_changes_trie: bool,
		authorities: Vec<AuthorityId>,
		endowed_accounts: Vec<AccountId>,
		balance: u64,
		heap_pages_override: Option<u64>,
		extra_storage: HashMap<Vec<u8>, Vec<u8>>,
		child_extra_storage: HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
	) -> Self {
		GenesisConfig {
			changes_trie_config: match support_changes_trie {
				true => Some(super::changes_trie_config()),
				false => None,
			},
			authorities: authorities.clone(),
			balances: endowed_accounts.into_iter().map(|a| (a, balance)).collect(),
			heap_pages_override,
			extra_storage,
			child_extra_storage,
		}
	}

	pub fn genesis_map(&self) -> (
		HashMap<Vec<u8>, Vec<u8>>,
		HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
	) {
		let wasm_runtime = WASM_BINARY.to_vec();
		let mut map: HashMap<Vec<u8>, Vec<u8>> = self.balances.iter()
			.map(|&(ref account, balance)| (account.to_keyed_vec(b"balance:"), vec![].and(&balance)))
			.map(|(k, v)| (blake2_256(&k[..])[..].to_vec(), v.to_vec()))
			.chain(vec![
				(well_known_keys::CODE.into(), wasm_runtime),
				(
					well_known_keys::HEAP_PAGES.into(),
					vec![].and(&(self.heap_pages_override.unwrap_or(16 as u64))),
				),
			].into_iter())
			.collect();
		if let Some(ref changes_trie_config) = self.changes_trie_config {
			map.insert(well_known_keys::CHANGES_TRIE_CONFIG.to_vec(), changes_trie_config.encode());
		}
		map.insert(twox_128(&b"sys:auth"[..])[..].to_vec(), self.authorities.encode());
		// Add the extra storage entries.
		map.extend(self.extra_storage.clone().into_iter());

		// Assimilate the system genesis config.
		let mut storage = (map, self.child_extra_storage.clone());
		let mut config = system::GenesisConfig::default();
		config.authorities = self.authorities.clone();
		config.assimilate_storage(&mut storage).expect("Adding `system::GensisConfig` to the genesis");

		storage
	}
}

pub fn insert_genesis_block(
	storage: &mut (
		HashMap<Vec<u8>, Vec<u8>>,
		HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
	)
) -> primitives::hash::H256 {
	let child_roots = storage.1.iter().map(|(sk, child_map)| {
		let state_root = <<<crate::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
			child_map.clone().into_iter().collect(),
		);
		(sk.clone(), state_root.encode())
	});
	let state_root = <<<crate::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		storage.0.clone().into_iter().chain(child_roots).collect()
	);
	let block: crate::Block = substrate_client::genesis::construct_genesis_block(state_root);
	let genesis_hash = block.header.hash();
	storage.0.extend(additional_storage_with_genesis(&block));
	genesis_hash
}

pub fn additional_storage_with_genesis(genesis_block: &crate::Block) -> HashMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&b"latest"[..]).to_vec() => genesis_block.hash().as_fixed_bytes().to_vec()
	]
}
