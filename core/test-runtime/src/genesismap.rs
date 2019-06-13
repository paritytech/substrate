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
use runtime_io::{blake2_256, twox_128};
use super::{AuthorityId, AccountId};
use parity_codec::{Encode, KeyedVec, Joiner};
use primitives::{ChangesTrieConfiguration, map, storage::well_known_keys};
use runtime_primitives::traits::Block;

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfig {
	pub changes_trie_config: Option<ChangesTrieConfiguration>,
	pub authorities: Vec<AuthorityId>,
	pub balances: Vec<(AccountId, u64)>,
}

impl GenesisConfig {
	pub fn new(
		support_changes_trie: bool,
		authorities: Vec<AuthorityId>,
		endowed_accounts: Vec<AccountId>,
		balance: u64
	) -> Self {
		GenesisConfig {
			changes_trie_config: match support_changes_trie {
				true => Some(super::changes_trie_config()),
				false => None,
			},
			authorities: authorities.clone(),
			balances: endowed_accounts.into_iter().map(|a| (a, balance)).collect(),
		}
	}

	pub fn genesis_map(&self) -> HashMap<Vec<u8>, Vec<u8>> {
		#[cfg(feature = "include-wasm-blob")]
		let wasm_runtime = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm").to_vec();
		let mut map: HashMap<Vec<u8>, Vec<u8>> = self.balances.iter()
			.map(|&(ref account, balance)| (account.to_keyed_vec(b"balance:"), vec![].and(&balance)))
			.map(|(k, v)| (blake2_256(&k[..])[..].to_vec(), v.to_vec()))
			.chain(vec![
				#[cfg(feature = "include-wasm-blob")]
				(well_known_keys::CODE.into(), wasm_runtime),
				(well_known_keys::HEAP_PAGES.into(), vec![].and(&(16 as u64))),
			].into_iter())
			.collect();
		if let Some(ref changes_trie_config) = self.changes_trie_config {
			map.insert(well_known_keys::CHANGES_TRIE_CONFIG.to_vec(), changes_trie_config.encode());
		}
		map.insert(twox_128(&b"sys:auth"[..])[..].to_vec(), self.authorities.encode());
		map
	}
}

pub fn additional_storage_with_genesis(genesis_block: &crate::Block) -> HashMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&b"latest"[..]).to_vec() => genesis_block.hash().as_fixed_bytes().to_vec()
	]
}
