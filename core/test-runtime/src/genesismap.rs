// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Tool for creating the genesis block.

use std::collections::HashMap;
use runtime_io::{blake2_256, twox_128};
use super::AccountId;
use parity_codec::{Encode, KeyedVec, Joiner};
use primitives::{ChangesTrieConfiguration, map, storage::well_known_keys};
use runtime_primitives::traits::Block;
use primitives::ed25519::Public as AuthorityId;

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfig {
	pub changes_trie_config: Option<ChangesTrieConfiguration>,
	pub authorities: Vec<AuthorityId>,
	pub balances: Vec<(AccountId, u64)>,
}

impl GenesisConfig {
	pub fn new(support_changes_trie: bool, authorities: Vec<AuthorityId>, endowed_accounts: Vec<AccountId>, balance: u64) -> Self {
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
		let wasm_runtime = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm").to_vec();
		let mut map: HashMap<Vec<u8>, Vec<u8>> = self.balances.iter()
			.map(|&(ref account, balance)| (account.to_keyed_vec(b"balance:"), vec![].and(&balance)))
			.map(|(k, v)| (blake2_256(&k[..])[..].to_vec(), v.to_vec()))
			.chain(vec![
				(well_known_keys::CODE.into(), wasm_runtime),
				(well_known_keys::HEAP_PAGES.into(), vec![].and(&(16 as u64))),
				(well_known_keys::AUTHORITY_COUNT.into(), vec![].and(&(self.authorities.len() as u32))),
			].into_iter())
			.chain(self.authorities.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(well_known_keys::AUTHORITY_PREFIX), vec![].and(account)))
			)
			.collect();
		if let Some(ref changes_trie_config) = self.changes_trie_config {
			map.insert(well_known_keys::CHANGES_TRIE_CONFIG.to_vec(), changes_trie_config.encode());
		}
		map
	}
}

pub fn additional_storage_with_genesis(genesis_block: &crate::Block) -> HashMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&b"latest"[..]).to_vec() => genesis_block.hash().as_fixed_bytes().to_vec()
	]
}
