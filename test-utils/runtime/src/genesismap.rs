// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Tool for creating the genesis block.

use super::{system, wasm_binary_unwrap, AccountId, AuthorityId};
use codec::{Encode, Joiner, KeyedVec};
use sc_service::client::genesis;
use sp_core::{
	map,
	storage::{well_known_keys, Storage},
};
use sp_io::hashing::{blake2_256, twox_128};
use sp_runtime::traits::{Block as BlockT, Hash as HashT, Header as HeaderT};
use std::collections::BTreeMap;

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfig {
	authorities: Vec<AuthorityId>,
	balances: Vec<(AccountId, u64)>,
	heap_pages_override: Option<u64>,
	/// Additional storage key pairs that will be added to the genesis map.
	extra_storage: Storage,
}

impl GenesisConfig {
	pub fn new(
		authorities: Vec<AuthorityId>,
		endowed_accounts: Vec<AccountId>,
		balance: u64,
		heap_pages_override: Option<u64>,
		extra_storage: Storage,
	) -> Self {
		GenesisConfig {
			authorities,
			balances: endowed_accounts.into_iter().map(|a| (a, balance)).collect(),
			heap_pages_override,
			extra_storage,
		}
	}

	pub fn genesis_map(&self) -> Storage {
		let wasm_runtime = wasm_binary_unwrap().to_vec();
		let mut map: BTreeMap<Vec<u8>, Vec<u8>> = self
			.balances
			.iter()
			.map(|&(ref account, balance)| {
				(account.to_keyed_vec(b"balance:"), vec![].and(&balance))
			})
			.map(|(k, v)| (blake2_256(&k[..])[..].to_vec(), v.to_vec()))
			.chain(
				vec![
					(well_known_keys::CODE.into(), wasm_runtime),
					(
						well_known_keys::HEAP_PAGES.into(),
						vec![].and(&(self.heap_pages_override.unwrap_or(16 as u64))),
					),
				]
				.into_iter(),
			)
			.collect();
		map.insert(twox_128(&b"sys:auth"[..])[..].to_vec(), self.authorities.encode());
		// Add the extra storage entries.
		map.extend(self.extra_storage.top.clone().into_iter());

		// Assimilate the system genesis config.
		let mut storage =
			Storage { top: map, children_default: self.extra_storage.children_default.clone() };
		let mut config = system::GenesisConfig::default();
		config.authorities = self.authorities.clone();
		config
			.assimilate_storage(&mut storage)
			.expect("Adding `system::GensisConfig` to the genesis");

		storage
	}
}

pub fn insert_genesis_block(storage: &mut Storage) -> sp_core::hash::H256 {
	let child_roots = storage.children_default.iter().map(|(sk, child_content)| {
		let state_root =
			<<<crate::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
				child_content.data.clone().into_iter().collect(),
				sp_runtime::StateVersion::V1,
			);
		(sk.clone(), state_root.encode())
	});
	// add child roots to storage
	storage.top.extend(child_roots);
	let state_root = <<<crate::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		storage.top.clone().into_iter().collect(),
		sp_runtime::StateVersion::V1,
	);
	let block: crate::Block = genesis::construct_genesis_block(state_root);
	let genesis_hash = block.header.hash();
	storage.top.extend(additional_storage_with_genesis(&block));
	genesis_hash
}

pub fn additional_storage_with_genesis(genesis_block: &crate::Block) -> BTreeMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&b"latest"[..]).to_vec() => genesis_block.hash().as_fixed_bytes().to_vec()
	]
}
