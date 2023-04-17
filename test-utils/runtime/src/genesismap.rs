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

//! Tool for creating the genesis block.

use super::{
	substrate_test_pallet, wasm_binary_unwrap, AccountId, AuthorityId, Balance, GenesisConfig,
	Runtime,
};
use codec::{Encode, Joiner};
use sc_service::construct_genesis_block;
use sp_core::{
	map,
	storage::{well_known_keys, StateVersion, Storage},
};
use sp_io::hashing::twox_128;
use sp_runtime::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT},
	BuildStorage,
};
use std::collections::BTreeMap;

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfigBuilder {
	authorities: Vec<AuthorityId>,
	balances: Vec<(AccountId, u64)>,
	heap_pages_override: Option<u64>,
	/// Additional storage key pairs that will be added to the genesis map.
	extra_storage: Storage,
}

impl GenesisConfigBuilder {
	pub fn new(
		authorities: Vec<AuthorityId>,
		endowed_accounts: Vec<AccountId>,
		balance: Balance,
		heap_pages_override: Option<u64>,
		extra_storage: Storage,
	) -> Self {
		GenesisConfigBuilder {
			authorities,
			balances: endowed_accounts.into_iter().map(|a| (a, balance)).collect(),
			heap_pages_override,
			extra_storage,
		}
	}

	pub fn genesis_map(&self) -> Storage {
		let genesis_config = GenesisConfig {
			system: frame_system::GenesisConfig { code: wasm_binary_unwrap().to_vec() },
			babe: pallet_babe::GenesisConfig {
				authorities: self.authorities.clone().into_iter().map(|x| (x, 1)).collect(),
				epoch_config: Some(crate::TEST_RUNTIME_BABE_EPOCH_CONFIGURATION),
			},
			substrate_test: substrate_test_pallet::GenesisConfig {
				authorities: self.authorities.clone(),
			},
			balances: pallet_balances::GenesisConfig { balances: self.balances.clone() },
		};
		let mut storage = genesis_config
			.build_storage()
			.expect("Build storage from substrate_test runtime GenesisConfig");

		{
			let map: BTreeMap<Vec<u8>, Vec<u8>> = vec![(
				well_known_keys::HEAP_PAGES.into(),
				vec![].and(&(self.heap_pages_override.unwrap_or(16_u64))),
			)]
			.into_iter()
			.collect();

			storage.top.extend(map);
		}

		// Add the extra storage entries.
		storage.top.extend(self.extra_storage.top.clone().into_iter());
		storage
			.children_default
			.extend(self.extra_storage.children_default.clone().into_iter());

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
	let block: crate::Block = construct_genesis_block(state_root, StateVersion::V1);
	let genesis_hash = block.header.hash();
	storage.top.extend(additional_storage_with_genesis(&block));
	genesis_hash
}

pub fn additional_storage_with_genesis(genesis_block: &crate::Block) -> BTreeMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&b"latest"[..]).to_vec() => genesis_block.hash().as_fixed_bytes().to_vec()
	]
}
