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
	currency, substrate_test_pallet, wasm_binary_unwrap, AccountId, Balance, GenesisConfig,
};
use codec::Encode;
use sc_service::construct_genesis_block;
use sp_core::{
	sr25519,
	storage::{well_known_keys, StateVersion, Storage},
	Pair,
};
use sp_keyring::{AccountKeyring, Sr25519Keyring};
use sp_runtime::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT},
	BuildStorage,
};

/// Builder for generating storage from substrate-test-runtime genesis config.
///
/// Default storage can be extended with additional key-value pairs.
pub struct GenesisStorageBuilder {
	/// Authorities accounts used by any component requiring an authority set (e.g. babe).
	authorities: Vec<AccountId>,
	/// Accounts to be endowed with some funds.
	balances: Vec<(AccountId, u64)>,
	/// Override default number of heap pages.
	heap_pages_override: Option<u64>,
	/// Additional storage key pairs that will be added to the genesis map.
	extra_storage: Storage,
	/// Optional wasm code override.
	wasm_code: Option<Vec<u8>>,
}

impl Default for GenesisStorageBuilder {
	/// Creates a builder with default settings for `substrate_test_runtime`.
	fn default() -> Self {
		Self::new(
			vec![
				Sr25519Keyring::Alice.into(),
				Sr25519Keyring::Bob.into(),
				Sr25519Keyring::Charlie.into(),
			],
			(0..16_usize)
				.into_iter()
				.map(|i| AccountKeyring::numeric(i).public())
				.chain(vec![
					AccountKeyring::Alice.into(),
					AccountKeyring::Bob.into(),
					AccountKeyring::Charlie.into(),
				])
				.collect(),
			1000 * currency::DOLLARS,
		)
	}
}

impl GenesisStorageBuilder {
	/// Creates a storage builder for genesis config. `substrage test runtime` `GenesisConfig` is
	/// initialized with provided `authorities`, `endowed_accounts` with given balance. Key-pairs
	/// from `extra_storage` will be injected into built storage. `HEAP_PAGES` key and value will
	/// also be placed into storage.
	pub fn new(
		authorities: Vec<AccountId>,
		endowed_accounts: Vec<AccountId>,
		balance: Balance,
	) -> Self {
		GenesisStorageBuilder {
			authorities,
			balances: endowed_accounts.into_iter().map(|a| (a, balance)).collect(),
			heap_pages_override: None,
			extra_storage: Default::default(),
			wasm_code: None,
		}
	}

	/// Override default wasm code to be placed into GenesisConfig.
	pub fn with_wasm_code(mut self, wasm_code: &Option<Vec<u8>>) -> Self {
		self.wasm_code = wasm_code.clone();
		self
	}

	pub fn with_heap_pages(mut self, heap_pages_override: Option<u64>) -> Self {
		self.heap_pages_override = heap_pages_override;
		self
	}

	pub fn with_extra_storage(mut self, storage: Storage) -> Self {
		self.extra_storage = storage;
		self
	}

	/// Builds the `GenesisConfig` and returns its storage.
	pub fn build(self) -> Storage {
		let authorities_sr25519: Vec<_> = self
			.authorities
			.clone()
			.into_iter()
			.map(|id| sr25519::Public::from(id))
			.collect();

		let genesis_config = GenesisConfig {
			system: frame_system::GenesisConfig {
				code: self.wasm_code.clone().unwrap_or(wasm_binary_unwrap().to_vec()),
			},
			babe: pallet_babe::GenesisConfig {
				authorities: authorities_sr25519
					.clone()
					.into_iter()
					.map(|x| (x.into(), 1))
					.collect(),
				epoch_config: Some(crate::TEST_RUNTIME_BABE_EPOCH_CONFIGURATION),
			},
			substrate_test: substrate_test_pallet::GenesisConfig {
				authorities: authorities_sr25519.clone(),
			},
			balances: pallet_balances::GenesisConfig { balances: self.balances.clone() },
		};

		let mut storage = genesis_config
			.build_storage()
			.expect("Build storage from substrate-test-runtime GenesisConfig");

		storage.top.insert(
			well_known_keys::HEAP_PAGES.into(),
			self.heap_pages_override.unwrap_or(16_u64).encode(),
		);

		storage.top.extend(self.extra_storage.top.clone());
		storage.children_default.extend(self.extra_storage.children_default.clone());

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

	genesis_hash
}
