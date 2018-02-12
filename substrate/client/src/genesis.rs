// Copyright 2017 Parity Technologies (UK) Ltd.
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
use primitives::{Block, Header};
use triehash::trie_root;

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block(storage: &HashMap<Vec<u8>, Vec<u8>>) -> Block {
	let state_root = trie_root(storage.clone().into_iter()).0.into();
	let header = Header {
		parent_hash: Default::default(),
		number: 0,
		state_root,
		transaction_root: trie_root(vec![].into_iter()).0.into(),
		digest: Default::default(),
	};
	Block {
		header,
		transactions: vec![],
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Slicable, Joiner};
	use runtime_support::Hashable;
	use keyring::Keyring;
	use test_runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
	use executor::WasmExecutor;
	use state_machine::{execute, OverlayedChanges};
	use state_machine::backend::InMemory;
	use test_runtime::{self, Hash, Block, BlockNumber, Header, Digest, Transaction,
		UncheckedTransaction};
	use ed25519::{Public, Pair};

	native_executor_instance!(Executor, test_runtime::api::dispatch, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));

	fn construct_block(backend: &InMemory, number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|tx| {
			let signature = Pair::from(Keyring::from_public(Public::from_raw(tx.from)).unwrap())
				.sign(&tx.encode());

			UncheckedTransaction { tx, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::encode)).0.into();

		let mut header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		let mut overlay = OverlayedChanges::default();

		for tx in transactions.iter() {
			let ret_data = execute(
				backend,
				&mut overlay,
				&Executor::new(),
				"execute_transaction",
				&vec![].and(&header).and(tx)
			).unwrap();
			header = Header::decode(&mut &ret_data[..]).unwrap();
		}

		let ret_data = execute(
			backend,
			&mut overlay,
			&Executor::new(),
			"finalise_block",
			&vec![].and(&header)
		).unwrap();
		header = Header::decode(&mut &ret_data[..]).unwrap();

		(vec![].and(&Block { header, transactions }), hash.into())
	}

	fn block1(genesis_hash: Hash, backend: &InMemory) -> (Vec<u8>, Hash) {
		construct_block(
			backend,
			1,
			genesis_hash,
			hex!("25e5b37074063ab75c889326246640729b40d0c86932edc527bc80db0e04fe5c").into(),
			vec![Transaction {
				from: Keyring::One.to_raw_public(),
				to: Keyring::Two.to_raw_public(),
				amount: 69,
				nonce: 0,
			}]
		)
	}

	#[test]
	fn construct_genesis_should_work() {
		let mut storage = GenesisConfig::new_simple(
			vec![Keyring::One.to_raw_public(), Keyring::Two.to_raw_public()], 1000
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256().into();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&Executor::new(),
			"execute_block",
			&b1data
		).unwrap();

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&WasmExecutor,
			"execute_block",
			&b1data
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn construct_genesis_with_bad_transaction_should_panic() {
		let mut storage = GenesisConfig::new_simple(
			vec![Keyring::One.to_raw_public(), Keyring::Two.to_raw_public()], 68
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256().into();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&Executor::new(),
			"execute_block",
			&b1data
		).unwrap();
	}
}
