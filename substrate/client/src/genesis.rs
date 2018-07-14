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

use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT, Zero};
use runtime_primitives::StorageMap;

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block<
	Block: BlockT
> (
	storage: &StorageMap
) -> Block {
	let state_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(storage.clone().into_iter());
	let extrinsics_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(::std::iter::empty::<(&[u8], &[u8])>());
	Block::new(
		<<Block as BlockT>::Header as HeaderT>::new(
			Zero::zero(),
			extrinsics_root,
			state_root,
			Default::default(),
			Default::default()
		),
		Default::default()
	)
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Slicable, Joiner};
	use keyring::Keyring;
	use executor::WasmExecutor;
	use state_machine::{execute, OverlayedChanges, ExecutionStrategy};
	use state_machine::backend::InMemory;
	use test_client;
	use test_client::runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
	use test_client::runtime::{Hash, Transfer, Block, BlockNumber, Header, Digest, Extrinsic};
	use ed25519::{Public, Pair};

	native_executor_instance!(Executor, test_client::runtime::api::dispatch, test_client::runtime::VERSION, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));

	fn construct_block(backend: &InMemory, number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transfer>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|tx| {
			let signature = Pair::from(Keyring::from_public(Public::from_raw(tx.from.0)).unwrap())
				.sign(&tx.encode()).into();

			Extrinsic { transfer: tx, signature }
		}).collect::<Vec<_>>();

		let extrinsics_root = ordered_trie_root(transactions.iter().map(Slicable::encode)).0.into();

		println!("root before: {:?}", extrinsics_root);
		let mut header = Header {
			parent_hash,
			number,
			state_root,
			extrinsics_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.hash();
		let mut overlay = OverlayedChanges::default();

		execute(
			backend,
			&mut overlay,
			&Executor::new(),
			"initialise_block",
			&header.encode(),
			ExecutionStrategy::NativeWhenPossible,
		).unwrap();

		for tx in transactions.iter() {
			execute(
				backend,
				&mut overlay,
				&Executor::new(),
				"apply_extrinsic",
				&tx.encode(),
				ExecutionStrategy::NativeWhenPossible,
			).unwrap();
		}

		let (ret_data, _) = execute(
			backend,
			&mut overlay,
			&Executor::new(),
			"finalise_block",
			&[],
			ExecutionStrategy::NativeWhenPossible,
		).unwrap();
		header = Header::decode(&mut &ret_data[..]).unwrap();
		println!("root after: {:?}", header.extrinsics_root);

		(vec![].and(&Block { header, extrinsics: transactions }), hash)
	}

	fn block1(genesis_hash: Hash, backend: &InMemory) -> (Vec<u8>, Hash) {
		construct_block(
			backend,
			1,
			genesis_hash,
			hex!("25e5b37074063ab75c889326246640729b40d0c86932edc527bc80db0e04fe5c").into(),
			vec![Transfer {
				from: Keyring::One.to_raw_public().into(),
				to: Keyring::Two.to_raw_public().into(),
				amount: 69,
				nonce: 0,
			}]
		)
	}

	#[test]
	fn construct_genesis_should_work_with_native() {
		let mut storage = GenesisConfig::new_simple(
			vec![Keyring::One.to_raw_public().into(), Keyring::Two.to_raw_public().into()], 1000
		).genesis_map();
		let block = construct_genesis_block::<Block>(&storage);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&Executor::new(),
			"execute_block",
			&b1data,
			ExecutionStrategy::NativeWhenPossible,
		).unwrap();
	}

	#[test]
	fn construct_genesis_should_work_with_wasm() {
		let mut storage = GenesisConfig::new_simple(
			vec![Keyring::One.to_raw_public().into(), Keyring::Two.to_raw_public().into()], 1000
		).genesis_map();
		let block = construct_genesis_block::<Block>(&storage);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&WasmExecutor { heap_pages: 8 },
			"execute_block",
			&b1data,
			ExecutionStrategy::NativeWhenPossible,
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn construct_genesis_with_bad_transaction_should_panic() {
		let mut storage = GenesisConfig::new_simple(
			vec![Keyring::One.to_raw_public().into(), Keyring::Two.to_raw_public().into()], 68
		).genesis_map();
		let block = construct_genesis_block::<Block>(&storage);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = execute(
			&backend,
			&mut overlay,
			&Executor::with_heap_pages(8),
			"execute_block",
			&b1data,
			ExecutionStrategy::NativeWhenPossible,
		).unwrap();
	}
}
