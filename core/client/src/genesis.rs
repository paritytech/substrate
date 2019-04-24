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

use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT, Zero};

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block<
	Block: BlockT
> (
	state_root: Block::Hash
) -> Block {
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
	use parity_codec::{Encode, Decode, Joiner};
	use executor::{NativeExecutionDispatch, native_executor_instance};
	use state_machine::{self, OverlayedChanges, ExecutionStrategy, InMemoryChangesTrieStorage};
	use state_machine::backend::InMemory;
	use test_client::{
		runtime::genesismap::{GenesisConfig, additional_storage_with_genesis},
		runtime::{Hash, Transfer, Block, BlockNumber, Header, Digest},
		AccountKeyring, AuthorityKeyring
	};
	use runtime_primitives::traits::BlakeTwo256;
	use primitives::Blake2Hasher;
	use hex::*;

	native_executor_instance!(Executor, test_client::runtime::api::dispatch, test_client::runtime::native_version, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));

	fn executor() -> executor::NativeExecutor<Executor> {
		NativeExecutionDispatch::new(None)
	}

	fn construct_block(
		backend: &InMemory<Blake2Hasher>,
		number: BlockNumber,
		parent_hash: Hash,
		state_root: Hash,
		txs: Vec<Transfer>
	) -> (Vec<u8>, Hash) {
		use trie::ordered_trie_root;

		let transactions = txs.into_iter().map(|tx| tx.into_signed_tx()).collect::<Vec<_>>();

		let extrinsics_root = ordered_trie_root::<Blake2Hasher, _, _>(transactions.iter().map(Encode::encode)).into();

		let mut header = Header {
			parent_hash,
			number,
			state_root,
			extrinsics_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.hash();
		let mut overlay = OverlayedChanges::default();

		state_machine::new(
			backend,
			Some(&InMemoryChangesTrieStorage::new()),
			state_machine::NeverOffchainExt::new(),
			&mut overlay,
			&executor(),
			"Core_initialize_block",
			&header.encode(),
		).execute(
			ExecutionStrategy::NativeElseWasm,
		).unwrap();

		for tx in transactions.iter() {
			state_machine::new(
				backend,
				Some(&InMemoryChangesTrieStorage::new()),
				state_machine::NeverOffchainExt::new(),
				&mut overlay,
				&executor(),
				"BlockBuilder_apply_extrinsic",
				&tx.encode(),
			).execute(
				ExecutionStrategy::NativeElseWasm,
			).unwrap();
		}

		let (ret_data, _, _) = state_machine::new(
			backend,
			Some(&InMemoryChangesTrieStorage::new()),
			state_machine::NeverOffchainExt::new(),
			&mut overlay,
			&executor(),
			"BlockBuilder_finalize_block",
			&[],
		).execute(
			ExecutionStrategy::NativeElseWasm,
		).unwrap();
		header = Header::decode(&mut &ret_data[..]).unwrap();

		(vec![].and(&Block { header, extrinsics: transactions }), hash)
	}

	fn block1(genesis_hash: Hash, backend: &InMemory<Blake2Hasher>) -> (Vec<u8>, Hash) {
		construct_block(
			backend,
			1,
			genesis_hash,
			hex!("25e5b37074063ab75c889326246640729b40d0c86932edc527bc80db0e04fe5c").into(),
			vec![Transfer {
				from: AccountKeyring::One.into(),
				to: AccountKeyring::Two.into(),
				amount: 69,
				nonce: 0,
			}]
		)
	}

	#[test]
	fn construct_genesis_should_work_with_native() {
		let mut storage = GenesisConfig::new(false,
			vec![AuthorityKeyring::One.into(), AuthorityKeyring::Two.into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			1000
		).genesis_map();
		let state_root = BlakeTwo256::trie_root(storage.clone().into_iter());
		let block = construct_genesis_block::<Block>(state_root);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = state_machine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::new()),
			state_machine::NeverOffchainExt::new(),
			&mut overlay,
			&executor(),
			"Core_execute_block",
			&b1data,
		).execute(
			ExecutionStrategy::NativeElseWasm,
		).unwrap();
	}

	#[test]
	fn construct_genesis_should_work_with_wasm() {
		let mut storage = GenesisConfig::new(false,
			vec![AuthorityKeyring::One.into(), AuthorityKeyring::Two.into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			1000
		).genesis_map();
		let state_root = BlakeTwo256::trie_root(storage.clone().into_iter());
		let block = construct_genesis_block::<Block>(state_root);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = state_machine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::new()),
			state_machine::NeverOffchainExt::new(),
			&mut overlay,
			&executor(),
			"Core_execute_block",
			&b1data,
		).execute(
			ExecutionStrategy::AlwaysWasm,
		).unwrap();
	}

	#[test]
	fn construct_genesis_with_bad_transaction_should_panic() {
		let mut storage = GenesisConfig::new(false,
			vec![AuthorityKeyring::One.into(), AuthorityKeyring::Two.into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			68
		).genesis_map();
		let state_root = BlakeTwo256::trie_root(storage.clone().into_iter());
		let block = construct_genesis_block::<Block>(state_root);
		let genesis_hash = block.header.hash();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let r = state_machine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::new()),
			state_machine::NeverOffchainExt::new(),
			&mut overlay,
			&Executor::new(None),
			"Core_execute_block",
			&b1data,
		).execute(
			ExecutionStrategy::NativeElseWasm,
		);
		assert!(r.is_err());
	}
}
