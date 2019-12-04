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

use sp_runtime::traits::{Block as BlockT, Header as HeaderT, Hash as HashT, Zero};

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block<
	Block: BlockT
> (
	state_root: Block::Hash
) -> Block {
	let extrinsics_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		Vec::new(),
	);

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
	use codec::{Encode, Decode, Joiner};
	use executor::native_executor_instance;
	use state_machine::{
		StateMachine, OverlayedChanges, ExecutionStrategy, InMemoryChangesTrieStorage,
	};
	use state_machine::backend::InMemory;
	use test_client::{
		runtime::genesismap::{GenesisConfig, insert_genesis_block},
		runtime::{Hash, Transfer, Block, BlockNumber, Header, Digest},
		AccountKeyring, Sr25519Keyring,
	};
	use primitives::{Blake2Hasher, map};
	use hex_literal::*;

	native_executor_instance!(
		Executor,
		test_client::runtime::api::dispatch,
		test_client::runtime::native_version
	);

	fn executor() -> executor::NativeExecutor<Executor> {
		executor::NativeExecutor::new(executor::WasmExecutionMethod::Interpreted, None)
	}

	fn construct_block(
		backend: &InMemory<Blake2Hasher>,
		number: BlockNumber,
		parent_hash: Hash,
		state_root: Hash,
		txs: Vec<Transfer>
	) -> (Vec<u8>, Hash) {
		use trie::{TrieConfiguration, trie_types::Layout};

		let transactions = txs.into_iter().map(|tx| tx.into_signed_tx()).collect::<Vec<_>>();

		let iter = transactions.iter().map(Encode::encode);
		let extrinsics_root = Layout::<Blake2Hasher>::ordered_trie_root(iter).into();

		let mut header = Header {
			parent_hash,
			number,
			state_root,
			extrinsics_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.hash();
		let mut overlay = OverlayedChanges::default();

		StateMachine::new(
			backend,
			Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
			&mut overlay,
			&executor(),
			"Core_initialize_block",
			&header.encode(),
			Default::default(),
		).execute(
			ExecutionStrategy::NativeElseWasm,
		).unwrap();

		for tx in transactions.iter() {
			StateMachine::new(
				backend,
				Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
				&mut overlay,
				&executor(),
				"BlockBuilder_apply_extrinsic",
				&tx.encode(),
				Default::default(),
			).execute(
				ExecutionStrategy::NativeElseWasm,
			).unwrap();
		}

		let (ret_data, _, _) = StateMachine::new(
			backend,
			Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
			&mut overlay,
			&executor(),
			"BlockBuilder_finalize_block",
			&[],
			Default::default(),
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
			vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			1000,
			None,
			map![],
			map![],
		).genesis_map();
		let genesis_hash = insert_genesis_block(&mut storage);

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = StateMachine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
			&mut overlay,
			&executor(),
			"Core_execute_block",
			&b1data,
			Default::default(),
		).execute(
			ExecutionStrategy::NativeElseWasm,
		).unwrap();
	}

	#[test]
	fn construct_genesis_should_work_with_wasm() {
		let mut storage = GenesisConfig::new(false,
			vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			1000,
			None,
			map![],
			map![],
		).genesis_map();
		let genesis_hash = insert_genesis_block(&mut storage);

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let _ = StateMachine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
			&mut overlay,
			&executor(),
			"Core_execute_block",
			&b1data,
			Default::default(),
		).execute(
			ExecutionStrategy::AlwaysWasm,
		).unwrap();
	}

	#[test]
	fn construct_genesis_with_bad_transaction_should_panic() {
		let mut storage = GenesisConfig::new(false,
			vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			68,
			None,
			map![],
			map![],
		).genesis_map();
		let genesis_hash = insert_genesis_block(&mut storage);

		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let mut overlay = OverlayedChanges::default();
		let r = StateMachine::new(
			&backend,
			Some(&InMemoryChangesTrieStorage::<_, u64>::new()),
			&mut overlay,
			&executor(),
			"Core_execute_block",
			&b1data,
			Default::default(),
		).execute(
			ExecutionStrategy::NativeElseWasm,
		);
		assert!(r.is_err());
	}
}
