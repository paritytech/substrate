// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use futures::executor::block_on;
use parity_scale_codec::{Decode, Encode, Joiner};
use sc_block_builder::BlockBuilderProvider;
use sc_client_api::{
	in_mem, BlockBackend, BlockchainEvents, FinalityNotifications, HeaderBackend, StorageProvider,
};
use sc_client_db::{Backend, BlocksPruning, DatabaseSettings, DatabaseSource, PruningMode};
use sc_consensus::{
	BlockCheckParams, BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult,
};
use sc_service::client::{new_in_mem, Client, LocalCallExecutor};
use sp_api::ProvideRuntimeApi;
use sp_consensus::{BlockOrigin, BlockStatus, Error as ConsensusError, SelectChain};
use sp_core::{testing::TaskExecutor, H256};
use sp_runtime::{
	generic::BlockId,
	traits::{BlakeTwo256, Block as BlockT, Header as HeaderT},
	ConsensusEngineId, Justifications, StateVersion,
};
use sp_state_machine::{
	backend::Backend as _, ExecutionStrategy, InMemoryBackend, OverlayedChanges, StateMachine,
};
use sp_storage::{ChildInfo, StorageKey};
use sp_trie::{LayoutV0, TrieConfiguration};
use std::{collections::HashSet, sync::Arc};
use substrate_test_runtime::TestAPI;
use substrate_test_runtime_client::{
	prelude::*,
	runtime::{
		genesismap::{insert_genesis_block, GenesisConfig},
		Block, BlockNumber, Digest, Hash, Header, RuntimeApi, Transfer,
	},
	AccountKeyring, BlockBuilderExt, ClientBlockImportExt, ClientExt, DefaultTestClientBuilderExt,
	Sr25519Keyring, TestClientBuilder, TestClientBuilderExt,
};

mod db;

const TEST_ENGINE_ID: ConsensusEngineId = *b"TEST";

pub struct ExecutorDispatch;

impl sc_executor::NativeExecutionDispatch for ExecutorDispatch {
	type ExtendHostFunctions = ();

	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
		substrate_test_runtime_client::runtime::api::dispatch(method, data)
	}

	fn native_version() -> sc_executor::NativeVersion {
		substrate_test_runtime_client::runtime::native_version()
	}
}

fn executor() -> sc_executor::NativeElseWasmExecutor<ExecutorDispatch> {
	sc_executor::NativeElseWasmExecutor::new(
		sc_executor::WasmExecutionMethod::Interpreted,
		None,
		8,
		2,
	)
}

fn construct_block(
	backend: &InMemoryBackend<BlakeTwo256>,
	number: BlockNumber,
	parent_hash: Hash,
	state_root: Hash,
	txs: Vec<Transfer>,
) -> (Vec<u8>, Hash) {
	let transactions = txs.into_iter().map(|tx| tx.into_signed_tx()).collect::<Vec<_>>();

	let iter = transactions.iter().map(Encode::encode);
	let extrinsics_root = LayoutV0::<BlakeTwo256>::ordered_trie_root(iter).into();

	let mut header = Header {
		parent_hash,
		number,
		state_root,
		extrinsics_root,
		digest: Digest { logs: vec![] },
	};
	let hash = header.hash();
	let mut overlay = OverlayedChanges::default();
	let backend_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(backend);
	let runtime_code = backend_runtime_code.runtime_code().expect("Code is part of the backend");
	let task_executor = Box::new(TaskExecutor::new());

	StateMachine::new(
		backend,
		&mut overlay,
		&executor(),
		"Core_initialize_block",
		&header.encode(),
		Default::default(),
		&runtime_code,
		task_executor.clone() as Box<_>,
	)
	.execute(ExecutionStrategy::NativeElseWasm)
	.unwrap();

	for tx in transactions.iter() {
		StateMachine::new(
			backend,
			&mut overlay,
			&executor(),
			"BlockBuilder_apply_extrinsic",
			&tx.encode(),
			Default::default(),
			&runtime_code,
			task_executor.clone() as Box<_>,
		)
		.execute(ExecutionStrategy::NativeElseWasm)
		.unwrap();
	}

	let ret_data = StateMachine::new(
		backend,
		&mut overlay,
		&executor(),
		"BlockBuilder_finalize_block",
		&[],
		Default::default(),
		&runtime_code,
		task_executor.clone() as Box<_>,
	)
	.execute(ExecutionStrategy::NativeElseWasm)
	.unwrap();
	header = Header::decode(&mut &ret_data[..]).unwrap();

	(vec![].and(&Block { header, extrinsics: transactions }), hash)
}

fn block1(genesis_hash: Hash, backend: &InMemoryBackend<BlakeTwo256>) -> (Vec<u8>, Hash) {
	construct_block(
		backend,
		1,
		genesis_hash,
		array_bytes::hex_n_into_unchecked(
			"25e5b37074063ab75c889326246640729b40d0c86932edc527bc80db0e04fe5c",
		),
		vec![Transfer {
			from: AccountKeyring::One.into(),
			to: AccountKeyring::Two.into(),
			amount: 69,
			nonce: 0,
		}],
	)
}

fn finality_notification_check(
	notifications: &mut FinalityNotifications<Block>,
	finalized: &[Hash],
	stale_heads: &[Hash],
) {
	match notifications.try_next() {
		Ok(Some(notif)) => {
			let stale_heads_expected: HashSet<_> = stale_heads.iter().collect();
			let stale_heads: HashSet<_> = notif.stale_heads.iter().collect();
			assert_eq!(notif.tree_route.as_ref(), &finalized[..finalized.len() - 1]);
			assert_eq!(notif.hash, *finalized.last().unwrap());
			assert_eq!(stale_heads, stale_heads_expected);
		},
		Ok(None) => panic!("unexpected notification result, client send channel was closed"),
		Err(_) => assert!(finalized.is_empty()),
	}
}

#[test]
fn construct_genesis_should_work_with_native() {
	let mut storage = GenesisConfig::new(
		vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
		vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
		1000,
		None,
		Default::default(),
	)
	.genesis_map();
	let genesis_hash = insert_genesis_block(&mut storage);

	let backend = InMemoryBackend::from((storage, StateVersion::default()));
	let (b1data, _b1hash) = block1(genesis_hash, &backend);
	let backend_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&backend);
	let runtime_code = backend_runtime_code.runtime_code().expect("Code is part of the backend");

	let mut overlay = OverlayedChanges::default();

	let _ = StateMachine::new(
		&backend,
		&mut overlay,
		&executor(),
		"Core_execute_block",
		&b1data,
		Default::default(),
		&runtime_code,
		TaskExecutor::new(),
	)
	.execute(ExecutionStrategy::NativeElseWasm)
	.unwrap();
}

#[test]
fn construct_genesis_should_work_with_wasm() {
	let mut storage = GenesisConfig::new(
		vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
		vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
		1000,
		None,
		Default::default(),
	)
	.genesis_map();
	let genesis_hash = insert_genesis_block(&mut storage);

	let backend = InMemoryBackend::from((storage, StateVersion::default()));
	let (b1data, _b1hash) = block1(genesis_hash, &backend);
	let backend_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&backend);
	let runtime_code = backend_runtime_code.runtime_code().expect("Code is part of the backend");

	let mut overlay = OverlayedChanges::default();

	let _ = StateMachine::new(
		&backend,
		&mut overlay,
		&executor(),
		"Core_execute_block",
		&b1data,
		Default::default(),
		&runtime_code,
		TaskExecutor::new(),
	)
	.execute(ExecutionStrategy::AlwaysWasm)
	.unwrap();
}

#[test]
fn construct_genesis_with_bad_transaction_should_panic() {
	let mut storage = GenesisConfig::new(
		vec![Sr25519Keyring::One.public().into(), Sr25519Keyring::Two.public().into()],
		vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
		68,
		None,
		Default::default(),
	)
	.genesis_map();
	let genesis_hash = insert_genesis_block(&mut storage);

	let backend = InMemoryBackend::from((storage, StateVersion::default()));
	let (b1data, _b1hash) = block1(genesis_hash, &backend);
	let backend_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&backend);
	let runtime_code = backend_runtime_code.runtime_code().expect("Code is part of the backend");

	let mut overlay = OverlayedChanges::default();

	let r = StateMachine::new(
		&backend,
		&mut overlay,
		&executor(),
		"Core_execute_block",
		&b1data,
		Default::default(),
		&runtime_code,
		TaskExecutor::new(),
	)
	.execute(ExecutionStrategy::NativeElseWasm);
	assert!(r.is_err());
}

#[test]
fn client_initializes_from_genesis_ok() {
	let client = substrate_test_runtime_client::new();

	assert_eq!(
		client
			.runtime_api()
			.balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Alice.into(),
			)
			.unwrap(),
		1000
	);
	assert_eq!(
		client
			.runtime_api()
			.balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Ferdie.into(),
			)
			.unwrap(),
		0
	);
}

#[test]
fn block_builder_works_with_no_transactions() {
	let mut client = substrate_test_runtime_client::new();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;

	block_on(client.import(BlockOrigin::Own, block)).unwrap();

	assert_eq!(client.chain_info().best_number, 1);
}

#[test]
fn block_builder_works_with_transactions() {
	let mut client = substrate_test_runtime_client::new();

	let mut builder = client.new_block(Default::default()).unwrap();

	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		})
		.unwrap();

	let block = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, block)).unwrap();

	let hash0 = client
		.expect_block_hash_from_id(&BlockId::Number(0))
		.expect("block 0 was just imported. qed");
	let hash1 = client
		.expect_block_hash_from_id(&BlockId::Number(1))
		.expect("block 1 was just imported. qed");

	assert_eq!(client.chain_info().best_number, 1);
	assert_ne!(client.state_at(&hash1).unwrap().pairs(), client.state_at(&hash0).unwrap().pairs());
	assert_eq!(
		client
			.runtime_api()
			.balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Alice.into(),
			)
			.unwrap(),
		958
	);
	assert_eq!(
		client
			.runtime_api()
			.balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Ferdie.into(),
			)
			.unwrap(),
		42
	);
}

#[test]
fn block_builder_does_not_include_invalid() {
	let mut client = substrate_test_runtime_client::new();

	let mut builder = client.new_block(Default::default()).unwrap();

	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		})
		.unwrap();

	assert!(builder
		.push_transfer(Transfer {
			from: AccountKeyring::Eve.into(),
			to: AccountKeyring::Alice.into(),
			amount: 42,
			nonce: 0,
		})
		.is_err());

	let block = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, block)).unwrap();

	let hash0 = client
		.expect_block_hash_from_id(&BlockId::Number(0))
		.expect("block 0 was just imported. qed");
	let hash1 = client
		.expect_block_hash_from_id(&BlockId::Number(1))
		.expect("block 1 was just imported. qed");

	assert_eq!(client.chain_info().best_number, 1);
	assert_ne!(client.state_at(&hash1).unwrap().pairs(), client.state_at(&hash0).unwrap().pairs());
	assert_eq!(client.body(&BlockId::Number(1)).unwrap().unwrap().len(), 1)
}

#[test]
fn best_containing_with_genesis_block() {
	// block tree:
	// G

	let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

	let genesis_hash = client.chain_info().genesis_hash;

	assert_eq!(
		genesis_hash.clone(),
		block_on(longest_chain_select.finality_target(genesis_hash, None)).unwrap(),
	);
}

#[test]
fn uncles_with_only_ancestors() {
	// block tree:
	// G -> A1 -> A2
	let mut client = substrate_test_runtime_client::new();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();
	let v: Vec<H256> = Vec::new();
	assert_eq!(v, client.uncles(a2.hash(), 3).unwrap());
}

#[test]
fn uncles_with_multiple_forks() {
	// block tree:
	// G -> A1 -> A2 -> A3 -> A4 -> A5
	//      A1 -> B2 -> B3 -> B4
	//	          B2 -> C3
	//	    A1 -> D2
	let mut client = substrate_test_runtime_client::new();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	// A2 -> A3
	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a3.clone())).unwrap();

	// A3 -> A4
	let a4 = client
		.new_block_at(&BlockId::Hash(a3.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a4.clone())).unwrap();

	// A4 -> A5
	let a5 = client
		.new_block_at(&BlockId::Hash(a4.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a5.clone())).unwrap();

	// A1 -> B2
	let mut builder = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise B2 has the same hash as A2 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let b2 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, b2.clone())).unwrap();

	// B2 -> B3
	let b3 = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b3.clone())).unwrap();

	// B3 -> B4
	let b4 = client
		.new_block_at(&BlockId::Hash(b3.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b4.clone())).unwrap();

	// // B2 -> C3
	let mut builder = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise C3 has the same hash as B3 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		})
		.unwrap();
	let c3 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, c3.clone())).unwrap();

	// A1 -> D2
	let mut builder = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise D2 has the same hash as B2 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		})
		.unwrap();
	let d2 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, d2.clone())).unwrap();

	let genesis_hash = client.chain_info().genesis_hash;

	let uncles1 = client.uncles(a4.hash(), 10).unwrap();
	assert_eq!(vec![b2.hash(), d2.hash()], uncles1);

	let uncles2 = client.uncles(a4.hash(), 0).unwrap();
	assert_eq!(0, uncles2.len());

	let uncles3 = client.uncles(a1.hash(), 10).unwrap();
	assert_eq!(0, uncles3.len());

	let uncles4 = client.uncles(genesis_hash, 10).unwrap();
	assert_eq!(0, uncles4.len());

	let uncles5 = client.uncles(d2.hash(), 10).unwrap();
	assert_eq!(vec![a2.hash(), b2.hash()], uncles5);

	let uncles6 = client.uncles(b3.hash(), 1).unwrap();
	assert_eq!(vec![c3.hash()], uncles6);
}

#[test]
fn best_containing_on_longest_chain_with_single_chain_3_blocks() {
	// block tree:
	// G -> A1 -> A2

	let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let genesis_hash = client.chain_info().genesis_hash;

	assert_eq!(
		a2.hash(),
		block_on(longest_chain_select.finality_target(genesis_hash, None)).unwrap()
	);
	assert_eq!(a2.hash(), block_on(longest_chain_select.finality_target(a1.hash(), None)).unwrap());
	assert_eq!(a2.hash(), block_on(longest_chain_select.finality_target(a2.hash(), None)).unwrap());
}

#[test]
fn best_containing_on_longest_chain_with_multiple_forks() {
	// block tree:
	// G -> A1 -> A2 -> A3 -> A4 -> A5
	//      A1 -> B2 -> B3 -> B4
	// 	          B2 -> C3
	// 	    A1 -> D2
	let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	// A2 -> A3
	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a3.clone())).unwrap();

	// A3 -> A4
	let a4 = client
		.new_block_at(&BlockId::Hash(a3.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a4.clone())).unwrap();

	// A4 -> A5
	let a5 = client
		.new_block_at(&BlockId::Hash(a4.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a5.clone())).unwrap();

	// A1 -> B2
	let mut builder = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise B2 has the same hash as A2 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let b2 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, b2.clone())).unwrap();

	// B2 -> B3
	let b3 = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b3.clone())).unwrap();

	// B3 -> B4
	let b4 = client
		.new_block_at(&BlockId::Hash(b3.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b4.clone())).unwrap();

	// B2 -> C3
	let mut builder = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise C3 has the same hash as B3 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		})
		.unwrap();
	let c3 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, c3.clone())).unwrap();

	// A1 -> D2
	let mut builder = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap();
	// this push is required as otherwise D2 has the same hash as B2 and won't get imported
	builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		})
		.unwrap();
	let d2 = builder.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, d2.clone())).unwrap();

	assert_eq!(client.chain_info().best_hash, a5.hash());

	let genesis_hash = client.chain_info().genesis_hash;
	let leaves = block_on(longest_chain_select.leaves()).unwrap();

	assert!(leaves.contains(&a5.hash()));
	assert!(leaves.contains(&b4.hash()));
	assert!(leaves.contains(&c3.hash()));
	assert!(leaves.contains(&d2.hash()));
	assert_eq!(leaves.len(), 4);

	let finality_target = |target_hash, number| {
		block_on(longest_chain_select.finality_target(target_hash, number)).unwrap()
	};

	// search without restriction
	assert_eq!(a5.hash(), finality_target(genesis_hash, None));
	assert_eq!(a5.hash(), finality_target(a1.hash(), None));
	assert_eq!(a5.hash(), finality_target(a2.hash(), None));
	assert_eq!(a5.hash(), finality_target(a3.hash(), None));
	assert_eq!(a5.hash(), finality_target(a4.hash(), None));
	assert_eq!(a5.hash(), finality_target(a5.hash(), None));
	assert_eq!(b4.hash(), finality_target(b2.hash(), None));
	assert_eq!(b4.hash(), finality_target(b3.hash(), None));
	assert_eq!(b4.hash(), finality_target(b4.hash(), None));
	assert_eq!(c3.hash(), finality_target(c3.hash(), None));
	assert_eq!(d2.hash(), finality_target(d2.hash(), None));

	// search only blocks with number <= 5. equivalent to without restriction for this scenario
	assert_eq!(a5.hash(), finality_target(genesis_hash, Some(5)));
	assert_eq!(a5.hash(), finality_target(a1.hash(), Some(5)));
	assert_eq!(a5.hash(), finality_target(a2.hash(), Some(5)));
	assert_eq!(a5.hash(), finality_target(a3.hash(), Some(5)));
	assert_eq!(a5.hash(), finality_target(a4.hash(), Some(5)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(5)));
	assert_eq!(b4.hash(), finality_target(b2.hash(), Some(5)));
	assert_eq!(b4.hash(), finality_target(b3.hash(), Some(5)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(5)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(5)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(5)));

	// search only blocks with number <= 4
	assert_eq!(a4.hash(), finality_target(genesis_hash, Some(4)));
	assert_eq!(a4.hash(), finality_target(a1.hash(), Some(4)));
	assert_eq!(a4.hash(), finality_target(a2.hash(), Some(4)));
	assert_eq!(a4.hash(), finality_target(a3.hash(), Some(4)));
	assert_eq!(a4.hash(), finality_target(a4.hash(), Some(4)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(4)));
	assert_eq!(b4.hash(), finality_target(b2.hash(), Some(4)));
	assert_eq!(b4.hash(), finality_target(b3.hash(), Some(4)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(4)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(4)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(4)));

	// search only blocks with number <= 3
	assert_eq!(a3.hash(), finality_target(genesis_hash, Some(3)));
	assert_eq!(a3.hash(), finality_target(a1.hash(), Some(3)));
	assert_eq!(a3.hash(), finality_target(a2.hash(), Some(3)));
	assert_eq!(a3.hash(), finality_target(a3.hash(), Some(3)));
	assert_eq!(a4.hash(), finality_target(a4.hash(), Some(3)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(3)));
	assert_eq!(b3.hash(), finality_target(b2.hash(), Some(3)));
	assert_eq!(b3.hash(), finality_target(b3.hash(), Some(3)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(3)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(3)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(3)));

	// search only blocks with number <= 2
	assert_eq!(a2.hash(), finality_target(genesis_hash, Some(2)));
	assert_eq!(a2.hash(), finality_target(a1.hash(), Some(2)));
	assert_eq!(a2.hash(), finality_target(a2.hash(), Some(2)));
	assert_eq!(a3.hash(), finality_target(a3.hash(), Some(2)));
	assert_eq!(a4.hash(), finality_target(a4.hash(), Some(2)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(2)));
	assert_eq!(b2.hash(), finality_target(b2.hash(), Some(2)));
	assert_eq!(b3.hash(), finality_target(b3.hash(), Some(2)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(2)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(2)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(2)));

	// search only blocks with number <= 1
	assert_eq!(a1.hash(), finality_target(genesis_hash, Some(1)));
	assert_eq!(a1.hash(), finality_target(a1.hash(), Some(1)));
	assert_eq!(a2.hash(), finality_target(a2.hash(), Some(1)));
	assert_eq!(a3.hash(), finality_target(a3.hash(), Some(1)));
	assert_eq!(a4.hash(), finality_target(a4.hash(), Some(1)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(1)));

	assert_eq!(b2.hash(), finality_target(b2.hash(), Some(1)));
	assert_eq!(b3.hash(), finality_target(b3.hash(), Some(1)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(1)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(1)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(1)));

	// search only blocks with number <= 0
	assert_eq!(genesis_hash, finality_target(genesis_hash, Some(0)));
	assert_eq!(a1.hash(), finality_target(a1.hash(), Some(0)));
	assert_eq!(a2.hash(), finality_target(a2.hash(), Some(0)));
	assert_eq!(a3.hash(), finality_target(a3.hash(), Some(0)));
	assert_eq!(a4.hash(), finality_target(a4.hash(), Some(0)));
	assert_eq!(a5.hash(), finality_target(a5.hash(), Some(0)));
	assert_eq!(b2.hash(), finality_target(b2.hash(), Some(0)));
	assert_eq!(b3.hash(), finality_target(b3.hash(), Some(0)));
	assert_eq!(b4.hash(), finality_target(b4.hash(), Some(0)));
	assert_eq!(c3.hash(), finality_target(c3.hash(), Some(0)));
	assert_eq!(d2.hash(), finality_target(d2.hash(), Some(0)));
}

#[test]
fn best_containing_on_longest_chain_with_max_depth_higher_than_best() {
	// block tree:
	// G -> A1 -> A2

	let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let genesis_hash = client.chain_info().genesis_hash;

	assert_eq!(
		a2.hash(),
		block_on(longest_chain_select.finality_target(genesis_hash, Some(10))).unwrap(),
	);
}

#[test]
fn import_with_justification() {
	// block tree:
	// G -> A1 -> A2 -> A3
	let mut client = substrate_test_runtime_client::new();

	let mut finality_notifications = client.finality_notification_stream();

	// G -> A1
	let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	// A1 -> A2
	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();
	client.finalize_block(BlockId::hash(a2.hash()), None).unwrap();

	// A2 -> A3
	let justification = Justifications::from((TEST_ENGINE_ID, vec![1, 2, 3]));
	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import_justified(BlockOrigin::Own, a3.clone(), justification.clone())).unwrap();

	assert_eq!(client.chain_info().finalized_hash, a3.hash());

	assert_eq!(client.justifications(&BlockId::Hash(a3.hash())).unwrap(), Some(justification));

	assert_eq!(client.justifications(&BlockId::Hash(a1.hash())).unwrap(), None);

	assert_eq!(client.justifications(&BlockId::Hash(a2.hash())).unwrap(), None);

	finality_notification_check(&mut finality_notifications, &[a1.hash(), a2.hash()], &[]);
	finality_notification_check(&mut finality_notifications, &[a3.hash()], &[]);
	assert!(finality_notifications.try_next().is_err());
}

#[test]
fn importing_diverged_finalized_block_should_trigger_reorg() {
	let mut client = substrate_test_runtime_client::new();

	// G -> A1 -> A2
	//   \
	//    -> B1

	let mut finality_notifications = client.finality_notification_stream();

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	// needed to make sure B1 gets a different hash from A1
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	// create but don't import B1 just yet
	let b1 = b1.build().unwrap().block;

	// A2 is the current best since it's the longest chain
	assert_eq!(client.chain_info().best_hash, a2.hash());

	// importing B1 as finalized should trigger a re-org and set it as new best
	let justification = Justifications::from((TEST_ENGINE_ID, vec![1, 2, 3]));
	block_on(client.import_justified(BlockOrigin::Own, b1.clone(), justification)).unwrap();

	assert_eq!(client.chain_info().best_hash, b1.hash());

	assert_eq!(client.chain_info().finalized_hash, b1.hash());

	finality_notification_check(&mut finality_notifications, &[b1.hash()], &[a2.hash()]);
	assert!(finality_notifications.try_next().is_err());
}

#[test]
fn finalizing_diverged_block_should_trigger_reorg() {
	let (mut client, select_chain) = TestClientBuilder::new().build_with_longest_chain();

	// G -> A1 -> A2
	//   \
	//    -> B1 -> B2

	let mut finality_notifications = client.finality_notification_stream();

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	// needed to make sure B1 gets a different hash from A1
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, b1.clone())).unwrap();

	let b2 = client
		.new_block_at(&BlockId::Hash(b1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b2.clone())).unwrap();

	// A2 is the current best since it's the longest chain
	assert_eq!(client.chain_info().best_hash, a2.hash());

	// we finalize block B1 which is on a different branch from current best
	// which should trigger a re-org.
	ClientExt::finalize_block(&client, BlockId::Hash(b1.hash()), None).unwrap();

	// B1 should now be the latest finalized
	assert_eq!(client.chain_info().finalized_hash, b1.hash());

	// and B1 should be the new best block (`finalize_block` as no way of
	// knowing about B2)
	assert_eq!(client.chain_info().best_hash, b1.hash());

	// `SelectChain` should report B2 as best block though
	assert_eq!(block_on(select_chain.best_chain()).unwrap().hash(), b2.hash());

	// after we build B3 on top of B2 and import it
	// it should be the new best block,
	let b3 = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b3.clone())).unwrap();

	assert_eq!(client.chain_info().best_hash, b3.hash());

	ClientExt::finalize_block(&client, BlockId::Hash(b3.hash()), None).unwrap();

	finality_notification_check(&mut finality_notifications, &[b1.hash()], &[]);
	finality_notification_check(&mut finality_notifications, &[b2.hash(), b3.hash()], &[a2.hash()]);
	assert!(finality_notifications.try_next().is_err());
}

#[test]
fn finality_notifications_content() {
	sp_tracing::try_init_simple();
	let (mut client, _select_chain) = TestClientBuilder::new().build_with_longest_chain();

	//               -> D3 -> D4
	// G -> A1 -> A2 -> A3
	//   -> B1 -> B2
	//   -> C1

	let mut finality_notifications = client.finality_notification_stream();

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a3.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	// needed to make sure B1 gets a different hash from A1
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, b1.clone())).unwrap();

	let b2 = client
		.new_block_at(&BlockId::Hash(b1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b2.clone())).unwrap();

	let mut c1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	// needed to make sure B1 gets a different hash from A1
	c1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 2,
		nonce: 0,
	})
	.unwrap();
	let c1 = c1.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, c1.clone())).unwrap();

	let mut d3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap();
	// needed to make sure D3 gets a different hash from A3
	d3.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 2,
		nonce: 0,
	})
	.unwrap();
	let d3 = d3.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, d3.clone())).unwrap();

	let d4 = client
		.new_block_at(&BlockId::Hash(d3.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;

	// Postpone import to test behavior of import of finalized block.

	ClientExt::finalize_block(&client, BlockId::Hash(a2.hash()), None).unwrap();

	// Import and finalize D4
	block_on(client.import_as_final(BlockOrigin::Own, d4.clone())).unwrap();

	finality_notification_check(&mut finality_notifications, &[a1.hash(), a2.hash()], &[c1.hash()]);
	finality_notification_check(&mut finality_notifications, &[d3.hash(), d4.hash()], &[b2.hash()]);
	assert!(finality_notifications.try_next().is_err());
}

#[test]
fn get_header_by_block_number_doesnt_panic() {
	let client = substrate_test_runtime_client::new();

	// backend uses u32 for block numbers, make sure we don't panic when
	// trying to convert
	let id = BlockId::<Block>::Number(72340207214430721);
	client.header(&id).expect_err("invalid block number overflows u32");
}

#[test]
fn state_reverted_on_reorg() {
	sp_tracing::try_init_simple();
	let mut client = substrate_test_runtime_client::new();

	let current_balance = |client: &substrate_test_runtime_client::TestClient| {
		client
			.runtime_api()
			.balance_of(
				&BlockId::number(client.chain_info().best_number),
				AccountKeyring::Alice.into(),
			)
			.unwrap()
	};

	// G -> A1 -> A2
	//   \
	//    -> B1
	let mut a1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	a1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Bob.into(),
		amount: 10,
		nonce: 0,
	})
	.unwrap();
	let a1 = a1.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 50,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;
	// Reorg to B1
	block_on(client.import_as_best(BlockOrigin::Own, b1.clone())).unwrap();

	assert_eq!(950, current_balance(&client));
	let mut a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap();
	a2.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Charlie.into(),
		amount: 10,
		nonce: 1,
	})
	.unwrap();
	let a2 = a2.build().unwrap().block;
	// Re-org to A2
	block_on(client.import_as_best(BlockOrigin::Own, a2)).unwrap();
	assert_eq!(980, current_balance(&client));
}

#[test]
fn doesnt_import_blocks_that_revert_finality() {
	sp_tracing::try_init_simple();
	let tmp = tempfile::tempdir().unwrap();

	// we need to run with archive pruning to avoid pruning non-canonical
	// states
	let backend = Arc::new(
		Backend::new(
			DatabaseSettings {
				trie_cache_maximum_size: Some(1 << 20),
				state_pruning: Some(PruningMode::ArchiveAll),
				blocks_pruning: BlocksPruning::KeepAll,
				source: DatabaseSource::RocksDb { path: tmp.path().into(), cache_size: 1024 },
			},
			u64::MAX,
		)
		.unwrap(),
	);

	let mut client = TestClientBuilder::with_backend(backend).build();

	let mut finality_notifications = client.finality_notification_stream();

	//    -> C1
	//   /
	// G -> A1 -> A2 -> A3
	//   \
	//    -> B1 -> B2 -> B3

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a1.clone())).unwrap();

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a2.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

	// needed to make sure B1 gets a different hash from A1
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;
	block_on(client.import(BlockOrigin::Own, b1.clone())).unwrap();

	let b2 = client
		.new_block_at(&BlockId::Hash(b1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, b2.clone())).unwrap();

	// prepare B3 before we finalize A2, because otherwise we won't be able to
	// read changes trie configuration after A2 is finalized
	let b3 = client
		.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;

	// we will finalize A2 which should make it impossible to import a new
	// B3 at the same height but that doesn't include it
	ClientExt::finalize_block(&client, BlockId::Hash(a2.hash()), None).unwrap();

	let import_err = block_on(client.import(BlockOrigin::Own, b3)).err().unwrap();
	let expected_err =
		ConsensusError::ClientImport(sp_blockchain::Error::NotInFinalizedChain.to_string());

	assert_eq!(import_err.to_string(), expected_err.to_string());

	// adding a C1 block which is lower than the last finalized should also
	// fail (with a cheaper check that doesn't require checking ancestry).
	let mut c1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

	// needed to make sure C1 gets a different hash from A1 and B1
	c1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 2,
		nonce: 0,
	})
	.unwrap();
	let c1 = c1.build().unwrap().block;

	let import_err = block_on(client.import(BlockOrigin::Own, c1)).err().unwrap();
	let expected_err =
		ConsensusError::ClientImport(sp_blockchain::Error::NotInFinalizedChain.to_string());

	assert_eq!(import_err.to_string(), expected_err.to_string());

	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::Own, a3.clone())).unwrap();
	ClientExt::finalize_block(&client, BlockId::Hash(a3.hash()), None).unwrap();

	finality_notification_check(&mut finality_notifications, &[a1.hash(), a2.hash()], &[]);

	finality_notification_check(&mut finality_notifications, &[a3.hash()], &[b2.hash()]);

	assert!(finality_notifications.try_next().is_err());
}

#[test]
fn respects_block_rules() {
	fn run_test(
		record_only: bool,
		known_bad: &mut HashSet<H256>,
		fork_rules: &mut Vec<(u64, H256)>,
	) {
		let mut client = if record_only {
			TestClientBuilder::new().build()
		} else {
			TestClientBuilder::new()
				.set_block_rules(Some(fork_rules.clone()), Some(known_bad.clone()))
				.build()
		};

		let block_ok = client
			.new_block_at(&BlockId::Number(0), Default::default(), false)
			.unwrap()
			.build()
			.unwrap()
			.block;

		let params = BlockCheckParams {
			hash: block_ok.hash(),
			number: 0,
			parent_hash: *block_ok.header().parent_hash(),
			allow_missing_state: false,
			allow_missing_parent: false,
			import_existing: false,
		};
		assert_eq!(block_on(client.check_block(params)).unwrap(), ImportResult::imported(false));

		// this is 0x0d6d6612a10485370d9e085aeea7ec427fb3f34d961c6a816cdbe5cde2278864
		let mut block_not_ok =
			client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
		block_not_ok.push_storage_change(vec![0], Some(vec![1])).unwrap();
		let block_not_ok = block_not_ok.build().unwrap().block;

		let params = BlockCheckParams {
			hash: block_not_ok.hash(),
			number: 0,
			parent_hash: *block_not_ok.header().parent_hash(),
			allow_missing_state: false,
			allow_missing_parent: false,
			import_existing: false,
		};
		if record_only {
			known_bad.insert(block_not_ok.hash());
		} else {
			assert_eq!(block_on(client.check_block(params)).unwrap(), ImportResult::KnownBad);
		}

		// Now going to the fork
		block_on(client.import_as_final(BlockOrigin::Own, block_ok)).unwrap();

		// And check good fork
		let mut block_ok =
			client.new_block_at(&BlockId::Number(1), Default::default(), false).unwrap();
		block_ok.push_storage_change(vec![0], Some(vec![2])).unwrap();
		let block_ok = block_ok.build().unwrap().block;

		let params = BlockCheckParams {
			hash: block_ok.hash(),
			number: 1,
			parent_hash: *block_ok.header().parent_hash(),
			allow_missing_state: false,
			allow_missing_parent: false,
			import_existing: false,
		};
		if record_only {
			fork_rules.push((1, block_ok.hash()));
		}
		assert_eq!(block_on(client.check_block(params)).unwrap(), ImportResult::imported(false));

		// And now try bad fork
		let mut block_not_ok =
			client.new_block_at(&BlockId::Number(1), Default::default(), false).unwrap();
		block_not_ok.push_storage_change(vec![0], Some(vec![3])).unwrap();
		let block_not_ok = block_not_ok.build().unwrap().block;

		let params = BlockCheckParams {
			hash: block_not_ok.hash(),
			number: 1,
			parent_hash: *block_not_ok.header().parent_hash(),
			allow_missing_state: false,
			allow_missing_parent: false,
			import_existing: false,
		};

		if !record_only {
			assert_eq!(block_on(client.check_block(params)).unwrap(), ImportResult::KnownBad);
		}
	}

	let mut known_bad = HashSet::new();
	let mut fork_rules = Vec::new();

	// records what bad_blocks and fork_blocks hashes should be
	run_test(true, &mut known_bad, &mut fork_rules);

	// enforces rules and actually makes assertions
	run_test(false, &mut known_bad, &mut fork_rules);
}

#[test]
fn returns_status_for_pruned_blocks() {
	sp_tracing::try_init_simple();
	let tmp = tempfile::tempdir().unwrap();

	// set to prune after 1 block
	// states
	let backend = Arc::new(
		Backend::new(
			DatabaseSettings {
				trie_cache_maximum_size: Some(1 << 20),
				state_pruning: Some(PruningMode::blocks_pruning(1)),
				blocks_pruning: BlocksPruning::KeepFinalized,
				source: DatabaseSource::RocksDb { path: tmp.path().into(), cache_size: 1024 },
			},
			u64::MAX,
		)
		.unwrap(),
	);

	let mut client = TestClientBuilder::with_backend(backend).build();

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

	// b1 is created, but not imported
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;

	let check_block_a1 = BlockCheckParams {
		hash: a1.hash(),
		number: 0,
		parent_hash: *a1.header().parent_hash(),
		allow_missing_state: false,
		allow_missing_parent: false,
		import_existing: false,
	};

	assert_eq!(
		block_on(client.check_block(check_block_a1.clone())).unwrap(),
		ImportResult::imported(false),
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(),
		BlockStatus::Unknown,
	);

	block_on(client.import_as_final(BlockOrigin::Own, a1.clone())).unwrap();

	assert_eq!(
		block_on(client.check_block(check_block_a1.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(),
		BlockStatus::InChainWithState,
	);

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import_as_final(BlockOrigin::Own, a2.clone())).unwrap();

	let check_block_a2 = BlockCheckParams {
		hash: a2.hash(),
		number: 1,
		parent_hash: *a1.header().parent_hash(),
		allow_missing_state: false,
		allow_missing_parent: false,
		import_existing: false,
	};

	assert_eq!(
		block_on(client.check_block(check_block_a1.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(),
		BlockStatus::InChainPruned,
	);
	assert_eq!(
		block_on(client.check_block(check_block_a2.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a2.hash)).unwrap(),
		BlockStatus::InChainWithState,
	);

	let a3 = client
		.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;

	block_on(client.import_as_final(BlockOrigin::Own, a3.clone())).unwrap();
	let check_block_a3 = BlockCheckParams {
		hash: a3.hash(),
		number: 2,
		parent_hash: *a2.header().parent_hash(),
		allow_missing_state: false,
		allow_missing_parent: false,
		import_existing: false,
	};

	// a1 and a2 are both pruned at this point
	assert_eq!(
		block_on(client.check_block(check_block_a1.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(),
		BlockStatus::InChainPruned,
	);
	assert_eq!(
		block_on(client.check_block(check_block_a2.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a2.hash)).unwrap(),
		BlockStatus::InChainPruned,
	);
	assert_eq!(
		block_on(client.check_block(check_block_a3.clone())).unwrap(),
		ImportResult::AlreadyInChain,
	);
	assert_eq!(
		client.block_status(&BlockId::hash(check_block_a3.hash)).unwrap(),
		BlockStatus::InChainWithState,
	);

	let mut check_block_b1 = BlockCheckParams {
		hash: b1.hash(),
		number: 0,
		parent_hash: *b1.header().parent_hash(),
		allow_missing_state: false,
		allow_missing_parent: false,
		import_existing: false,
	};
	assert_eq!(
		block_on(client.check_block(check_block_b1.clone())).unwrap(),
		ImportResult::MissingState,
	);
	check_block_b1.allow_missing_state = true;
	assert_eq!(
		block_on(client.check_block(check_block_b1.clone())).unwrap(),
		ImportResult::imported(false),
	);
	check_block_b1.parent_hash = H256::random();
	assert_eq!(
		block_on(client.check_block(check_block_b1.clone())).unwrap(),
		ImportResult::UnknownParent,
	);
}

#[test]
fn storage_keys_iter_prefix_and_start_key_works() {
	let child_info = ChildInfo::new_default(b"child");
	let client = TestClientBuilder::new()
		.add_extra_child_storage(&child_info, b"first".to_vec(), vec![0u8; 32])
		.add_extra_child_storage(&child_info, b"second".to_vec(), vec![0u8; 32])
		.add_extra_child_storage(&child_info, b"third".to_vec(), vec![0u8; 32])
		.build();

	let child_root = b":child_storage:default:child".to_vec();
	let prefix = StorageKey(array_bytes::hex2bytes_unchecked("3a"));
	let child_prefix = StorageKey(b"sec".to_vec());

	let res: Vec<_> = client
		.storage_keys_iter(&BlockId::Number(0), Some(&prefix), None)
		.unwrap()
		.map(|x| x.0)
		.collect();
	assert_eq!(
		res,
		[
			child_root.clone(),
			array_bytes::hex2bytes_unchecked("3a636f6465"),
			array_bytes::hex2bytes_unchecked("3a686561707061676573"),
		]
	);

	let res: Vec<_> = client
		.storage_keys_iter(
			&BlockId::Number(0),
			Some(&prefix),
			Some(&StorageKey(array_bytes::hex2bytes_unchecked("3a636f6465"))),
		)
		.unwrap()
		.map(|x| x.0)
		.collect();
	assert_eq!(res, [array_bytes::hex2bytes_unchecked("3a686561707061676573")]);

	let res: Vec<_> = client
		.storage_keys_iter(
			&BlockId::Number(0),
			Some(&prefix),
			Some(&StorageKey(array_bytes::hex2bytes_unchecked("3a686561707061676573"))),
		)
		.unwrap()
		.map(|x| x.0)
		.collect();
	assert_eq!(res, Vec::<Vec<u8>>::new());

	let res: Vec<_> = client
		.child_storage_keys_iter(&BlockId::Number(0), child_info.clone(), Some(&child_prefix), None)
		.unwrap()
		.map(|x| x.0)
		.collect();
	assert_eq!(res, [b"second".to_vec()]);

	let res: Vec<_> = client
		.child_storage_keys_iter(
			&BlockId::Number(0),
			child_info,
			None,
			Some(&StorageKey(b"second".to_vec())),
		)
		.unwrap()
		.map(|x| x.0)
		.collect();
	assert_eq!(res, [b"third".to_vec()]);
}

#[test]
fn storage_keys_iter_works() {
	let client = substrate_test_runtime_client::new();

	let prefix = StorageKey(array_bytes::hex2bytes_unchecked(""));

	let res: Vec<_> = client
		.storage_keys_iter(&BlockId::Number(0), Some(&prefix), None)
		.unwrap()
		.take(9)
		.map(|x| array_bytes::bytes2hex("", &x.0))
		.collect();
	assert_eq!(
		res,
		[
			"00c232cf4e70a5e343317016dc805bf80a6a8cd8ad39958d56f99891b07851e0",
			"085b2407916e53a86efeb8b72dbe338c4b341dab135252f96b6ed8022209b6cb",
			"0befda6e1ca4ef40219d588a727f1271",
			"1a560ecfd2a62c2b8521ef149d0804eb621050e3988ed97dca55f0d7c3e6aa34",
			"1d66850d32002979d67dd29dc583af5b2ae2a1f71c1f35ad90fff122be7a3824",
			"237498b98d8803334286e9f0483ef513098dd3c1c22ca21c4dc155b4ef6cc204",
			"26aa394eea5630e07c48ae0c9558cef75e0621c4869aa60c02be9adcc98a0d1d",
			"29b9db10ec5bf7907d8f74b5e60aa8140c4fbdd8127a1ee5600cb98e5ec01729",
			"3a636f6465",
		]
	);

	let res: Vec<_> = client
		.storage_keys_iter(
			&BlockId::Number(0),
			Some(&prefix),
			Some(&StorageKey(array_bytes::hex2bytes_unchecked("3a636f6465"))),
		)
		.unwrap()
		.take(7)
		.map(|x| array_bytes::bytes2hex("", &x.0))
		.collect();
	assert_eq!(
		res,
		[
			"3a686561707061676573",
			"52008686cc27f6e5ed83a216929942f8bcd32a396f09664a5698f81371934b56",
			"5348d72ac6cc66e5d8cbecc27b0e0677503b845fe2382d819f83001781788fd5",
			"5c2d5fda66373dabf970e4fb13d277ce91c5233473321129d32b5a8085fa8133",
			"6644b9b8bc315888ac8e41a7968dc2b4141a5403c58acdf70b7e8f7e07bf5081",
			"66484000ed3f75c95fc7b03f39c20ca1e1011e5999278247d3b2f5e3c3273808",
			"7d5007603a7f5dd729d51d93cf695d6465789443bb967c0d1fe270e388c96eaa",
		]
	);

	let res: Vec<_> = client
		.storage_keys_iter(
			&BlockId::Number(0),
			Some(&prefix),
			Some(&StorageKey(array_bytes::hex2bytes_unchecked(
				"7d5007603a7f5dd729d51d93cf695d6465789443bb967c0d1fe270e388c96eaa",
			))),
		)
		.unwrap()
		.take(5)
		.map(|x| array_bytes::bytes2hex("", &x.0))
		.collect();
	assert_eq!(
		res,
		[
			"811ecfaadcf5f2ee1d67393247e2f71a1662d433e8ce7ff89fb0d4aa9561820b",
			"a93d74caa7ec34ea1b04ce1e5c090245f867d333f0f88278a451e45299654dc5",
			"a9ee1403384afbfc13f13be91ff70bfac057436212e53b9733914382ac942892",
			"cf722c0832b5231d35e29f319ff27389f5032bfc7bfc3ba5ed7839f2042fb99f",
			"e3b47b6c84c0493481f97c5197d2554f",
		]
	);
}

#[test]
fn cleans_up_closed_notification_sinks_on_block_import() {
	use substrate_test_runtime_client::GenesisInit;

	// NOTE: we need to build the client here instead of using the client
	// provided by test_runtime_client otherwise we can't access the private
	// `import_notification_sinks` and `finality_notification_sinks` fields.
	let mut client = new_in_mem::<_, Block, _, RuntimeApi>(
		substrate_test_runtime_client::new_native_executor(),
		&substrate_test_runtime_client::GenesisParameters::default().genesis_storage(),
		None,
		None,
		None,
		Box::new(TaskExecutor::new()),
		Default::default(),
	)
	.unwrap();

	type TestClient = Client<
		in_mem::Backend<Block>,
		LocalCallExecutor<
			Block,
			in_mem::Backend<Block>,
			sc_executor::NativeElseWasmExecutor<LocalExecutorDispatch>,
		>,
		Block,
		RuntimeApi,
	>;

	let import_notif1 = client.import_notification_stream();
	let import_notif2 = client.import_notification_stream();
	let finality_notif1 = client.finality_notification_stream();
	let finality_notif2 = client.finality_notification_stream();

	// for some reason I can't seem to use `ClientBlockImportExt`
	let bake_and_import_block = |client: &mut TestClient, origin| {
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;

		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		block_on(client.import_block(import, Default::default())).unwrap();
	};

	// after importing a block we should still have 4 notification sinks
	// (2 import + 2 finality)
	bake_and_import_block(&mut client, BlockOrigin::Own);
	assert_eq!(client.import_notification_sinks().lock().len(), 2);
	assert_eq!(client.finality_notification_sinks().lock().len(), 2);

	// if we drop one import notification receiver and one finality
	// notification receiver
	drop(import_notif2);
	drop(finality_notif2);

	// the sinks should be cleaned up after block import
	bake_and_import_block(&mut client, BlockOrigin::Own);
	assert_eq!(client.import_notification_sinks().lock().len(), 1);
	assert_eq!(client.finality_notification_sinks().lock().len(), 1);

	// the same thing should happen if block import happens during initial
	// sync
	drop(import_notif1);
	drop(finality_notif1);

	bake_and_import_block(&mut client, BlockOrigin::NetworkInitialSync);
	assert_eq!(client.import_notification_sinks().lock().len(), 0);
	assert_eq!(client.finality_notification_sinks().lock().len(), 0);
}

/// Test that ensures that we always send an import notification for re-orgs.
#[test]
fn reorg_triggers_a_notification_even_for_sources_that_should_not_trigger_notifications() {
	let mut client = TestClientBuilder::new().build();

	let mut notification_stream =
		futures::executor::block_on_stream(client.import_notification_stream());

	let a1 = client
		.new_block_at(&BlockId::Number(0), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::NetworkInitialSync, a1.clone())).unwrap();

	let a2 = client
		.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	block_on(client.import(BlockOrigin::NetworkInitialSync, a2.clone())).unwrap();

	let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();
	// needed to make sure B1 gets a different hash from A1
	b1.push_transfer(Transfer {
		from: AccountKeyring::Alice.into(),
		to: AccountKeyring::Ferdie.into(),
		amount: 1,
		nonce: 0,
	})
	.unwrap();
	let b1 = b1.build().unwrap().block;
	block_on(client.import(BlockOrigin::NetworkInitialSync, b1.clone())).unwrap();

	let b2 = client
		.new_block_at(&BlockId::Hash(b1.hash()), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;

	// Should trigger a notification because we reorg
	block_on(client.import_as_best(BlockOrigin::NetworkInitialSync, b2.clone())).unwrap();

	// There should be one notification
	let notification = notification_stream.next().unwrap();

	// We should have a tree route of the re-org
	let tree_route = notification.tree_route.unwrap();
	assert_eq!(tree_route.enacted()[0].hash, b1.hash());
}
