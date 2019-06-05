// Copyright 2019 Parity Technologies (UK) Ltd.
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

use test_client::{
	AccountKeyring, runtime::{TestAPI, DecodeFails, Transfer, Header},
	NativeExecutor, LocalExecutor, TestClientBuilder
};
use runtime_primitives::{
	generic::BlockId,
	traits::{ProvideRuntimeApi, Header as HeaderT, Hash as HashT},
};
use state_machine::{
	ExecutionStrategy, create_proof_check_backend,
	execution_proof_check_on_trie_backend,
};

use consensus_common::SelectChain;
use codec::Encode;

fn calling_function_with_strat(strat: ExecutionStrategy) {
	let client = TestClientBuilder::new().set_execution_strategy(strat).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);

	assert_eq!(runtime_api.benchmark_add_one(&block_id, &1).unwrap(), 2);
}

#[test]
fn calling_native_runtime_function() {
	calling_function_with_strat(ExecutionStrategy::NativeWhenPossible);
}

#[test]
fn calling_wasm_runtime_function() {
	calling_function_with_strat(ExecutionStrategy::AlwaysWasm);
}

#[test]
#[should_panic(expected = "Could not convert parameter `param` between node and runtime!")]
fn calling_native_runtime_function_with_non_decodable_parameter() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::NativeWhenPossible).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	runtime_api.fail_convert_parameter(&block_id, DecodeFails::new()).unwrap();
}

#[test]
#[should_panic(expected = "Could not convert return value from runtime to node!")]
fn calling_native_runtime_function_with_non_decodable_return_value() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::NativeWhenPossible).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	runtime_api.fail_convert_return_value(&block_id).unwrap();
}

#[test]
fn calling_native_runtime_signature_changed_function() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::NativeWhenPossible).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);

	assert_eq!(runtime_api.function_signature_changed(&block_id).unwrap(), 1);
}

#[test]
fn calling_wasm_runtime_signature_changed_old_function() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);

	#[allow(deprecated)]
	let res = runtime_api.function_signature_changed_before_version_2(&block_id).unwrap();
	assert_eq!(&res, &[1, 2]);
}

#[test]
fn calling_with_both_strategy_and_fail_on_wasm_should_return_error() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert!(runtime_api.fail_on_wasm(&block_id).is_err());
}

#[test]
fn calling_with_both_strategy_and_fail_on_native_should_work() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.fail_on_native(&block_id).unwrap(), 1);
}


#[test]
fn calling_with_native_else_wasm_and_faild_on_wasm_should_work() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::NativeElseWasm).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.fail_on_wasm(&block_id).unwrap(), 1);
}

#[test]
fn calling_with_native_else_wasm_and_fail_on_native_should_work() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::NativeElseWasm).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.fail_on_native(&block_id).unwrap(), 1);
}

#[test]
fn use_trie_function() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.use_trie(&block_id).unwrap(), 2);
}

#[test]
fn initialize_block_works() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.get_block_number(&block_id).unwrap(), 1);
}

#[test]
fn initialize_block_is_called_only_once() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert_eq!(runtime_api.take_block_number(&block_id).unwrap(), Some(1));
	assert_eq!(runtime_api.take_block_number(&block_id).unwrap(), None);
}

#[test]
fn initialize_block_is_skipped() {
	let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
	let runtime_api = client.runtime_api();
	let block_id = BlockId::Number(client.info().chain.best_number);
	assert!(runtime_api.without_initialize_block(&block_id).unwrap());
}

#[test]
fn record_proof_works() {
	let (client, longest_chain) = TestClientBuilder::new()
		.set_execution_strategy(ExecutionStrategy::Both)
		.build_with_longest_chain();

	let block_id = BlockId::Number(client.info().chain.best_number);
	let storage_root = longest_chain.best_chain().unwrap().state_root().clone();

	let transaction = Transfer {
		amount: 1000,
		nonce: 0,
		from: AccountKeyring::Alice.into(),
		to: Default::default(),
	}.into_signed_tx();

	// Build the block and record proof
	let mut builder = client
		.new_block_at_with_proof_recording(&block_id, Default::default())
		.expect("Creates block builder");
	builder.push(transaction.clone()).unwrap();
	let (block, proof) = builder.bake_and_extract_proof().expect("Bake block");

	let backend = create_proof_check_backend::<<<Header as HeaderT>::Hashing as HashT>::Hasher>(
		storage_root,
		proof.expect("Proof was generated"),
	).expect("Creates proof backend.");

	// Use the proof backend to execute `execute_block`.
	let mut overlay = Default::default();
	let executor = NativeExecutor::<LocalExecutor>::new(None);
	execution_proof_check_on_trie_backend(
		&backend,
		&mut overlay,
		&executor,
		"Core_execute_block",
		&block.encode(),
	).expect("Executes block while using the proof backend");
}