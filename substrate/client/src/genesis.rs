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
	use runtime_support::{one, two, Hashable};
	use test_runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
	use executor::{NativeExecutionDispatch, NativeExecutor, WasmExecutor, with_native_environment,
		error};
	use state_machine::{execute, Externalities, OverlayedChanges};
	use state_machine::backend::InMemory;
	use test_runtime::{self, AccountId, Hash, Block, BlockNumber, Header, Digest, Transaction,
		UncheckedTransaction};
	use ed25519::Pair;

	/// A null struct which implements `NativeExecutionDispatch` feeding in the hard-coded runtime.
	pub struct LocalNativeExecutionDispatch;

	impl NativeExecutionDispatch for LocalNativeExecutionDispatch {
		fn native_equivalent() -> &'static [u8] {
			// WARNING!!! This assumes that the runtime was built *before* the main project. Until we
			// get a proper build script, this must be strictly adhered to or things will go wrong.
			include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm")
		}

		fn dispatch(ext: &mut Externalities, method: &str, data: &[u8]) -> error::Result<Vec<u8>> {
			with_native_environment(ext, move || test_runtime::apis::dispatch(method, data))?
				.ok_or_else(|| error::ErrorKind::MethodNotFound(method.to_owned()).into())
		}
	}

	fn executor() -> NativeExecutor<LocalNativeExecutionDispatch> {
		NativeExecutor { _dummy: Default::default() }
	}

	fn secret_for(who: &AccountId) -> Option<Pair> {
		match who {
			x if *x == one() => Some(Pair::from_seed(b"12345678901234567890123456789012")),
			x if *x == two() => Some("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60".into()),
			_ => None,
		}
	}

	fn construct_block(backend: &InMemory, number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|tx| {
			let signature = secret_for(&tx.from).unwrap()
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
				&executor(),
				"execute_transaction",
				&vec![].and(&header).and(tx)
			).unwrap();
			header = Header::decode(&mut &ret_data[..]).unwrap();
		}

		let ret_data = execute(
			backend,
			&mut overlay,
			&executor(),
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
				from: one(),
				to: two(),
				amount: 69,
				nonce: 0,
			}]
		)
	}

	#[test]
	fn construct_genesis_should_work() {
		let mut storage = GenesisConfig::new_simple(
			vec![one(), two()], 1000
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256().into();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let mut overlay = OverlayedChanges::default();
		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let _ = execute(
			&backend,
			&mut overlay,
			&executor(),
			"execute_block",
			&b1data
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn construct_genesis_with_bad_transaction_should_panic() {
		let mut storage = GenesisConfig::new_simple(
			vec![one(), two()], 68
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256().into();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let mut overlay = OverlayedChanges::default();
		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let _ = execute(
			&backend,
			&mut overlay,
			&executor(),
			"execute_block",
			&b1data
		).unwrap();
	}

	#[test]
	fn construct_genesis_should_work_under_wasm() {
		let mut storage = GenesisConfig::new_simple(
			vec![one(), two()], 1000
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256().into();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let mut overlay = OverlayedChanges::default();
		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash, &backend);

		let _ = execute(
			&backend,
			&mut overlay,
			&WasmExecutor,
			"execute_block",
			&b1data
		).unwrap();
	}
}
