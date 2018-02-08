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

//! A `CodeExecutor` specialisation which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

extern crate polkadot_runtime;
extern crate substrate_executor;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate polkadot_primitives as polkadot_primitives;
extern crate ed25519;
extern crate triehash;
#[cfg(test)]
#[macro_use]
extern crate hex_literal;

use polkadot_runtime as runtime;
use substrate_executor::{NativeExecutionDispatch, NativeExecutor};

/// A null struct which implements `NativeExecutionDispatch` feeding in the hard-coded runtime.
pub struct LocalNativeExecutionDispatch;

impl NativeExecutionDispatch for LocalNativeExecutionDispatch {
	fn native_equivalent() -> &'static [u8] {
		// WARNING!!! This assumes that the runtime was built *before* the main project. Until we
		// get a proper build script, this must be strictly adhered to or things will go wrong.
		include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm")
	}

	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
		runtime::dispatch(method, data)
	}
}

/// Creates new RustExecutor for contracts.
pub fn executor() -> NativeExecutor<LocalNativeExecutionDispatch> {
	NativeExecutor { _dummy: ::std::marker::PhantomData }
}

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::*;
	use substrate_executor::WasmExecutor;
	use codec::{KeyedVec, Slicable, Joiner};
	use polkadot_runtime::support::{one, two, Hashable};
	use polkadot_runtime::runtime::staking::balance;
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use polkadot_primitives::{Hash, Header, BlockNumber, Block, Digest, Transaction,
		UncheckedTransaction, Function, AccountId};
	use ed25519::Pair;

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn tx() -> UncheckedTransaction {
		let transaction = Transaction {
			signed: one(),
			nonce: 0,
			function: Function::StakingTransfer(two(), 69),
		};
		let signature = secret_for(&transaction.signed).unwrap()
			.sign(&transaction.to_vec());

		UncheckedTransaction { transaction, signature }
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let one = one();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = executor().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let one = one();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = executor().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = executor().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = executor().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		let one = one();
		let two = two();
		let three = [3u8; 32];

		TestExternalities { storage: map![
			twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => [69u8; 32].to_vec(),
			twox_128(b"gov:apr").to_vec() => vec![].join(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].join(&2u64),
			twox_128(b"ses:val:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].join(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].join(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].join(&0u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], }
	}

	fn secret_for(who: &AccountId) -> Option<Pair> {
		match who {
			x if *x == one() => Some(Pair::from_seed(b"12345678901234567890123456789012")),
			x if *x == two() => Some("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60".into()),
			_ => None,
		}
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|transaction| {
			let signature = secret_for(&transaction.signed).unwrap()
				.sign(&transaction.to_vec());

			UncheckedTransaction { transaction, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::to_vec)).0.into();

		let header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		(Block { header, transactions }.to_vec(), hash.into())
	}

	fn block1() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("2481853da20b9f4322f34650fea5f240dcbfb266d02db94bfa0153c31f4a29db").into(),
			vec![Transaction {
				signed: one(),
				nonce: 0,
				function: Function::StakingTransfer(two(), 69),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("1feb4d3a2e587079e6ce1685fa79994efd995e33cb289d39cded67aac1bb46a9").into(),
			vec![
				Transaction {
					signed: two(),
					nonce: 0,
					function: Function::StakingTransfer(one(), 5),
				},
				Transaction {
					signed: one(),
					nonce: 1,
					function: Function::StakingTransfer(two(), 15),
				}
			]
		)
	}

	#[test]
	fn test_execution_works() {
		let mut t = new_test_ext();
		println!("Testing Wasm...");
		let r = WasmExecutor.call(&mut t, COMPACT_CODE, "run_tests", &block2().0);
		assert!(r.is_ok());
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		executor().call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 42);
			assert_eq!(balance(&two()), 69);
		});

		executor().call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 32);
			assert_eq!(balance(&two()), 79);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 42);
			assert_eq!(balance(&two()), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 32);
			assert_eq!(balance(&two()), 79);
		});
	}

	#[test]
	fn panic_execution_gives_error() {
		let one = one();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_gives_ok() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].join(&Header::from_block_number(1u64)).join(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}
}
