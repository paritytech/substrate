// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! A `CodeExecutor` specialisation which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

extern crate demo_runtime;
#[macro_use] extern crate substrate_executor;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate demo_primitives;
extern crate ed25519;
extern crate triehash;

#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] #[macro_use] extern crate hex_literal;

native_executor_instance!(pub Executor, demo_runtime::api::dispatch, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::WasmExecutor;
	use codec::{KeyedVec, Slicable, Joiner};
	use keyring::Keyring::{self, One, Two};
	use runtime_support::Hashable;
	use demo_runtime::runtime::staking::{self, balance, BALANCE_OF};
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use demo_primitives::{Hash, Header, BlockNumber, Block, Digest, Transaction,
		UncheckedTransaction, Function};
	use ed25519::{Public, Pair};

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn tx() -> UncheckedTransaction {
		let transaction = Transaction {
			signed: One.into(),
			nonce: 0,
			function: Function::StakingTransfer(Two.into(), 69),
		};
		let signature = Keyring::from_raw_public(transaction.signed).unwrap()
			.sign(&transaction.encode());

		UncheckedTransaction { transaction, signature }
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 42);
			assert_eq!(balance(&Two), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 42);
			assert_eq!(balance(&Two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		staking::testing::externalities(2, 2, 0)
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|transaction| {
			let signature = Pair::from(Keyring::from_public(Public::from_raw(transaction.signed)).unwrap())
				.sign(&transaction.encode());

			UncheckedTransaction { transaction, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::encode)).0.into();

		let header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		(Block { header, transactions }.encode(), hash.into())
	}

	fn block1() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("6f0202ee141932f5cf9efad76d9200ec0ae98e2782335c5c7940be6a66bb9418").into(),
			vec![Transaction {
				signed: One.into(),
				nonce: 0,
				function: Function::StakingTransfer(Two.into(), 69),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("04a2ca0ff5cdbe6a0ceb75009b4e707c8d052f28c95e9a7751ea814b13b95c92").into(),
			vec![
				Transaction {
					signed: Two.into(),
					nonce: 0,
					function: Function::StakingTransfer(One.into(), 5),
				},
				Transaction {
					signed: One.into(),
					nonce: 1,
					function: Function::StakingTransfer(Two.into(), 15),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 42);
			assert_eq!(balance(&Two), 69);
		});

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 32);
			assert_eq!(balance(&Two), 79);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 42);
			assert_eq!(balance(&Two), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 32);
			assert_eq!(balance(&Two), 79);
		});
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&One.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&One), 42);
			assert_eq!(balance(&Two), 69);
		});
	}
}
