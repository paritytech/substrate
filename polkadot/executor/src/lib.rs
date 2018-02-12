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
#[macro_use] extern crate substrate_executor;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate polkadot_primitives as polkadot_primitives;
extern crate ed25519;
extern crate triehash;

#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] #[macro_use] extern crate hex_literal;

native_executor_instance!(pub Executor, polkadot_runtime::api::dispatch, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::WasmExecutor;
	use codec::{KeyedVec, Slicable, Joiner};
	use keyring::Keyring;
	use runtime_support::Hashable;
	use polkadot_runtime::runtime::staking::balance;
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use polkadot_primitives::{Hash, Header, BlockNumber, Block, Digest, Transaction,
		UncheckedTransaction, Function};
	use ed25519::{Public, Pair};

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
			signed: Keyring::One.to_raw_public(),
			nonce: 0,
			function: Function::StakingTransfer(Keyring::Two.to_raw_public(), 69),
		};
		let signature = Keyring::from_raw_public(transaction.signed).unwrap()
			.sign(&transaction.encode());

		UncheckedTransaction { transaction, signature }
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let one = Keyring::One.to_raw_public();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let one = Keyring::One.to_raw_public();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];

		TestExternalities { storage: map![
			twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => [69u8; 32].encode(),
			twox_128(b"gov:apr").to_vec() => vec![].and(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].and(&2u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].and(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].and(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].and(&0u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], }
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
			hex!("2481853da20b9f4322f34650fea5f240dcbfb266d02db94bfa0153c31f4a29db").into(),
			vec![Transaction {
				signed: Keyring::One.to_raw_public(),
				nonce: 0,
				function: Function::StakingTransfer(Keyring::Two.to_raw_public(), 69),
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
					signed: Keyring::Two.to_raw_public(),
					nonce: 0,
					function: Function::StakingTransfer(Keyring::One.to_raw_public(), 5),
				},
				Transaction {
					signed: Keyring::One.to_raw_public(),
					nonce: 1,
					function: Function::StakingTransfer(Keyring::Two.to_raw_public(), 15),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Keyring::One.to_raw_public()), 42);
			assert_eq!(balance(&Keyring::Two.to_raw_public()), 69);
		});

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Keyring::One.to_raw_public()), 32);
			assert_eq!(balance(&Keyring::Two.to_raw_public()), 79);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Keyring::One.to_raw_public()), 42);
			assert_eq!(balance(&Keyring::Two.to_raw_public()), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Keyring::One.to_raw_public()), 32);
			assert_eq!(balance(&Keyring::Two.to_raw_public()), 79);
		});
	}

	#[test]
	fn panic_execution_gives_error() {
		let one = Keyring::One.to_raw_public();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_gives_ok() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&Header::from_block_number(1u64)).and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}
}
