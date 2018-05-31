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
#[cfg(test)] extern crate substrate_runtime_primitives as runtime_primitives;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] extern crate substrate_runtime_staking as staking;
#[cfg(test)] extern crate substrate_runtime_system as system;
#[cfg(test)] #[macro_use] extern crate hex_literal;

native_executor_instance!(pub Executor, demo_runtime::api::dispatch, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::WasmExecutor;
	use codec::{Slicable, Joiner};
	use keyring::Keyring::{self, Alice, Bob};
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use demo_primitives::{Hash, BlockNumber};
	use runtime_primitives::traits::Header as HeaderT;
	use {staking, system};
	use demo_runtime::{Header, Block, UncheckedExtrinsic, Extrinsic, Call, Concrete, Staking,
		BuildExternalities, GenesisConfig, SessionConfig, StakingConfig};
	use ed25519::{Public, Pair};

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn xt() -> UncheckedExtrinsic {
		let extrinsic = Extrinsic {
			signed: Alice.into(),
			index: 0,
			function: Call::Staking(staking::Call::transfer::<Concrete>(Bob.into(), 69)),
		};
		let signature = Keyring::from_raw_public(extrinsic.signed).unwrap()
			.sign(&extrinsic.encode()).into();

		UncheckedExtrinsic { extrinsic, signature }
	}

	fn from_block_number(n: u64) -> Header {
		Header::new(n, Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 42);
			assert_eq!(Staking::balance(&Bob), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 42);
			assert_eq!(Staking::balance(&Bob), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		use keyring::Keyring::*;
		let three = [3u8; 32];
		GenesisConfig {
			consensus: Some(Default::default()),
			system: Some(Default::default()),
			session: Some(SessionConfig {
				session_length: 2,
				validators: vec![One.into(), Two.into(), three],
			}),
			staking: Some(StakingConfig {
				sessions_per_era: 2,
				current_era: 0,
				balances: vec![(Alice.into(), 111)],
				intentions: vec![Alice.into(), Bob.into(), Charlie.into()],
				validator_count: 3,
				bonding_duration: 0,
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
			}),
			democracy: Some(Default::default()),
			council: Some(Default::default()),
		}.build_externalities()
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, extrinsics: Vec<Extrinsic>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let extrinsics = extrinsics.into_iter().map(|extrinsic| {
			let signature = Pair::from(Keyring::from_public(Public::from_raw(extrinsic.signed)).unwrap())
				.sign(&extrinsic.encode()).into();

			UncheckedExtrinsic { extrinsic, signature }
		}).collect::<Vec<_>>();

		let extrinsics_root = ordered_trie_root(extrinsics.iter().map(Slicable::encode)).0.into();

		let header = Header {
			parent_hash,
			number,
			state_root,
			extrinsics_root,
			digest: Default::default(),
		};
		let hash = header.blake2_256();

		(Block { header, extrinsics }.encode(), hash.into())
	}

	fn block1() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("76b0393b4958d3cb98bb51d9f4edb316af48485142b8721e94c3b52c75ec3243").into(),
			vec![Extrinsic {
				signed: Alice.into(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(Bob.into(), 69)),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("8ae9828a5988459d35fb428086170dead660176ee0766e89bc1a4b48153d4e88").into(),
			vec![
				Extrinsic {
					signed: Bob.into(),
					index: 0,
					function: Call::Staking(staking::Call::transfer(Alice.into(), 5)),
				},
				Extrinsic {
					signed: Alice.into(),
					index: 1,
					function: Call::Staking(staking::Call::transfer(Bob.into(), 15)),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 41);
			assert_eq!(Staking::balance(&Bob), 69);
		});

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 30);
			assert_eq!(Staking::balance(&Bob), 78);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 41);
			assert_eq!(Staking::balance(&Bob), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 30);
			assert_eq!(Staking::balance(&Bob), 78);
		});
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::balance(&Alice), 42);
			assert_eq!(Staking::balance(&Bob), 69);
		});
	}
}
