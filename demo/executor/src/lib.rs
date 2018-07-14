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
#[cfg(test)] extern crate substrate_runtime_consensus as consensus;
#[cfg(test)] #[macro_use] extern crate hex_literal;

native_executor_instance!(pub Executor, demo_runtime::api::dispatch, demo_runtime::VERSION, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::WasmExecutor;
	use codec::{Slicable, Joiner};
	use keyring::Keyring;
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use demo_primitives::{Hash, BlockNumber, AccountId};
	use runtime_primitives::traits::Header as HeaderT;
	use runtime_primitives::{ApplyOutcome, ApplyError, ApplyResult, MaybeUnsigned};
	use {staking, system, consensus};
	use demo_runtime::{Header, Block, UncheckedExtrinsic, Extrinsic, Call, Concrete, Staking,
		BuildStorage, GenesisConfig, SessionConfig, StakingConfig, BareExtrinsic};
	use ed25519::{Public, Pair};

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn alice() -> AccountId {
		AccountId::from(Keyring::Alice.to_raw_public())
	}

	fn bob() -> AccountId {
		AccountId::from(Keyring::Bob.to_raw_public())
	}

	fn xt() -> UncheckedExtrinsic {
		let extrinsic = BareExtrinsic {
			signed: alice(),
			index: 0,
			function: Call::Staking(staking::Call::transfer::<Concrete>(bob().into(), 69)),
		};
		let signature = MaybeUnsigned(Keyring::from_raw_public(extrinsic.signed.0.clone()).unwrap()
			.sign(&extrinsic.encode()).into());
		let extrinsic = Extrinsic {
			signed: extrinsic.signed.into(),
			index: extrinsic.index,
			function: extrinsic.function,
		};
		UncheckedExtrinsic::new(extrinsic, signature)
	}

	fn from_block_number(n: u64) -> Header {
		Header::new(n, Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = Executor::new().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn bad_extrinsic_with_native_equivalent_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = Executor::new().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 42);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 42);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		use keyring::Keyring::*;
		let three = [3u8; 32].into();
		GenesisConfig {
			consensus: Some(Default::default()),
			system: Some(Default::default()),
			session: Some(SessionConfig {
				session_length: 2,
				validators: vec![One.to_raw_public().into(), Two.to_raw_public().into(), three],
				broken_percent_late: 100,
			}),
			staking: Some(StakingConfig {
				sessions_per_era: 2,
				current_era: 0,
				balances: vec![(alice(), 111)],
				intentions: vec![alice(), bob(), Charlie.to_raw_public().into()],
				validator_count: 3,
				bonding_duration: 0,
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
				existential_deposit: 0,
				transfer_fee: 0,
				creation_fee: 0,
				contract_fee: 0,
				reclaim_rebate: 0,
				early_era_slash: 0,
				session_reward: 0,
			}),
			democracy: Some(Default::default()),
			council: Some(Default::default()),
			timestamp: Some(Default::default()),
		}.build_storage().unwrap()
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, extrinsics: Vec<BareExtrinsic>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let extrinsics = extrinsics.into_iter().map(|extrinsic| {
			let signature = MaybeUnsigned(Pair::from(Keyring::from_public(Public::from_raw(extrinsic.signed.0.clone())).unwrap())
				.sign(&extrinsic.encode()).into());
			let extrinsic = Extrinsic {
				signed: extrinsic.signed.into(),
				index: extrinsic.index,
				function: extrinsic.function,
			};
			UncheckedExtrinsic::new(extrinsic, signature)
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
			hex!("786071057714fdd6ea4595eecd4a0f327908d65f462ff5bca0f700fafce588c9").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(bob().into(), 69)),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("a7f1259cc6b2fa758542f2996e737f8f0de9dec3a9d32641da348178f48b9fc2").into(),
			vec![
				BareExtrinsic {
					signed: bob(),
					index: 0,
					function: Call::Staking(staking::Call::transfer(alice().into(), 5)),
				},
				BareExtrinsic {
					signed: alice(),
					index: 1,
					function: Call::Staking(staking::Call::transfer(bob().into(), 15)),
				}
			]
		)
	}

	fn block1big() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("d95fc2cf4541b97ed2cd381fe7a486af8aebad9ed0480c30e9cca184bb207e95").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Consensus(consensus::Call::remark(vec![0; 60000])),
			}]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 41);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 30);
			assert_eq!(Staking::voting_balance(&bob()), 78);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor{heap_pages: 8}.call(&mut t, COMPACT_CODE, "execute_block", &block1().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 41);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});

		WasmExecutor{heap_pages: 8}.call(&mut t, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 30);
			assert_eq!(Staking::voting_balance(&bob()), 78);
		});
	}

	#[test]
	fn wasm_big_block_import_fails() {
		let mut t = new_test_ext();

		let r = WasmExecutor{heap_pages: 8}.call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(!r.is_ok());
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext();

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(r.is_ok());
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext();

		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, false).0;
		assert!(!r.is_ok());
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
		let r = WasmExecutor{heap_pages: 8}.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = WasmExecutor{heap_pages: 8}.call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<staking::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<staking::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor{heap_pages: 8}.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = WasmExecutor{heap_pages: 8}.call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 42);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});
	}
}
