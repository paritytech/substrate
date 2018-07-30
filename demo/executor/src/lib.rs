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

pub use substrate_executor::NativeExecutor;
native_executor_instance!(pub Executor, demo_runtime::api::dispatch, demo_runtime::VERSION, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io::{self, Externalities};
	use super::Executor;
	use substrate_executor::{WasmExecutor, NativeExecutionDispatch};
	use codec::{Encode, Decode, Joiner};
	use keyring::Keyring;
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use demo_primitives::{Hash, BlockNumber, AccountId, Balance};
	use runtime_primitives::traits::Header as HeaderT;
	use runtime_primitives::{ApplyOutcome, ApplyError, ApplyResult, MaybeUnsigned};
	use {staking, system, consensus};
	use demo_runtime::{Header, Block, UncheckedExtrinsic, Extrinsic, Call, Concrete, Staking, System,
		BuildStorage, GenesisConfig, SessionConfig, StakingConfig, BareExtrinsic, SystemConfig};
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

	fn executor() -> ::substrate_executor::NativeExecutor<Executor> {
		::substrate_executor::NativeExecutor::with_heap_pages(8, 8)
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

		let r = executor().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
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

		let r = executor().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
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

		let r = executor().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
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

		let r = executor().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 42);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});
	}

	fn new_test_ext(with_prefix: bool, existential_deposit: Balance) -> TestExternalities {
		use keyring::Keyring::*;
		let three = [3u8; 32].into();
		GenesisConfig {
			consensus: Some(Default::default()),
			system: Some(SystemConfig {
				use_block_number_prefix: with_prefix,
				storage_purge_interval: if with_prefix { Some(4) } else { None },
				min_purged_value_age: if with_prefix { Some(2) } else { None },
				..Default::default()
			}),
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
				existential_deposit,
				transfer_fee: 0,
				creation_fee: 0,
				reclaim_rebate: 0,
				early_era_slash: 0,
				session_reward: 0,
			}),
			democracy: Some(Default::default()),
			council: Some(Default::default()),
			timestamp: Some(Default::default()),
		}.build_storage().unwrap().into()
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

		let extrinsics_root = ordered_trie_root(extrinsics.iter().map(Encode::encode)).0.into();

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

	fn block1(with_prefix: bool) -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			if with_prefix {
				hex!("8c516ad4b624f1d2d83c4bff6a82681edff7ef226d547da0119b70301a172da4")
			} else {
				hex!("b97d52254fc967bb94bed485de6a738e9fad05decfda3453711677b8becf6d0a")
			}.into(),
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
			block1(false).1,
			hex!("a1f018d2faa339f72f5ee29050b4670d971e2e271cc06c41ee9cbe1f4c6feec9").into(),
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
			hex!("41d07010f49aa29b2c9aca542cbaa6f59aafd3dda53cdf711c51ddb7d386912e").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Consensus(consensus::Call::remark(vec![0; 60000])),
			}]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext(false, 0);

		executor().call(&mut t, COMPACT_CODE, "execute_block", &block1(false).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 41);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});

		executor().call(&mut t, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 30);
			assert_eq!(Staking::voting_balance(&bob()), 78);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext(false, 0);

		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1(false).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 41);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});

		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 30);
			assert_eq!(Staking::voting_balance(&bob()), 78);
		});
	}

	#[test]
	fn wasm_big_block_import_fails() {
		let mut t = new_test_ext(false, 0);

		let r = WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(!r.is_ok());
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext(false, 0);

		let r = Executor::with_heap_pages(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(r.is_ok());
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext(false, 0);

		let r = Executor::with_heap_pages(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1big().0, false).0;
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
		let r = WasmExecutor::new(8, 8).call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = WasmExecutor::new(8, 8).call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
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
		let r = WasmExecutor::new(8, 8).call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = WasmExecutor::new(8, 8).call(&mut t, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Staking::voting_balance(&alice()), 42);
			assert_eq!(Staking::voting_balance(&bob()), 69);
		});
	}

	#[test]
	fn change_block_number_is_unknown_by_runtime_without_prefix() {
		let mut t = new_test_ext(false, 0);
		runtime_io::with_externalities(&mut t, || {
			assert_eq!(System::storage_value_change_block(
				&<staking::SessionReward<Concrete>>::key()
			), None)
		});
	}

	#[test]
	fn change_block_number_is_known_by_native_runtime_with_prefix() {
		let mut t = new_test_ext(true, 0);

		runtime_io::with_externalities(&mut t, || {
			// session reward is non-empty at genesis
			assert_eq!(System::storage_value_change_block(
				&<staking::SessionReward<Concrete>>::key()
			), Some(0));
			// Alice have a non-empty balance at the genesis
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(alice())
			), Some(0));
			// and Bob does not
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(bob())
			), None);
		});

		executor().call(&mut t, COMPACT_CODE, "execute_block", &block1(true).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			// session reward has not changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::SessionReward<Concrete>>::key()
			), Some(0));
			// Alice balance has been changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(alice())
			), Some(1));
			// Bob balance has been changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(bob())
			), Some(1));
		});
	}

	#[test]
	fn change_block_number_is_known_by_wasm_runtime_with_prefix() {
		let mut t = new_test_ext(true, 0);

		runtime_io::with_externalities(&mut t, || {
			// session reward is non-empty at genesis
			assert_eq!(System::storage_value_change_block(
				&<staking::SessionReward<Concrete>>::key()
			), Some(0));
			// Alice have a non-empty balance at the genesis
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(alice())
			), Some(0));
			// and Bob does not
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(bob())
			), None);
		});

		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1(true).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			// session reward has not changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::SessionReward<Concrete>>::key()
			), Some(0));
			// Alice balance has been changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(alice())
			), Some(1));
			// Bob balance has been changed at block#1
			assert_eq!(System::storage_value_change_block(
				&<staking::FreeBalance<Concrete>>::key_for(bob())
			), Some(1));
		});
	}

	fn alice_balance_with_prefix(t: &TestExternalities) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
		t.storage(&twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())))
			.map(|mut prefix| {
				let balance = prefix.split_off(8);
				(Some(prefix), if balance.is_empty() { None } else { Some(balance) })
			})
			.unwrap_or_default()
	}

	fn is_alice_balance_scheduled_for_purge(t: &TestExternalities) -> bool {
		let mut key = b":deleted:map:".to_vec();
		key.extend(&twox_128(&<staking::FreeBalance<Concrete>>::key_for(alice())));
		t.storage(&key).is_some()
	}

	fn purge_check_blocks() -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
		let (block1, block1_hash) = construct_block(1, [0u8; 32].into(),
			hex!("98c95785d35313f3d42b008eb03232f9f6afee8b9aab97f89c8abc33b1e36f6c").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(bob().into(), 100)),
			}]);
		let (block2, block2_hash) = construct_block(2, block1_hash,
			hex!("06ad3d42c4cd8014ec4da70885363445075f12711a6c58c273375f669dd235d6").into(),
			vec![]);
		let (block3, block3_hash) = construct_block(3, block2_hash,
			hex!("33e075417e0402e0cb923cae68d3559a879b1d0b7b0bd55f1e3b01c8c46c7c30").into(),
			vec![]);
		let (block4, _) = construct_block(4, block3_hash,
			hex!("2ffab08e7bd186004e51510ad0a927f9ae520a1d56fc544f970bd06d44b1ee40").into(),
			vec![]);
		(block1, block2, block3, block4)
	}

	#[test]
	fn prefixed_values_are_purged_after_native_purge_block_import() {
		let mut t = new_test_ext(true, 100);
		let (block1, block2, block3, block4) = purge_check_blocks();

		// at the genesis block there's Alice with free balance of 111
		// let's say at block1 Alice transfers 100 dots to Bob
		// => Alice account disappers, because her balance is dropped below existential deposit (100)
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block1, true).0.unwrap();

		// after block1 Alice' free balance is deleted, but it still has a footprint in db
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#2
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block2, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#3
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block3, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// purge is performed @ block#4 => mine empty block && check that footprint is removed
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block4, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (None, None));
	}

	#[test]
	fn prefixed_values_are_purged_after_wasm_purge_block_import() {
		let mut t = new_test_ext(true, 100);
		let (block1, block2, block3, block4) = purge_check_blocks();

		// at the genesis block there's Alice with free balance of 111
		// let's say at block1 Alice transfers 100 dots to Bob
		// => Alice account disappers, because her balance is dropped below existential deposit (100)
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1, true).0.unwrap();

		// after block1 Alice' free balance is deleted, but it still has a footprint in db
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#2
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block2, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#3
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block3, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// purge is performed @ block#4 => mine empty block && check that footprint is removed
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block4, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (None, None));
	}

	fn recently_purge_check_blocks() -> (Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>) {
		let (block1, block1_hash) = construct_block(1, [0u8; 32].into(),
			hex!("f08294d628fd15e6410184f0a87c867fdea6d13fc1da718696e753f96d93ae72").into(),
			vec![]);
		let (block2, block2_hash) = construct_block(2, block1_hash,
			hex!("fd175eb2a1df58e4e103c1f630a11bdc46a4ea0bb26fcb44315a37c8694ce09a").into(),
			vec![]);
		let (block3, block3_hash) = construct_block(3, block2_hash,
			hex!("5225f4861c89007b858dfb7f701728d14a214df96d735f80e59e020675cdbad3").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(bob().into(), 100)),
			}]);
		let (block4, block4_hash) = construct_block(4, block3_hash,
			hex!("e8826789efa5f521062fd5d4ea1cbc3f758e51fd3d2a65f7e7612c45a960b961").into(),
			vec![]);
		let (block5, block5_hash) = construct_block(5, block4_hash,
			hex!("8b88f7c5cd1bfc3aa416a9434ae62ae607fff3751bb632e84a3520d7aba86348").into(),
			vec![]);
		let (block6, block6_hash) = construct_block(6, block5_hash,
			hex!("de4d162b2c70781cba13d39646f420b7f479dd8677e3121a4ee8862636fc7433").into(),
			vec![]);
		let (block7, block7_hash) = construct_block(7, block6_hash,
			hex!("d9ef3e74441b4c3a846f8482e5adb2341951be0caa867d34dd255527a8079fbf").into(),
			vec![]);
		let (block8, _) = construct_block(8, block7_hash,
			hex!("9cc6a8e83ed7e01b0b0bc3fb0da8f847443d2b3b7be5dc767f4a213786a090a5").into(),
			vec![]);
		(vec![block1, block2], vec![block3, block4, block5, block6, block7], block8)
	}

	#[test]
	fn prefixed_values_are_not_purged_after_native_purge_block_import_if_deleted_recently() {
		let mut t = new_test_ext(true, 100);
		let (has_balance_blocks, has_no_balance_blocks, has_no_footprint_block) = recently_purge_check_blocks();

		// at these blocks Alice has a balance
		for has_balance_block in has_balance_blocks {
			executor().call(&mut t, COMPACT_CODE, "execute_block", &has_balance_block, true).0.unwrap();
			let (prefix, balance) = alice_balance_with_prefix(&t);
			assert!(prefix.is_some() && balance.is_some());
		}

		// at these blocks Alice has no balance, but balance is not yet purged
		for has_no_balance_block in has_no_balance_blocks {
			executor().call(&mut t, COMPACT_CODE, "execute_block", &has_no_balance_block, true).0.unwrap();
			let (prefix, balance) = alice_balance_with_prefix(&t);
			assert!(prefix.is_some() && balance.is_none());
		}

		// finally balance is purged off the db
		executor().call(&mut t, COMPACT_CODE, "execute_block", &has_no_footprint_block, true).0.unwrap();
		let (prefix, balance) = alice_balance_with_prefix(&t);
		assert!(prefix.is_none() && balance.is_none());
	}

	#[test]
	fn prefixed_values_are_not_purged_after_wasm_purge_block_import_if_deleted_recently() {
		let mut t = new_test_ext(true, 100);
		let (has_balance_blocks, has_no_balance_blocks, has_no_footprint_block) = recently_purge_check_blocks();

		// at these blocks Alice has a balance
		for has_balance_block in has_balance_blocks {
			WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &has_balance_block, true).0.unwrap();
			let (prefix, balance) = alice_balance_with_prefix(&t);
			assert!(prefix.is_some() && balance.is_some());
		}

		// at these blocks Alice has no balance, but balance is not yet purged
		for has_no_balance_block in has_no_balance_blocks {
			WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &has_no_balance_block, true).0.unwrap();
			let (prefix, balance) = alice_balance_with_prefix(&t);
			assert!(prefix.is_some() && balance.is_none());
		}

		// finally balance is purged off the db
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &has_no_footprint_block, true).0.unwrap();
		let (prefix, balance) = alice_balance_with_prefix(&t);
		assert!(prefix.is_none() && balance.is_none());
	}

	fn recreated_purge_check_blocks() -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
		let (block1, block1_hash) = construct_block(1, [0u8; 32].into(),
			hex!("d3e819b9539fea007e4489c903abb928aa80f97ff850a6f1f3d0ca1a67f58159").into(),
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(bob().into(), 110)),
			}]);
		let (block2, block2_hash) = construct_block(2, block1_hash,
			hex!("5b69688dbed36d7834cb940e77ebd1bccabf8ed8939b4ab122714fc6b6bf8cad").into(),
			vec![]);
		let (block3, block3_hash) = construct_block(3, block2_hash,
			hex!("b2031fd2fc59bd6eb5c19768a94605895f8d15ac151c147defdaf1fe8670c515").into(),
			vec![BareExtrinsic {
				signed: bob(),
				index: 0,
				function: Call::Staking(staking::Call::transfer(alice().into(), 109)),
			}]);
		let (block4, _) = construct_block(4, block3_hash,
			hex!("e14f06895c83bbd9e5d149827caa213d06329b4d1e7cc99c854c72a865e3de59").into(),
			vec![]);
		(block1, block2, block3, block4)
	}

	#[test]
	fn prefixed_values_are_not_purged_after_native_purge_block_import_if_recreated_after_deletion() {
		let mut t = new_test_ext(true, 100);
		let (block1, block2, block3, block4) = recreated_purge_check_blocks();

		// at the genesis block there's Alice with free balance of 111
		// let's say at block1 Alice transfers 100 dots to Bob
		// => Alice account disappers, because her balance is dropped below existential deposit (100)
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block1, true).0.unwrap();

		// after block1 Alice' free balance is deleted, but it still has a footprint in db
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#2
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block2, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// at block#3 Bob returns 100 DOTs to Alice => Alice account is recreated back
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block3, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t),
			(Some(vec![3, 0, 0, 0, 0, 0, 0, 0]), Some(vec![109, 0, 0, 0, 0, 0, 0, 0])));

		// purge is performed @ block#4 => Aice account is not deleted
		executor().call(&mut t, COMPACT_CODE, "execute_block", &block4, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t),
			(Some(vec![3, 0, 0, 0, 0, 0, 0, 0]), Some(vec![109, 0, 0, 0, 0, 0, 0, 0])));

		// check that value is not scheduled for purge anymore
		assert!(!is_alice_balance_scheduled_for_purge(&t));
	}

	#[test]
	fn prefixed_values_are_not_purged_after_wasm_purge_block_import_if_recreated_after_deletion() {
		let mut t = new_test_ext(true, 100);
		let (block1, block2, block3, block4) = recreated_purge_check_blocks();

		// at the genesis block there's Alice with free balance of 111
		// let's say at block1 Alice transfers 110 dots to Bob
		// => Alice account disappers, because her balance is dropped below existential deposit (100)
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block1, true).0.unwrap();

		// after block1 Alice' free balance is deleted, but it still has a footprint in db
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// mine empty block#2
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block2, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t), (Some(vec![1, 0, 0, 0, 0, 0, 0, 0]), None));

		// at block#3 Bob returns 109 DOTs to Alice => Alice account is recreated back
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block3, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t),
			(Some(vec![3, 0, 0, 0, 0, 0, 0, 0]), Some(vec![109, 0, 0, 0, 0, 0, 0, 0])));

		// purge is performed @ block#4 => Aice account is not deleted
		WasmExecutor::new(8, 8).call(&mut t, COMPACT_CODE, "execute_block", &block4, true).0.unwrap();
		assert_eq!(alice_balance_with_prefix(&t),
			(Some(vec![3, 0, 0, 0, 0, 0, 0, 0]), Some(vec![109, 0, 0, 0, 0, 0, 0, 0])));
	
		// check that value is not scheduled for purge anymore
		assert!(!is_alice_balance_scheduled_for_purge(&t));
	}
}
