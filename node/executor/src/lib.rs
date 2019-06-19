// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! A `CodeExecutor` specialization which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

#![cfg_attr(feature = "benchmarks", feature(test))]

#[cfg(feature = "benchmarks")] extern crate test;

pub use substrate_executor::NativeExecutor;
use substrate_executor::native_executor_instance;

// Declare an instance of the native executor named `Executor`. Include the wasm binary as the
// equivalent wasm code.
native_executor_instance!(
	pub Executor,
	node_runtime::api::dispatch,
	node_runtime::native_version,
	include_bytes!(
		"../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm"
	)
);

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::{WasmExecutor, NativeExecutionDispatch};
	use parity_codec::{Encode, Decode, Joiner};
	use keyring::{AuthorityKeyring, AccountKeyring};
	use runtime_support::{Hashable, StorageValue, StorageMap, traits::Currency};
	use state_machine::{CodeExecutor, Externalities, TestExternalities as CoreTestExternalities};
	use primitives::{twox_128, blake2_256, Blake2Hasher, ChangesTrieConfiguration, NeverNativeValue,
		NativeOrEncoded};
	use node_primitives::{Hash, BlockNumber, AccountId};
	use runtime_primitives::traits::{Header as HeaderT, Hash as HashT};
	use runtime_primitives::{generic::Era, ApplyOutcome, ApplyError, ApplyResult, Perbill};
	use {balances, indices, system, staking, timestamp, treasury, contracts};
	use contracts::ContractAddressFor;
	use system::{EventRecord, Phase};
	use node_runtime::{Header, Block, UncheckedExtrinsic, CheckedExtrinsic, Call, Runtime, Balances,
		BuildStorage, GenesisConfig, BalancesConfig, SessionConfig, StakingConfig, System,
		SystemConfig, GrandpaConfig, IndicesConfig, Event, SessionKeys};
	use wabt;
	use primitives::map;

	/// The wasm runtime code.
	///
	/// `compact` since it is after post-processing with wasm-gc which performs tree-shaking thus
	/// making the binary slimmer. There is a convention to use compact version of the runtime
	/// as canonical. This is why `native_executor_instance` also uses the compact version of the
	/// runtime.
	const COMPACT_CODE: &[u8] =
		include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm");

	/// The wasm runtime binary which hasn't undergone the compacting process.
	///
	/// The idea here is to pass it as the current runtime code to the executor so the executor will
	/// have to execute provided wasm code instead of the native equivalent. This trick is used to
	/// test code paths that differ between native and wasm versions.
	const BLOATY_CODE: &[u8] =
		include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.wasm");

	const GENESIS_HASH: [u8; 32] = [69u8; 32];

	type TestExternalities<H> = CoreTestExternalities<H, u64>;

	fn alice() -> AccountId {
		AccountKeyring::Alice.into()
	}

	fn bob() -> AccountId {
		AccountKeyring::Bob.into()
	}

	fn charlie() -> AccountId {
		AccountKeyring::Charlie.into()
	}

	fn dave() -> AccountId {
		AccountKeyring::Dave.into()
	}

	fn eve() -> AccountId {
		AccountKeyring::Eve.into()
	}

	fn ferdie() -> AccountId {
		AccountKeyring::Ferdie.into()
	}

	fn sign(xt: CheckedExtrinsic) -> UncheckedExtrinsic {
		match xt.signed {
			Some((signed, index)) => {
				let era = Era::mortal(256, 0);
				let payload = (index.into(), xt.function, era, GENESIS_HASH);
				let key = AccountKeyring::from_public(&signed).unwrap();
				let signature = payload.using_encoded(|b| {
					if b.len() > 256 {
						key.sign(&runtime_io::blake2_256(b))
					} else {
						key.sign(b)
					}
				}).into();
				UncheckedExtrinsic {
					signature: Some((indices::address::Address::Id(signed), signature, payload.0, era)),
					function: payload.1,
				}
			}
			None => UncheckedExtrinsic {
				signature: None,
				function: xt.function,
			},
		}
	}

	fn xt() -> UncheckedExtrinsic {
		sign(CheckedExtrinsic {
			signed: Some((alice(), 0)),
			function: Call::Balances(balances::Call::transfer::<Runtime>(bob().into(), 69)),
		})
	}

	fn from_block_number(n: u64) -> Header {
		Header::new(n, Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	fn executor() -> ::substrate_executor::NativeExecutor<Executor> {
		::substrate_executor::NativeExecutor::new(None)
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => {
				vec![0u8; 32]
			},
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => {
				vec![70u8; 16]
			},
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			}
		]);

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u64)),
			true,
			None,
		).0;
		assert!(r.is_ok());
		let v = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"BlockBuilder_apply_extrinsic",
			&vec![].and(&xt()),
			true,
			None,
		).0.unwrap();
		let r = ApplyResult::decode(&mut &v.as_encoded()[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn bad_extrinsic_with_native_equivalent_code_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			},
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => {
				vec![0u8; 32]
			},
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => {
				vec![70u8; 16]
			},
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => {
				vec![0u8; 16]
			}
		]);

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u64)),
			true,
			None,
		).0;
		assert!(r.is_ok());
		let v = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"BlockBuilder_apply_extrinsic",
			&vec![].and(&xt()),
			true,
			None,
		).0.unwrap();
		let r = ApplyResult::decode(&mut &v.as_encoded()[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16]
		]);

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u64)),
			true,
			None,
		).0;
		assert!(r.is_ok());
		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"BlockBuilder_apply_extrinsic",
			&vec![].and(&xt()),
			true,
			None,
		).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16]
		]);

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u64)),
			true,
			None,
		).0;
		assert!(r.is_ok());
		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"BlockBuilder_apply_extrinsic",
			&vec![].and(&xt()),
			true,
			None,
		).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	fn to_session_keys(ring: &AuthorityKeyring) -> SessionKeys {
		SessionKeys(ring.to_owned().into(), ring.to_owned().into())
	}

	fn new_test_ext(code: &[u8], support_changes_trie: bool) -> TestExternalities<Blake2Hasher> {
		let three = AccountId::from_raw([3u8; 32]);
		let mut ext = TestExternalities::new_with_code(code, GenesisConfig {
			aura: Some(Default::default()),
			system: Some(SystemConfig {
				changes_trie_config: if support_changes_trie { Some(ChangesTrieConfiguration {
					digest_interval: 2,
					digest_levels: 2,
				}) } else { None },
				..Default::default()
			}),
			indices: Some(IndicesConfig {
				ids: vec![alice(), bob(), charlie(), dave(), eve(), ferdie()],
			}),
			balances: Some(BalancesConfig {
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
				balances: vec![
					(alice(), 111),
					(bob(), 100),
					(charlie(), 100_000_000),
					(dave(), 111),
					(eve(), 101),
					(ferdie(), 100),
				],
				existential_deposit: 0,
				transfer_fee: 0,
				creation_fee: 0,
				vesting: vec![],
			}),
			session: Some(SessionConfig {
				validators: vec![AccountKeyring::One.into(), AccountKeyring::Two.into(), three],
				keys: vec![
					(alice(), to_session_keys(&AuthorityKeyring::Alice)),
					(bob(), to_session_keys(&AuthorityKeyring::Bob)),
					(charlie(), to_session_keys(&AuthorityKeyring::Charlie)),
				]
			}),
			staking: Some(StakingConfig {
				current_era: 0,
				stakers: vec![
					(dave(), alice(), 111, staking::StakerStatus::Validator),
					(eve(), bob(), 100, staking::StakerStatus::Validator),
					(ferdie(), charlie(), 100, staking::StakerStatus::Validator)
				],
				validator_count: 3,
				minimum_validator_count: 0,
				offline_slash: Perbill::zero(),
				session_reward: Perbill::zero(),
				current_session_reward: 0,
				offline_slash_grace: 0,
				invulnerables: vec![alice(), bob(), charlie()],
			}),
			democracy: Some(Default::default()),
			council_seats: Some(Default::default()),
			timestamp: Some(Default::default()),
			treasury: Some(Default::default()),
			contracts: Some(Default::default()),
			sudo: Some(Default::default()),
			grandpa: Some(GrandpaConfig {
				_genesis_phantom_data: Default::default(),
				authorities: vec![],
			}),
		}.build_storage().unwrap().0);
		ext.changes_trie_storage().insert(0, GENESIS_HASH.into(), Default::default());
		ext
	}

	fn construct_block(
		env: &mut TestExternalities<Blake2Hasher>,
		number: BlockNumber,
		parent_hash: Hash,
		extrinsics: Vec<CheckedExtrinsic>,
	) -> (Vec<u8>, Hash) {
		use trie::ordered_trie_root;

		// sign extrinsics.
		let extrinsics = extrinsics.into_iter().map(sign).collect::<Vec<_>>();

		// calculate the header fields that we can.
		let extrinsics_root = ordered_trie_root::<Blake2Hasher, _, _>(
				extrinsics.iter().map(Encode::encode)
			).to_fixed_bytes()
			.into();

		let header = Header {
			parent_hash,
			number,
			extrinsics_root,
			state_root: Default::default(),
			digest: Default::default(),
		};

		// execute the block to get the real header.
		Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
			env,
			"Core_initialize_block",
			&header.encode(),
			true,
			None,
		).0.unwrap();

		for i in extrinsics.iter() {
			Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
				env,
				"BlockBuilder_apply_extrinsic",
				&i.encode(),
				true,
				None,
			).0.unwrap();
		}

		let header = match Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
			env,
			"BlockBuilder_finalize_block",
			&[0u8;0],
			true,
			None,
		).0.unwrap() {
			NativeOrEncoded::Native(_) => unreachable!(),
			NativeOrEncoded::Encoded(h) => Header::decode(&mut &h[..]).unwrap(),
		};

		let hash = header.blake2_256();
		(Block { header, extrinsics }.encode(), hash.into())
	}

	fn changes_trie_block() -> (Vec<u8>, Hash) {
		construct_block(
			&mut new_test_ext(COMPACT_CODE, true),
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 0)),
					function: Call::Balances(balances::Call::transfer(bob().into(), 69)),
				},
			]
		)
	}

	// block 1 and 2 must be created together to ensure transactions are only signed once (since they
	// are not guaranteed to be deterministic) and to ensure that the correct state is propagated
	// from block1's execution to block2 to derive the correct storage_root.
	fn blocks() -> ((Vec<u8>, Hash), (Vec<u8>, Hash)) {
		let mut t = new_test_ext(COMPACT_CODE, false);
		let block1 = construct_block(
			&mut t,
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 0)),
					function: Call::Balances(balances::Call::transfer(bob().into(), 69)),
				},
			]
		);
		let block2 = construct_block(
			&mut t,
			2,
			block1.1.clone(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(52)),
				},
				CheckedExtrinsic {
					signed: Some((bob(), 0)),
					function: Call::Balances(balances::Call::transfer(alice().into(), 5)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 1)),
					function: Call::Balances(balances::Call::transfer(bob().into(), 15)),
				}
			]
		);

		// session change => consensus authorities change => authorities change digest item appears
		let digest = Header::decode(&mut &block2.0[..]).unwrap().digest;
		assert_eq!(digest.logs().len(), 0);
//		assert!(digest.logs()[0].as_consensus().is_some());

		(block1, block2)
	}

	fn big_block() -> (Vec<u8>, Hash) {
		construct_block(
			&mut new_test_ext(COMPACT_CODE, false),
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 0)),
					function: Call::System(system::Call::remark(vec![0; 120000])),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		let (block1, block2) = blocks();

		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block1.0,
			true,
			None,
		).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			// block1 transfers from alice 69 to bob.
			// -1 is the default fee
			assert_eq!(Balances::total_balance(&alice()), 111 - 69 - 1);
			assert_eq!(Balances::total_balance(&bob()), 100 + 69);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::balances(balances::RawEvent::Transfer(
						alice().into(),
						bob().into(),
						69,
						0
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Spending(0)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Burnt(0)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Rollover(0)),
					topics: vec![],
				},
			]);
		});

		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block2.0,
			true,
			None,
		).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			// bob sends 5, alice sends 15 | bob += 10, alice -= 10
			// 111 - 69 - 1 - 10 - 1 = 30
			assert_eq!(Balances::total_balance(&alice()), 111 - 69 - 1 - 10 - 1);
			// 100 + 69 + 10 - 1     = 178
			assert_eq!(Balances::total_balance(&bob()), 100 + 69 + 10 - 1);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::balances(
						balances::RawEvent::Transfer(
							bob().into(),
							alice().into(),
							5,
							0
						)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(2),
					event: Event::balances(
						balances::RawEvent::Transfer(
							alice().into(),
							bob().into(),
							15,
							0
						)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(2),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Spending(0)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Burnt(0)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Rollover(0)),
					topics: vec![],
				},
			]);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		let (block1, block2) = blocks();

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block1.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			// block1 transfers from alice 69 to bob.
			// -1 is the default fee
			assert_eq!(Balances::total_balance(&alice()), 111 - 69 - 1);
			assert_eq!(Balances::total_balance(&bob()), 100 + 69);
		});

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block2.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			// bob sends 5, alice sends 15 | bob += 10, alice -= 10
			// 111 - 69 - 1 - 10 - 1 = 30
			assert_eq!(Balances::total_balance(&alice()), 111 - 69 - 1 - 10 - 1);
			// 100 + 69 + 10 - 1     = 178
			assert_eq!(Balances::total_balance(&bob()), 100 + 69 + 10 - 1);
		});
	}

	const CODE_TRANSFER: &str = r#"
(module
	;; ext_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32
	;; ) -> u32
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_input_size" (func $ext_input_size (result i32)))
	(import "env" "ext_input_copy" (func $ext_input_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "deploy")
	)
	(func (export "call")
		(block $fail
			;; fail if ext_input_size != 4
			(br_if $fail
				(i32.ne
					(i32.const 4)
					(call $ext_input_size)
				)
			)

			(call $ext_input_copy
				(i32.const 0)
				(i32.const 0)
				(i32.const 4)
			)


			(br_if $fail
				(i32.ne
					(i32.load8_u (i32.const 0))
					(i32.const 0)
				)
			)
			(br_if $fail
				(i32.ne
					(i32.load8_u (i32.const 1))
					(i32.const 1)
				)
			)
			(br_if $fail
				(i32.ne
					(i32.load8_u (i32.const 2))
					(i32.const 2)
				)
			)
			(br_if $fail
				(i32.ne
					(i32.load8_u (i32.const 3))
					(i32.const 3)
				)
			)

			(drop
				(call $ext_call
					(i32.const 4)  ;; Pointer to "callee" address.
					(i32.const 32)  ;; Length of "callee" address.
					(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
					(i32.const 36)  ;; Pointer to the buffer with value to transfer
					(i32.const 16)   ;; Length of the buffer with value to transfer.
					(i32.const 0)   ;; Pointer to input data buffer address
					(i32.const 0)   ;; Length of input data buffer
				)
			)

			(return)
		)
		unreachable
	)
	;; Destination AccountId to transfer the funds.
	;; Represented by H256 (32 bytes long) in little endian.
	(data (i32.const 4)
		"\09\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
		"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
		"\00\00\00\00"
	)
	;; Amount of value to transfer.
	;; Represented by u128 (16 bytes long) in little endian.
	(data (i32.const 36)
		"\06\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
		"\00\00"
	)
)
"#;

	#[test]
	fn deploying_wasm_contract_should_work() {

		let transfer_code = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let transfer_ch = <Runtime as system::Trait>::Hashing::hash(&transfer_code);

		let addr = <Runtime as contracts::Trait>::DetermineContractAddress::contract_address_for(
			&transfer_ch,
			&[],
			&charlie(),
		);

		let b = construct_block(
			&mut new_test_ext(COMPACT_CODE, false),
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42)),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), 0)),
					function: Call::Contracts(
						contracts::Call::put_code::<Runtime>(10_000, transfer_code)
					),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), 1)),
					function: Call::Contracts(
						contracts::Call::create::<Runtime>(10, 10_000, transfer_ch, Vec::new())
					),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), 2)),
					function: Call::Contracts(
						contracts::Call::call::<Runtime>(
							indices::address::Address::Id(addr.clone()),
							10,
							10_000,
							vec![0x00, 0x01, 0x02, 0x03]
						)
					),
				},
			]
		);

		let mut t = new_test_ext(COMPACT_CODE, false);

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE,"Core_execute_block", &b.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			// Verify that the contract constructor worked well and code of TRANSFER contract is actually deployed.
			assert_eq!(
				&contracts::ContractInfoOf::<Runtime>::get(addr)
					.and_then(|c| c.get_alive())
					.unwrap()
					.code_hash,
				&transfer_ch
			);
		});
	}

	#[test]
	fn wasm_big_block_import_fails() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		assert!(
			WasmExecutor::new().call(
				&mut t,
				4,
				COMPACT_CODE,
				"Core_execute_block",
				&big_block().0
			).is_err()
		);
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&big_block().0,
			true,
			None,
		).0.unwrap();
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		assert!(
			Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
				&mut t,
				"Core_execute_block",
				&big_block().0,
				false,
				None,
			).0.is_err()
		);
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![70u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16]
		]);

		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "Core_initialize_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "BlockBuilder_apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, map![
			blake2_256(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => {
				vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
			},
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<indices::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			blake2_256(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16]
		]);

		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "Core_initialize_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "BlockBuilder_apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn full_native_block_import_works_with_changes_trie() {
		let block1 = changes_trie_block();
		let block_data = block1.0;
		let block = Block::decode(&mut &block_data[..]).unwrap();

		let mut t = new_test_ext(COMPACT_CODE, true);
		Executor::new(None).call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block.encode(),
			true,
			None,
		).0.unwrap();

		assert!(t.storage_changes_root(GENESIS_HASH.into()).unwrap().is_some());
	}

	#[test]
	fn full_wasm_block_import_works_with_changes_trie() {
		let block1 = changes_trie_block();

		let mut t = new_test_ext(COMPACT_CODE, true);
		WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block1.0).unwrap();

		assert!(t.storage_changes_root(GENESIS_HASH.into()).unwrap().is_some());
	}

	#[test]
	fn should_import_block_with_test_client() {
		use test_client::{ClientExt, TestClientBuilder, consensus::BlockOrigin};

		let client = TestClientBuilder::default()
			.build_with_native_executor::<Block, node_runtime::RuntimeApi, _>(executor())
			.0;

		let block1 = changes_trie_block();
		let block_data = block1.0;
		let block = Block::decode(&mut &block_data[..]).unwrap();

		client.import(BlockOrigin::Own, block).unwrap();
	}

	#[cfg(feature = "benchmarks")]
	mod benches {
		use super::*;
		use test::Bencher;

		#[bench]
		fn wasm_execute_block(b: &mut Bencher) {
			let (block1, block2) = blocks();

			b.iter(|| {
				let mut t = new_test_ext(COMPACT_CODE, false);
				WasmExecutor::new().call(&mut t, "Core_execute_block", &block1.0).unwrap();
				WasmExecutor::new().call(&mut t, "Core_execute_block", &block2.0).unwrap();
			});
		}
	}
}
