// Copyright 2018 Parity Technologies (UK) Ltd.
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

extern crate node_runtime;
#[macro_use] extern crate substrate_executor;
#[cfg_attr(test, macro_use)] extern crate substrate_primitives as primitives;

#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate sr_primitives as runtime_primitives;
#[cfg(test)] extern crate srml_support as runtime_support;
#[cfg(test)] extern crate srml_balances as balances;
#[cfg(test)] extern crate srml_session as session;
#[cfg(test)] extern crate srml_staking as staking;
#[cfg(test)] extern crate srml_system as system;
#[cfg(test)] extern crate srml_consensus as consensus;
#[cfg(test)] extern crate srml_timestamp as timestamp;
#[cfg(test)] extern crate srml_treasury as treasury;
#[cfg(test)] extern crate srml_contract as contract;
#[cfg(test)] extern crate node_primitives;
#[cfg(test)] extern crate parity_codec as codec;
#[cfg(test)] extern crate sr_io as runtime_io;
#[cfg(test)] extern crate substrate_trie as trie;
#[cfg(test)] extern crate substrate_state_machine as state_machine;
#[cfg(test)] #[macro_use] extern crate hex_literal;
#[cfg(test)] extern crate wabt;

pub use substrate_executor::NativeExecutor;
native_executor_instance!(pub Executor, node_runtime::api::dispatch, node_runtime::native_version, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::{WasmExecutor, NativeExecutionDispatch};
	use codec::{Encode, Decode, Joiner};
	use keyring::Keyring;
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, Externalities, TestExternalities};
	use primitives::{twox_128, Blake2Hasher, ChangesTrieConfiguration,
		ed25519::{Public, Pair}};
	use node_primitives::{Hash, BlockNumber, AccountId};
	use runtime_primitives::traits::{Header as HeaderT, Digest as DigestT};
	use runtime_primitives::{generic, generic::Era, ApplyOutcome, ApplyError, ApplyResult, Perbill};
	use {balances, staking, session, system, consensus, timestamp, treasury, contract};
	use contract::ContractAddressFor;
	use system::{EventRecord, Phase};
	use node_runtime::{Header, Block, UncheckedExtrinsic, CheckedExtrinsic, Call, Runtime, Balances,
		BuildStorage, GenesisConfig, BalancesConfig, SessionConfig, StakingConfig, System,
		SystemConfig, Event, Log};
	use wabt;

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm");
	const GENESIS_HASH: [u8; 32] = [69u8; 32];

	fn alice() -> AccountId {
		AccountId::from(Keyring::Alice.to_raw_public())
	}

	fn bob() -> AccountId {
		AccountId::from(Keyring::Bob.to_raw_public())
	}

	fn charlie() -> AccountId {
		AccountId::from(Keyring::Charlie.to_raw_public())
	}

	fn sign(xt: CheckedExtrinsic) -> UncheckedExtrinsic {
		match xt.signed {
			Some((signed, index)) => {
				let era = Era::mortal(256, 0);
				let payload = (index, xt.function, era, GENESIS_HASH);
				let pair = Pair::from(Keyring::from_public(Public::from_raw(signed.clone().into())).unwrap());
				let signature = pair.sign(&payload.encode()).into();
				UncheckedExtrinsic {
					signature: Some((balances::address::Address::Id(signed), signature, payload.0, era)),
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
			function: Call::Balances(balances::Call::transfer::<Runtime>(bob().into(), 69.into())),
		})
	}

	fn from_block_number(n: u64) -> Header {
		Header::new(n, Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	fn executor() -> ::substrate_executor::NativeExecutor<Executor> {
		::substrate_executor::NativeExecutor::new()
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![70u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, 8, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn bad_extrinsic_with_native_equivalent_code_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![70u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, 8, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, 8, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, 8, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	fn new_test_ext(support_changes_trie: bool) -> TestExternalities<Blake2Hasher> {
		use keyring::Keyring::*;
		let three = [3u8; 32].into();
		TestExternalities::new(GenesisConfig {
			consensus: Some(Default::default()),
			system: Some(SystemConfig {
				changes_trie_config: if support_changes_trie { Some(ChangesTrieConfiguration {
					digest_interval: 2,
					digest_levels: 2,
				}) } else { None },
				..Default::default()
			}),
			balances: Some(BalancesConfig {
				balances: vec![
					(alice(), 111),
					(charlie(), 100_000_000),
				],
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
				existential_deposit: 0,
				transfer_fee: 0,
				creation_fee: 0,
				reclaim_rebate: 0,
			}),
			session: Some(SessionConfig {
				session_length: 2,
				validators: vec![One.to_raw_public().into(), Two.to_raw_public().into(), three],
			}),
			staking: Some(StakingConfig {
				sessions_per_era: 2,
				current_era: 0,
				intentions: vec![alice(), bob(), Charlie.to_raw_public().into()],
				validator_count: 3,
				minimum_validator_count: 0,
				bonding_duration: 0,
				offline_slash: Perbill::zero(),
				session_reward: Perbill::zero(),
				current_offline_slash: 0,
				current_session_reward: 0,
				offline_slash_grace: 0,
			}),
			democracy: Some(Default::default()),
			council_seats: Some(Default::default()),
			council_voting: Some(Default::default()),
			timestamp: Some(Default::default()),
			treasury: Some(Default::default()),
			contract: Some(Default::default()),
			upgrade_key: Some(Default::default()),
		}.build_storage().unwrap().0)
	}

	fn construct_block(
		number: BlockNumber,
		parent_hash: Hash,
		state_root: Hash,
		changes_root: Option<Hash>,
		extrinsics: Vec<CheckedExtrinsic>
	) -> (Vec<u8>, Hash) {
		use trie::ordered_trie_root;

		let extrinsics = extrinsics.into_iter().map(sign).collect::<Vec<_>>();
		let extrinsics_root = ordered_trie_root::<Blake2Hasher, _, _>(extrinsics.iter().map(Encode::encode)).0.into();

		let mut digest = generic::Digest::<Log>::default();
		if let Some(changes_root) = changes_root {
			digest.push(Log::from(system::RawLog::ChangesTrieRoot::<Hash>(changes_root)));
		}

		let header = Header {
			parent_hash,
			number,
			state_root,
			extrinsics_root,
			digest,
		};
		let hash = header.blake2_256();

		(Block { header, extrinsics }.encode(), hash.into())
	}

	fn block1(support_changes_trie: bool) -> (Vec<u8>, Hash) {
		construct_block(
			1,
			GENESIS_HASH.into(),
			if support_changes_trie {
				hex!("978a3ff733a86638da39d36a349c693b5cf562bcc8db30fec6c2b6c40f925a9b").into()
			} else {
				hex!("7bbad534e3de3db3c8cda015c4e8ed8ba10dde7e3fca21f4fd4fbc686e6c1410").into()
			},
			if support_changes_trie {
				Some(hex!("1f8f44dcae8982350c14dee720d34b147e73279f5a2ce1f9781195a991970978").into())
			} else {
				None
			},
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42.into())),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 0)),
					function: Call::Balances(balances::Call::transfer(bob().into(), 69.into())),
				},
			]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1(false).1,
			hex!("7be30152ee2ee909047cffad5f0a28bf8c2b0a97c124b500aeac112f6917738e").into(),
			None,
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(52.into())),
				},
				CheckedExtrinsic {
					signed: Some((bob(), 0)),
					function: Call::Balances(balances::Call::transfer(alice().into(), 5.into())),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 1)),
					function: Call::Balances(balances::Call::transfer(bob().into(), 15.into())),
				}
			]
		)
	}

	fn block1big() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			GENESIS_HASH.into(),
			hex!("325a73726dc640af41becb42938e7152e218f130219c0695aae35b6a156f93f3").into(),
			None,
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42.into())),
				},
				CheckedExtrinsic {
					signed: Some((alice(), 0)),
					function: Call::Consensus(consensus::Call::remark(vec![0; 120000])),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext(false);

		executor().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(false).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 41);
			assert_eq!(Balances::total_balance(&bob()), 69);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::balances(balances::RawEvent::NewAccount(bob(), 2, balances::NewAccountOutcome::NoHint))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::balances(balances::RawEvent::Transfer(
						hex!["d172a74cda4c865912c32ba0a80a57ae69abae410e5ccb59dee84e2f4432db4f"].into(),
						hex!["d7568e5f0a7eda67a82691ff379ac4bba4f9c9b859fe779b5d46363b61ad2db9"].into(),
						69,
						0
					))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Spending(0))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Burnt(0))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Rollover(0))
				}
			]);
		});

		executor().call(&mut t, 8, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 30);
			assert_eq!(Balances::total_balance(&bob()), 78);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::balances(
						balances::RawEvent::Transfer(
							hex!["d7568e5f0a7eda67a82691ff379ac4bba4f9c9b859fe779b5d46363b61ad2db9"].into(),
							hex!["d172a74cda4c865912c32ba0a80a57ae69abae410e5ccb59dee84e2f4432db4f"].into(),
							5,
							0
						)
					)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(2),
					event: Event::balances(
						balances::RawEvent::Transfer(
							hex!["d172a74cda4c865912c32ba0a80a57ae69abae410e5ccb59dee84e2f4432db4f"].into(),
							hex!["d7568e5f0a7eda67a82691ff379ac4bba4f9c9b859fe779b5d46363b61ad2db9"].into(),
							15,
							0
						)
					)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(2),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::session(session::RawEvent::NewSession(1))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::staking(staking::RawEvent::Reward(0))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Spending(0))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Burnt(0))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::treasury(treasury::RawEvent::Rollover(0))
				}
			]);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext(false);

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(false).0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 41);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 30);
			assert_eq!(Balances::total_balance(&bob()), 78);
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
	(data (i32.const 4) "\09\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u128 (16 bytes long) in little endian.
	(data (i32.const 36) "\06\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00")
)
"#;

	/// Convert a byte slice to a string with hex values.
	/// Convert a byte slice to a string with hex values.
	///
	/// Each value is preceeded with a `\` character.
	fn escaped_bytestring(bytes: &[u8]) -> String {
		use std::fmt::Write;
		let mut result = String::new();
		for b in bytes {
			write!(result, "\\{:02x}", b).unwrap();
		}
		result
	}

	/// Create a constructor for the specified code.
	///
	/// When constructor is executed, it will call `ext_return` with code that
	/// specified in `child_bytecode`.
	fn code_ctor(child_bytecode: &[u8]) -> String {
		format!(
			r#"
	(module
		;; ext_return(data_ptr: u32, data_len: u32) -> !
		(import "env" "ext_return" (func $ext_return (param i32 i32)))
		(import "env" "memory" (memory 1 1))
		(func (export "call")
			(call $ext_return
				(i32.const 4)
				(i32.const {code_len})
			)
			;; ext_return is diverging, i.e. doesn't return.
			unreachable
		)
		(data (i32.const 4) "{escaped_bytecode}")
	)
	"#,
			escaped_bytecode = escaped_bytestring(child_bytecode),
			code_len = child_bytecode.len(),
		)
	}

	#[test]
	fn deploying_wasm_contract_should_work() {
		let mut t = new_test_ext(false);

		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();

		let addr = <Runtime as contract::Trait>::DetermineContractAddress::contract_address_for(
			&code_ctor_transfer,
			&[],
			&charlie(),
		);

		let b = construct_block(
			1,
			GENESIS_HASH.into(),
			hex!("cf0fee74c87ecff646804984bbdf85832a788b3ca2a2aa33e20da61fa7182b37").into(),
			None,
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(42.into())),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), 0)),
					function: Call::Contract(
						contract::Call::create::<Runtime>(10.into(), 10_000.into(), code_ctor_transfer, Vec::new())
					),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), 1)),
					function: Call::Contract(
						contract::Call::call::<Runtime>(addr, 10.into(), 10_000.into(), vec![0x00, 0x01, 0x02, 0x03])
					),
				},
			]
		);

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &b.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			// Verify that the contract constructor worked well and code of TRANSFER contract is actually deployed.
			assert_eq!(&contract::CodeOf::<Runtime>::get(addr), &code_transfer);
		});
	}

	#[test]
	fn wasm_big_block_import_fails() {
		let mut t = new_test_ext(false);

		let r = WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0);
		assert!(!r.is_ok());
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext(false);

		let r = Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(r.is_ok());
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext(false);

		let r = Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0, false).0;
		assert!(!r.is_ok());
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![70u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.wasm");
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new(map![
			twox_128(&<balances::FreeBalance<Runtime>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Runtime>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransactionByteFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::ExistentialDeposit<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::CreationFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::TransferFee<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(<balances::NextEnumSet<Runtime>>::key()).to_vec() => vec![0u8; 16],
			twox_128(&<system::BlockHash<Runtime>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm");
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn full_native_block_import_works_with_changes_trie() {
		let mut t = new_test_ext(true);
		Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(true).0, true).0.unwrap();

		assert!(t.storage_changes_root(1).is_some());
	}

	#[test]
	fn full_wasm_block_import_works_with_changes_trie() {
		let mut t = new_test_ext(true);
		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(true).0).unwrap();

		assert!(t.storage_changes_root(1).is_some());
	}
}
