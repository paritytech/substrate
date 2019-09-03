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
pub use substrate_executor::RuntimesCache;
use substrate_executor::native_executor_instance;

// Declare an instance of the native executor named `Executor`. Include the wasm binary as the
// equivalent wasm code.
native_executor_instance!(
	pub Executor,
	node_runtime::api::dispatch,
	node_runtime::native_version
);

#[cfg(test)]
mod tests {
	use super::Executor;
	use {balances, contracts, indices, system, timestamp};
	use runtime_io;
	use substrate_executor::WasmExecutor;
	use codec::{Encode, Decode, Joiner};
	use runtime_support::{Hashable, StorageValue, StorageMap, assert_eq_error_rate, traits::Currency};
	use state_machine::{CodeExecutor, Externalities, TestExternalities as CoreTestExternalities};
	use primitives::{Blake2Hasher, NeverNativeValue, NativeOrEncoded, map};
	use sr_primitives::traits::{Header as HeaderT, Hash as HashT, Convert};
	use sr_primitives::{ApplyOutcome, ApplyError, ApplyResult};
	use sr_primitives::weights::{WeightMultiplier, GetDispatchInfo};
	use contracts::ContractAddressFor;
	use system::{EventRecord, Phase};
	use node_primitives::{Hash, BlockNumber, Balance};
	use node_runtime::{
		Header, Block, UncheckedExtrinsic, CheckedExtrinsic, Call, Runtime, Balances, BuildStorage,
		System, Event,
		TransferFee, TransactionBaseFee, TransactionByteFee,
	};
	use node_runtime::constants::currency::*;
	use node_runtime::impls::WeightToFee;
	use node_testing::keyring::*;
	use wabt;

	/// The wasm runtime code.
	///
	/// `compact` since it is after post-processing with wasm-gc which performs tree-shaking thus
	/// making the binary slimmer. There is a convention to use compact version of the runtime
	/// as canonical. This is why `native_executor_instance` also uses the compact version of the
	/// runtime.
	const COMPACT_CODE: &[u8] = node_runtime::WASM_BINARY;

	/// The wasm runtime binary which hasn't undergone the compacting process.
	///
	/// The idea here is to pass it as the current runtime code to the executor so the executor will
	/// have to execute provided wasm code instead of the native equivalent. This trick is used to
	/// test code paths that differ between native and wasm versions.
	const BLOATY_CODE: &[u8] = node_runtime::WASM_BINARY_BLOATY;

	const GENESIS_HASH: [u8; 32] = [69u8; 32];

	const VERSION: u32 = node_runtime::VERSION.spec_version;

	type TestExternalities<H> = CoreTestExternalities<H, u64>;

	fn sign(xt: CheckedExtrinsic) -> UncheckedExtrinsic {
		node_testing::keyring::sign(xt, VERSION, GENESIS_HASH)
	}

	/// Default transfer fee
	fn transfer_fee<E: Encode>(extrinsic: &E) -> Balance {
		let length_fee = TransactionBaseFee::get() +
			TransactionByteFee::get() *
			(extrinsic.encode().len() as Balance);

		let weight = default_transfer_call().get_dispatch_info().weight;
		// NOTE: this is really hard to apply, since the multiplier of each block needs to be fetched
		// before the block, while we compute this after the block.
		// weight = <system::Module<Runtime>>::next_weight_multiplier().apply_to(weight);
		let weight_fee = <Runtime as balances::Trait>::WeightToFee::convert(weight);
		length_fee + weight_fee + TransferFee::get()
	}

	fn default_transfer_call() -> balances::Call<Runtime> {
		balances::Call::transfer::<Runtime>(bob().into(), 69 * DOLLARS)
	}

	fn xt() -> UncheckedExtrinsic {
		sign(CheckedExtrinsic {
			signed: Some((alice(), signed_extra(0, 0))),
			function: Call::Balances(default_transfer_call()),
		})
	}

	fn from_block_number(n: u32) -> Header {
		Header::new(n, Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	fn executor() -> ::substrate_executor::NativeExecutor<Executor> {
		substrate_executor::NativeExecutor::new(None)
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				69_u128.encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				69_u128.encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => {
				0_u128.encode()
			},
			<system::BlockHash<Runtime>>::hashed_key_for(0) => {
				vec![0u8; 32]
			}
		], map![]));

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u32)),
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
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				69_u128.encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				69_u128.encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => {
				0_u128.encode()
			},
			<system::BlockHash<Runtime>>::hashed_key_for(0) => {
				vec![0u8; 32]
			}
		], map![]));

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u32)),
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
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				(111 * DOLLARS).encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => vec![0u8; 16],
			<system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		], map![]));

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u32)),
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
			assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - transfer_fee(&xt()));
			assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				(111 * DOLLARS).encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => vec![0u8; 16],
			<system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		], map![]));

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u32)),
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
			assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - transfer_fee(&xt()));
			assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
		});
	}

	fn new_test_ext(code: &[u8], support_changes_trie: bool) -> TestExternalities<Blake2Hasher> {
		let mut ext = TestExternalities::new_with_code(
			code,
			node_testing::genesis::config(support_changes_trie, Some(code)).build_storage().unwrap(),
		);
		ext.changes_trie_storage().insert(0, GENESIS_HASH.into(), Default::default());
		ext
	}

	fn construct_block(
		env: &mut TestExternalities<Blake2Hasher>,
		number: BlockNumber,
		parent_hash: Hash,
		extrinsics: Vec<CheckedExtrinsic>,
	) -> (Vec<u8>, Hash) {
		use trie::{TrieConfiguration, trie_types::Layout};

		// sign extrinsics.
		let extrinsics = extrinsics.into_iter().map(sign).collect::<Vec<_>>();

		// calculate the header fields that we can.
		let extrinsics_root = Layout::<Blake2Hasher>::ordered_trie_root(
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
		executor().call::<_, NeverNativeValue, fn() -> _>(
			env,
			"Core_initialize_block",
			&header.encode(),
			true,
			None,
		).0.unwrap();

		for i in extrinsics.iter() {
			executor().call::<_, NeverNativeValue, fn() -> _>(
				env,
				"BlockBuilder_apply_extrinsic",
				&i.encode(),
				true,
				None,
			).0.unwrap();
		}

		let header = match executor().call::<_, NeverNativeValue, fn() -> _>(
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
					function: Call::Timestamp(timestamp::Call::set(42 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), signed_extra(0, 0))),
					function: Call::Balances(balances::Call::transfer(bob().into(), 69 * DOLLARS)),
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
					function: Call::Timestamp(timestamp::Call::set(42 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), signed_extra(0, 0))),
					function: Call::Balances(balances::Call::transfer(bob().into(), 69 * DOLLARS)),
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
					function: Call::Timestamp(timestamp::Call::set(52 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((bob(), signed_extra(0, 0))),
					function: Call::Balances(balances::Call::transfer(alice().into(), 5 * DOLLARS)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), signed_extra(1, 0))),
					function: Call::Balances(balances::Call::transfer(bob().into(), 15 * DOLLARS)),
				}
			]
		);

		// session change => consensus authorities change => authorities change digest item appears
		let digest = Header::decode(&mut &block2.0[..]).unwrap().digest;
		assert_eq!(digest.logs().len(), 0);

		(block1, block2)
	}

	fn block_with_size(time: u64, nonce: u32, size: usize) -> (Vec<u8>, Hash) {
		construct_block(
			&mut new_test_ext(COMPACT_CODE, false),
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
					signed: None,
					function: Call::Timestamp(timestamp::Call::set(time * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((alice(), signed_extra(nonce, 0))),
					function: Call::System(system::Call::remark(vec![0; size])),
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
			assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - transfer_fee(&xt()));
			assert_eq!(Balances::total_balance(&bob()), 169 * DOLLARS);
			let events = vec![
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
						69 * DOLLARS,
						1 * CENTS
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
			];
			assert_eq!(System::events(), events);
		});
		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block2.0,
			true,
			None,
		).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			// NOTE: fees differ slightly in tests that execute more than one block due to the
			// weight update. Hence, using `assert_eq_error_rate`.
			assert_eq_error_rate!(
				Balances::total_balance(&alice()),
				32 * DOLLARS - 2 * transfer_fee(&xt()),
				10_000
			);
			assert_eq_error_rate!(
				Balances::total_balance(&bob()),
				179 * DOLLARS - transfer_fee(&xt()),
				10_000
			);
			let events = vec![
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
							5 * DOLLARS,
							1 * CENTS,
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
							15 * DOLLARS,
							1 * CENTS,
						)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(2),
					event: Event::system(system::Event::ExtrinsicSuccess),
					topics: vec![],
				},
			];
			assert_eq!(System::events(), events);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		let (block1, block2) = blocks();

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block1.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - transfer_fee(&xt()));
			assert_eq!(Balances::total_balance(&bob()), 169 * DOLLARS);
		});

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block2.0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq_error_rate!(
				Balances::total_balance(&alice()),
				32 * DOLLARS - 2 * transfer_fee(&xt()),
				10_000
			);
			assert_eq_error_rate!(
				Balances::total_balance(&bob()),
				179 * DOLLARS - 1 * transfer_fee(&xt()),
				10_000
			);
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
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "deploy")
	)
	(func (export "call")
		(block $fail
			;; load and check the input data (which is stored in the scratch buffer).
			;; fail if the input size is not != 4
			(br_if $fail
				(i32.ne
					(i32.const 4)
					(call $ext_scratch_size)
				)
			)

			(call $ext_scratch_read
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
					function: Call::Timestamp(timestamp::Call::set(42 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), signed_extra(0, 0))),
					function: Call::Contracts(
						contracts::Call::put_code::<Runtime>(10_000, transfer_code)
					),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), signed_extra(1, 0))),
					function: Call::Contracts(
						contracts::Call::create::<Runtime>(1 * DOLLARS, 10_000, transfer_ch, Vec::new())
					),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), signed_extra(2, 0))),
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

		let result = WasmExecutor::new().call(
			&mut t,
			4,
			COMPACT_CODE,
			"Core_execute_block",
			&block_with_size(42, 0, 120_000).0
		);
		assert!(result.is_err()); // Err(Wasmi(Trap(Trap { kind: Host(AllocatorOutOfSpace) })))
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block_with_size(42, 0, 120_000).0,
			true,
			None,
		).0.unwrap();
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		assert!(
			executor().call::<_, NeverNativeValue, fn() -> _>(
				&mut t,
				"Core_execute_block",
				&block_with_size(42, 0, 120_000).0,
				false,
				None,
			).0.is_err()
		);
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(BLOATY_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				0_u128.encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				0_u128.encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => vec![0u8; 16],
			<system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		], map![]));

		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "Core_initialize_block", &vec![].and(&from_block_number(1u32)));
		assert!(r.is_ok());
		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "BlockBuilder_apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				(111 * DOLLARS).encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => vec![0u8; 16],
			<system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		], map![]));

		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "Core_initialize_block", &vec![].and(&from_block_number(1u32)));
		assert!(r.is_ok());
		let r = WasmExecutor::new()
			.call(&mut t, 8, COMPACT_CODE, "BlockBuilder_apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - 1 * transfer_fee(&xt()));
			assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
		});
	}

	#[test]
	fn full_native_block_import_works_with_changes_trie() {
		let block1 = changes_trie_block();
		let block_data = block1.0;
		let block = Block::decode(&mut &block_data[..]).unwrap();

		let mut t = new_test_ext(COMPACT_CODE, true);
		executor().call::<_, NeverNativeValue, fn() -> _>(
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
		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "Core_execute_block", &block1.0).unwrap();

		assert!(t.storage_changes_root(GENESIS_HASH.into()).unwrap().is_some());
	}

	#[test]
	fn should_import_block_with_test_client() {
		use node_testing::client::{ClientExt, TestClientBuilderExt, TestClientBuilder, consensus::BlockOrigin};

		let client = TestClientBuilder::new().build();
		let block1 = changes_trie_block();
		let block_data = block1.0;
		let block = node_primitives::Block::decode(&mut &block_data[..]).unwrap();

		client.import(BlockOrigin::Own, block).unwrap();
	}


	#[test]
	fn weight_multiplier_increases_and_decreases_on_big_weight() {
		let mut t = new_test_ext(COMPACT_CODE, false);

		let mut prev_multiplier = WeightMultiplier::default();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(System::next_weight_multiplier(), prev_multiplier);
		});

		let mut tt = new_test_ext(COMPACT_CODE, false);

		// big one in terms of weight.
		let block1 = construct_block(
			&mut tt,
			1,
			GENESIS_HASH.into(),
			vec![
				CheckedExtrinsic {
				signed: None,
				function: Call::Timestamp(timestamp::Call::set(42 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), signed_extra(0, 0))),
					function: Call::System(system::Call::fill_block()),
				}
			]
		);

		// small one in terms of weight.
		let block2 = construct_block(
			&mut tt,
			2,
			block1.1.clone(),
			vec![
				CheckedExtrinsic {
				signed: None,
				function: Call::Timestamp(timestamp::Call::set(52 * 1000)),
				},
				CheckedExtrinsic {
					signed: Some((charlie(), signed_extra(1, 0))),
					function: Call::System(system::Call::remark(vec![0; 1])),
				}
			]
		);

		println!("++ Block 1 size: {} / Block 2 size {}", block1.0.encode().len(), block2.0.encode().len());

		// execute a big block.
		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block1.0,
			true,
			None,
		).0.unwrap();

		// weight multiplier is increased for next block.
		runtime_io::with_externalities(&mut t, || {
			let fm = System::next_weight_multiplier();
			println!("After a big block: {:?} -> {:?}", prev_multiplier, fm);
			assert!(fm > prev_multiplier);
			prev_multiplier = fm;
		});

		// execute a big block.
		executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_execute_block",
			&block2.0,
			true,
			None,
		).0.unwrap();

		// weight multiplier is increased for next block.
		runtime_io::with_externalities(&mut t, || {
			let fm = System::next_weight_multiplier();
			println!("After a small block: {:?} -> {:?}", prev_multiplier, fm);
			assert!(fm < prev_multiplier);
		});
	}

	#[test]
	fn transaction_fee_is_correct_ultimate() {
		// This uses the exact values of substrate-node.
		//
		// weight of transfer call as of now: 1_000_000
		// if weight of the cheapest weight would be 10^7, this would be 10^9, which is:
		//   - 1 MILLICENTS in substrate node.
		//   - 1 milldot based on current polkadot runtime.
		// (this baed on assigning 0.1 CENT to the cheapest tx with `weight = 100`)
		let mut t = TestExternalities::<Blake2Hasher>::new_with_code(COMPACT_CODE, (map![
			<balances::FreeBalance<Runtime>>::hashed_key_for(alice()) => {
				(100 * DOLLARS).encode()
			},
			<balances::FreeBalance<Runtime>>::hashed_key_for(bob()) => {
				(10 * DOLLARS).encode()
			},
			<balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(110 * DOLLARS).encode()
			},
			<indices::NextEnumSet<Runtime>>::hashed_key().to_vec() => vec![0u8; 16],
			<system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		], map![]));

		let tip = 1_000_000;
		let xt = sign(CheckedExtrinsic {
			signed: Some((alice(), signed_extra(0, tip))),
			function: Call::Balances(default_transfer_call()),
		});

		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"Core_initialize_block",
			&vec![].and(&from_block_number(1u32)),
			true,
			None,
		).0;

		assert!(r.is_ok());
		let r = executor().call::<_, NeverNativeValue, fn() -> _>(
			&mut t,
			"BlockBuilder_apply_extrinsic",
			&vec![].and(&xt.clone()),
			true,
			None,
		).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&bob()), (10 + 69) * DOLLARS);
			// Components deducted from alice's balances:
			// - Weight fee
			// - Length fee
			// - Tip
			// - Creation-fee of bob's account.
			let mut balance_alice = (100 - 69) * DOLLARS;

			let length_fee = TransactionBaseFee::get() +
				TransactionByteFee::get() *
				(xt.clone().encode().len() as Balance);
			balance_alice -= length_fee;

			let weight = default_transfer_call().get_dispatch_info().weight;
			let weight_fee = WeightToFee::convert(weight);

			// we know that weight to fee multiplier is effect-less in block 1.
			assert_eq!(weight_fee as Balance, MILLICENTS);
			balance_alice -= weight_fee;

			balance_alice -= tip;
			balance_alice -= TransferFee::get();

			assert_eq!(Balances::total_balance(&alice()), balance_alice);
		});
	}

	#[test]
	#[should_panic]
	#[cfg(feature = "stress-test")]
	fn block_weight_capacity_report() {
		// Just report how many transfer calls you could fit into a block. The number should at least
		// be a few hundred (250 at the time of writing but can change over time). Runs until panic.

		// execution ext.
		let mut t = new_test_ext(COMPACT_CODE, false);
		// setup ext.
		let mut tt = new_test_ext(COMPACT_CODE, false);

		let factor = 50;
		let mut time = 10;
		let mut nonce: Index = 0;
		let mut block_number = 1;
		let mut previous_hash: Hash = GENESIS_HASH.into();

		loop {
			let num_transfers = block_number * factor;
			let mut xts = (0..num_transfers).map(|i| CheckedExtrinsic {
				signed: Some((charlie(), signed_extra(nonce + i as Index, 0))),
				function: Call::Balances(balances::Call::transfer(bob().into(), 0)),
			}).collect::<Vec<CheckedExtrinsic>>();

			xts.insert(0, CheckedExtrinsic {
				signed: None,
				function: Call::Timestamp(timestamp::Call::set(time * 1000)),
			});

			// NOTE: this is super slow. Can probably be improved.
			let block = construct_block(
				&mut tt,
				block_number,
				previous_hash,
				xts
			);

			let len = block.0.len();
			print!(
				"++ Executing block with {} transfers. Block size = {} bytes / {} kb / {} mb",
				num_transfers,
				len,
				len / 1024,
				len / 1024 / 1024,
			);

			let r = executor().call::<_, NeverNativeValue, fn() -> _>(
				&mut t,
				"Core_execute_block",
				&block.0,
				true,
				None,
			).0;

			println!(" || Result = {:?}", r);
			assert!(r.is_ok());

			previous_hash = block.1;
			nonce += num_transfers;
			time += 10;
			block_number += 1;
		}
	}

	#[test]
	#[should_panic]
	#[cfg(feature = "stress-test")]
	fn block_length_capacity_report() {
		// Just report how big a block can get. Executes until panic. Should be ignored unless if
		// manually inspected. The number should at least be a few megabytes (5 at the time of
		// writing but can change over time).

		// execution ext.
		let mut t = new_test_ext(COMPACT_CODE, false);
		// setup ext.
		let mut tt = new_test_ext(COMPACT_CODE, false);

		let factor = 256 * 1024;
		let mut time = 10;
		let mut nonce: Index = 0;
		let mut block_number = 1;
		let mut previous_hash: Hash = GENESIS_HASH.into();

		loop {
			// NOTE: this is super slow. Can probably be improved.
			let block = construct_block(
				&mut tt,
				block_number,
				previous_hash,
				vec![
					CheckedExtrinsic {
						signed: None,
						function: Call::Timestamp(timestamp::Call::set(time * 1000)),
					},
					CheckedExtrinsic {
						signed: Some((charlie(), signed_extra(nonce, 0))),
						function: Call::System(system::Call::remark(vec![0u8; (block_number * factor) as usize])),
					},
				]
			);

			let len = block.0.len();
			print!(
				"++ Executing block with big remark. Block size = {} bytes / {} kb / {} mb",
				len,
				len / 1024,
				len / 1024 / 1024,
			);

			let r = executor().call::<_, NeverNativeValue, fn() -> _>(
				&mut t,
				"Core_execute_block",
				&block.0,
				true,
				None,
			).0;

			println!(" || Result = {:?}", r);
			assert!(r.is_ok());

			previous_hash = block.1;
			nonce += 1;
			time += 10;
			block_number += 1;
		}
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
