// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use codec::{Encode, Decode, Joiner};
use frame_support::{
	StorageValue, StorageMap,
	traits::Currency,
	weights::{GetDispatchInfo, DispatchInfo, DispatchClass, constants::ExtrinsicBaseWeight},
};
use sp_core::{
	NeverNativeValue, map, traits::Externalities, storage::{well_known_keys, Storage},
};
use sp_runtime::{
	ApplyExtrinsicResult, Fixed128,
	traits::{Hash as HashT, Convert, BlakeTwo256},
	transaction_validity::InvalidTransaction,
};
use pallet_contracts::ContractAddressFor;
use frame_system::{self, EventRecord, Phase};

use node_runtime::{
	Header, Block, UncheckedExtrinsic, CheckedExtrinsic, Call, Runtime, Balances,
	System, TransactionPayment, Event, TransactionByteFee,
	constants::currency::*,
};
use node_primitives::{Balance, Hash};
use wabt;
use node_testing::keyring::*;

pub mod common;
use self::common::{*, sign};

/// The wasm runtime binary which hasn't undergone the compacting process.
///
/// The idea here is to pass it as the current runtime code to the executor so the executor will
/// have to execute provided wasm code instead of the native equivalent. This trick is used to
/// test code paths that differ between native and wasm versions.
pub const BLOATY_CODE: &[u8] = node_runtime::WASM_BINARY_BLOATY;

/// Default transfer fee
fn transfer_fee<E: Encode>(extrinsic: &E, fee_multiplier: Fixed128) -> Balance {
	let length_fee = TransactionByteFee::get() * (extrinsic.encode().len() as Balance);

	let base_weight = ExtrinsicBaseWeight::get();
	let base_fee = <Runtime as pallet_transaction_payment::Trait>::WeightToFee::convert(base_weight);
	let weight = default_transfer_call().get_dispatch_info().weight;
	let weight_fee = <Runtime as pallet_transaction_payment::Trait>::WeightToFee::convert(weight);

	base_fee + fee_multiplier.saturated_multiply_accumulate(length_fee + weight_fee)
}

fn xt() -> UncheckedExtrinsic {
	sign(CheckedExtrinsic {
		signed: Some((alice(), signed_extra(0, 0))),
		function: Call::Balances(default_transfer_call()),
	})
}

fn set_heap_pages<E: Externalities>(ext: &mut E, heap_pages: u64) {
	ext.place_storage(well_known_keys::HEAP_PAGES.to_vec(), Some(heap_pages.encode()));
}

fn changes_trie_block() -> (Vec<u8>, Hash) {
	construct_block(
		&mut new_test_ext(COMPACT_CODE, true),
		1,
		GENESIS_HASH.into(),
		vec![
			CheckedExtrinsic {
				signed: None,
				function: Call::Timestamp(pallet_timestamp::Call::set(42 * 1000)),
			},
			CheckedExtrinsic {
				signed: Some((alice(), signed_extra(0, 0))),
				function: Call::Balances(pallet_balances::Call::transfer(bob().into(), 69 * DOLLARS)),
			},
		]
	)
}

/// block 1 and 2 must be created together to ensure transactions are only signed once (since they
/// are not guaranteed to be deterministic) and to ensure that the correct state is propagated
/// from block1's execution to block2 to derive the correct storage_root.
fn blocks() -> ((Vec<u8>, Hash), (Vec<u8>, Hash)) {
	let mut t = new_test_ext(COMPACT_CODE, false);
	let block1 = construct_block(
		&mut t,
		1,
		GENESIS_HASH.into(),
		vec![
			CheckedExtrinsic {
				signed: None,
				function: Call::Timestamp(pallet_timestamp::Call::set(42 * 1000)),
			},
			CheckedExtrinsic {
				signed: Some((alice(), signed_extra(0, 0))),
				function: Call::Balances(pallet_balances::Call::transfer(bob().into(), 69 * DOLLARS)),
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
				function: Call::Timestamp(pallet_timestamp::Call::set(52 * 1000)),
			},
			CheckedExtrinsic {
				signed: Some((bob(), signed_extra(0, 0))),
				function: Call::Balances(pallet_balances::Call::transfer(alice().into(), 5 * DOLLARS)),
			},
			CheckedExtrinsic {
				signed: Some((alice(), signed_extra(1, 0))),
				function: Call::Balances(pallet_balances::Call::transfer(bob().into(), 15 * DOLLARS)),
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
				function: Call::Timestamp(pallet_timestamp::Call::set(time * 1000)),
			},
			CheckedExtrinsic {
				signed: Some((alice(), signed_extra(nonce, 0))),
				function: Call::System(frame_system::Call::remark(vec![0; size])),
			}
		]
	)
}

#[test]
fn panic_execution_with_foreign_code_gives_error() {
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(BLOATY_CODE, Storage {
		top: map![
			<frame_system::Account<Runtime>>::hashed_key_for(alice()) => {
				(69u128, 0u8, 0u128, 0u128, 0u128).encode()
			},
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				69_u128.encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => {
				vec![0u8; 32]
			}
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		true,
		None,
	).0;
	assert!(r.is_ok());
	let v = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		true,
		None,
	).0.unwrap();
	let r = ApplyExtrinsicResult::decode(&mut &v.as_encoded()[..]).unwrap();
	assert_eq!(r, Err(InvalidTransaction::Payment.into()));
}

#[test]
fn bad_extrinsic_with_native_equivalent_code_gives_error() {
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(COMPACT_CODE, Storage {
		top: map![
			<frame_system::Account<Runtime>>::hashed_key_for(alice()) => {
				(0u32, 0u8, 69u128, 0u128, 0u128, 0u128).encode()
			},
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				69_u128.encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => {
				vec![0u8; 32]
			}
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		true,
		None,
	).0;
	assert!(r.is_ok());
	let v = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		true,
		None,
	).0.unwrap();
	let r = ApplyExtrinsicResult::decode(&mut &v.as_encoded()[..]).unwrap();
	assert_eq!(r, Err(InvalidTransaction::Payment.into()));
}

#[test]
fn successful_execution_with_native_equivalent_code_gives_ok() {
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(COMPACT_CODE, Storage {
		top: map![
			<frame_system::Account<Runtime>>::hashed_key_for(alice()) => {
				(0u32, 0u8, 111 * DOLLARS, 0u128, 0u128, 0u128).encode()
			},
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		true,
		None,
	).0;
	assert!(r.is_ok());

	let fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		true,
		None,
	).0;
	assert!(r.is_ok());

	t.execute_with(|| {
		let fees = transfer_fee(&xt(), fm);
		assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - fees);
		assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
	});
}

#[test]
fn successful_execution_with_foreign_code_gives_ok() {
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(BLOATY_CODE, Storage {
		top: map![
			<frame_system::Account<Runtime>>::hashed_key_for(alice()) => {
				(0u32, 0u8, 111 * DOLLARS, 0u128, 0u128, 0u128).encode()
			},
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		true,
		None,
	).0;
	assert!(r.is_ok());

	let fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		true,
		None,
	).0;
	assert!(r.is_ok());

	t.execute_with(|| {
		let fees = transfer_fee(&xt(), fm);
		assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - fees);
		assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
	});
}

#[test]
fn full_native_block_import_works() {
	let mut t = new_test_ext(COMPACT_CODE, false);

	let (block1, block2) = blocks();

	let mut alice_last_known_balance: Balance = Default::default();
	let mut fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block1.0,
		true,
		None,
	).0.unwrap();

	t.execute_with(|| {
		let fees = transfer_fee(&xt(), fm);
		assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - fees);
		assert_eq!(Balances::total_balance(&bob()), 169 * DOLLARS);
		alice_last_known_balance = Balances::total_balance(&alice());
		let events = vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				// timestamp set call with weight 8_000_000 + 2 read + 1 write
				event: Event::frame_system(frame_system::RawEvent::ExtrinsicSuccess(
					DispatchInfo { weight: 8_000_000 + 2 * 25_000_000 + 1 * 100_000_000, class: DispatchClass::Mandatory, ..Default::default() }
				)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				event: Event::pallet_balances(pallet_balances::RawEvent::Transfer(
					alice().into(),
					bob().into(),
					69 * DOLLARS,
				)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				event: Event::pallet_treasury(pallet_treasury::RawEvent::Deposit(fees * 8 / 10)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				// Balance Transfer 70_000_000 + 1 Read + 1 Write
				event: Event::frame_system(frame_system::RawEvent::ExtrinsicSuccess(
					DispatchInfo { weight: 70_000_000 + 25_000_000 + 100_000_000, ..Default::default() }
				)),
				topics: vec![],
			},
		];
		assert_eq!(System::events(), events);
	});

	fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block2.0,
		true,
		None,
	).0.unwrap();

	t.execute_with(|| {
		let fees = transfer_fee(&xt(), fm);
		assert_eq!(
			Balances::total_balance(&alice()),
			alice_last_known_balance - 10 * DOLLARS - fees,
		);
		assert_eq!(
			Balances::total_balance(&bob()),
			179 * DOLLARS - fees,
		);
		let events = vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				// timestamp set call with weight 8_000_000 + 2 read + 1 write
				event: Event::frame_system(frame_system::RawEvent::ExtrinsicSuccess(
					DispatchInfo { weight: 8_000_000 + 2 * 25_000_000 + 1 * 100_000_000, class: DispatchClass::Mandatory, ..Default::default() }
				)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				event: Event::pallet_balances(
					pallet_balances::RawEvent::Transfer(
						bob().into(),
						alice().into(),
						5 * DOLLARS,
					)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				event: Event::pallet_treasury(pallet_treasury::RawEvent::Deposit(fees * 8 / 10)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				// Balance Transfer 70_000_000 + 1 Read + 1 Write
				event: Event::frame_system(frame_system::RawEvent::ExtrinsicSuccess(
					DispatchInfo { weight: 70_000_000 + 25_000_000 + 100_000_000, ..Default::default() }
				)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(2),
				event: Event::pallet_balances(
					pallet_balances::RawEvent::Transfer(
						alice().into(),
						bob().into(),
						15 * DOLLARS,
					)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(2),
				event: Event::pallet_treasury(pallet_treasury::RawEvent::Deposit(fees * 8 / 10)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(2),
				// Balance Transfer 70_000_000 + 1 Read + 1 Write
				event: Event::frame_system(frame_system::RawEvent::ExtrinsicSuccess(
					DispatchInfo { weight: 70_000_000 + 25_000_000 + 100_000_000, ..Default::default() }
				)),
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

	let mut alice_last_known_balance: Balance = Default::default();
	let mut fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block1.0,
		false,
		None,
	).0.unwrap();

	t.execute_with(|| {
		assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - transfer_fee(&xt(), fm));
		assert_eq!(Balances::total_balance(&bob()), 169 * DOLLARS);
		alice_last_known_balance = Balances::total_balance(&alice());
	});

	fm = t.execute_with(TransactionPayment::next_fee_multiplier);

	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block2.0,
		false,
		None,
	).0.unwrap();

	t.execute_with(|| {
		assert_eq!(
			Balances::total_balance(&alice()),
			alice_last_known_balance - 10 * DOLLARS - transfer_fee(&xt(), fm),
		);
		assert_eq!(
			Balances::total_balance(&bob()),
			179 * DOLLARS - 1 * transfer_fee(&xt(), fm),
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
	let transfer_ch = <Runtime as frame_system::Trait>::Hashing::hash(&transfer_code);

	let addr = <Runtime as pallet_contracts::Trait>::DetermineContractAddress::contract_address_for(
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
				function: Call::Timestamp(pallet_timestamp::Call::set(42 * 1000)),
			},
			CheckedExtrinsic {
				signed: Some((charlie(), signed_extra(0, 0))),
				function: Call::Contracts(
					pallet_contracts::Call::put_code::<Runtime>(transfer_code)
				),
			},
			CheckedExtrinsic {
				signed: Some((charlie(), signed_extra(1, 0))),
				function: Call::Contracts(
					pallet_contracts::Call::instantiate::<Runtime>(
						1 * DOLLARS,
						500_000_000,
						transfer_ch,
						Vec::new()
					)
				),
			},
			CheckedExtrinsic {
				signed: Some((charlie(), signed_extra(2, 0))),
				function: Call::Contracts(
					pallet_contracts::Call::call::<Runtime>(
						pallet_indices::address::Address::Id(addr.clone()),
						10,
						500_000_000,
						vec![0x00, 0x01, 0x02, 0x03]
					)
				),
			},
		]
	);

	let mut t = new_test_ext(COMPACT_CODE, false);

	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&b.0,
		false,
		None,
	).0.unwrap();

	t.execute_with(|| {
		// Verify that the contract constructor worked well and code of TRANSFER contract is actually deployed.
		assert_eq!(
			&pallet_contracts::ContractInfoOf::<Runtime>::get(addr)
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

	set_heap_pages(&mut t.ext(), 4);

	let result = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block_with_size(42, 0, 120_000).0,
		false,
		None,
	).0;
	assert!(result.is_err()); // Err(Wasmi(Trap(Trap { kind: Host(AllocatorOutOfSpace) })))
}

#[test]
fn native_big_block_import_succeeds() {
	let mut t = new_test_ext(COMPACT_CODE, false);

	executor_call::<NeverNativeValue, fn() -> _>(
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
		executor_call::<NeverNativeValue, fn() -> _>(
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
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(BLOATY_CODE, Storage {
		top: map![
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				0_u128.encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		false,
		None,
	).0;
	assert!(r.is_ok());
	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		false,
		None,
	).0.unwrap().into_encoded();
	let r = ApplyExtrinsicResult::decode(&mut &r[..]).unwrap();
	assert_eq!(r, Err(InvalidTransaction::Payment.into()));
}

#[test]
fn successful_execution_gives_ok() {
	let mut t = TestExternalities::<BlakeTwo256>::new_with_code(COMPACT_CODE, Storage {
		top: map![
			<frame_system::Account<Runtime>>::hashed_key_for(alice()) => {
				(0u32, 0u8, 111 * DOLLARS, 0u128, 0u128, 0u128).encode()
			},
			<pallet_balances::TotalIssuance<Runtime>>::hashed_key().to_vec() => {
				(111 * DOLLARS).encode()
			},
			<frame_system::BlockHash<Runtime>>::hashed_key_for(0) => vec![0u8; 32]
		],
		children_default: map![],
	});

	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_initialize_block",
		&vec![].and(&from_block_number(1u32)),
		false,
		None,
	).0;
	assert!(r.is_ok());
	let fm = t.execute_with(TransactionPayment::next_fee_multiplier);
	let r = executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"BlockBuilder_apply_extrinsic",
		&vec![].and(&xt()),
		false,
		None,
	).0.unwrap().into_encoded();
	ApplyExtrinsicResult::decode(&mut &r[..])
		.unwrap()
		.expect("Extrinsic could not be applied")
		.expect("Extrinsic failed");

	t.execute_with(|| {
		let fees = transfer_fee(&xt(), fm);
		assert_eq!(Balances::total_balance(&alice()), 42 * DOLLARS - fees);
		assert_eq!(Balances::total_balance(&bob()), 69 * DOLLARS);
	});
}

#[test]
fn full_native_block_import_works_with_changes_trie() {
	let block1 = changes_trie_block();
	let block_data = block1.0;
	let block = Block::decode(&mut &block_data[..]).unwrap();

	let mut t = new_test_ext(COMPACT_CODE, true);
	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block.encode(),
		true,
		None,
	).0.unwrap();

	assert!(t.ext().storage_changes_root(&GENESIS_HASH).unwrap().is_some());
}

#[test]
fn full_wasm_block_import_works_with_changes_trie() {
	let block1 = changes_trie_block();

	let mut t = new_test_ext(COMPACT_CODE, true);
	executor_call::<NeverNativeValue, fn() -> _>(
		&mut t,
		"Core_execute_block",
		&block1.0,
		false,
		None,
	).0.unwrap();

	assert!(t.ext().storage_changes_root(&GENESIS_HASH).unwrap().is_some());
}

#[test]
fn should_import_block_with_test_client() {
	use node_testing::client::{
		ClientBlockImportExt, TestClientBuilderExt, TestClientBuilder,
		sp_consensus::BlockOrigin,
	};

	let mut client = TestClientBuilder::new().build();
	let block1 = changes_trie_block();
	let block_data = block1.0;
	let block = node_primitives::Block::decode(&mut &block_data[..]).unwrap();

	client.import(BlockOrigin::Own, block).unwrap();
}
