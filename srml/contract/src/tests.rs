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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use double_map::StorageDoubleMap;
use runtime_io::with_externalities;
use runtime_primitives::testing::{Digest, DigestItem, H256, Header};
use runtime_primitives::traits::{BlakeTwo256};
use runtime_primitives::BuildStorage;
use runtime_support::StorageMap;
use substrate_primitives::{Blake2Hasher};
use system::{Phase, EventRecord};
use wabt;
use {
	runtime_io, balances, system, CodeOf, ContractAddressFor,
	GenesisConfig, Module, StorageOf, Trait, RawEvent,
};

impl_outer_origin! {
	pub enum Origin for Test {}
}

mod contract {
	pub use super::super::*;
}
impl_outer_event! {
	pub enum MetaEvent for Test {
		balances<T>, contract<T>,
	}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
	type Event = MetaEvent;
	type Log = DigestItem;
}
impl balances::Trait for Test {
	type Balance = u64;
	type AccountIndex = u64;
	type OnFreeBalanceZero = Contract;
	type EnsureAccountLiquid = ();
	type Event = MetaEvent;
}
impl Trait for Test {
	type Gas = u64;
	type DetermineContractAddress = DummyContractAddressFor;
	type Event = MetaEvent;
}

type Balances = balances::Module<Test>;
type Contract = Module<Test>;
type System = system::Module<Test>;

pub struct DummyContractAddressFor;
impl ContractAddressFor<u64> for DummyContractAddressFor {
	fn contract_address_for(_code: &[u8], _data: &[u8], origin: &u64) -> u64 {
		origin + 1
	}
}

struct ExtBuilder {
	existential_deposit: u64,
	gas_price: u64,
	block_gas_limit: u64,
	transfer_fee: u64,
	creation_fee: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 0,
			gas_price: 2,
			block_gas_limit: 100_000_000,
			transfer_fee: 0,
			creation_fee: 0,
		}
	}
}
impl ExtBuilder {
	fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	fn gas_price(mut self, gas_price: u64) -> Self {
		self.gas_price = gas_price;
		self
	}
	fn block_gas_limit(mut self, block_gas_limit: u64) -> Self {
		self.block_gas_limit = block_gas_limit;
		self
	}
	fn transfer_fee(mut self, transfer_fee: u64) -> Self {
		self.transfer_fee = transfer_fee;
		self
	}
	fn creation_fee(mut self, creation_fee: u64) -> Self {
		self.creation_fee = creation_fee;
		self
	}
	fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default()
			.build_storage()
			.unwrap();
		t.extend(
			balances::GenesisConfig::<Test> {
				balances: vec![],
				transaction_base_fee: 0,
				transaction_byte_fee: 0,
				existential_deposit: self.existential_deposit,
				transfer_fee: self.transfer_fee,
				creation_fee: self.creation_fee,
				reclaim_rebate: 0,
			}.build_storage()
			.unwrap(),
		);
		t.extend(
			GenesisConfig::<Test> {
				contract_fee: 21,
				call_base_fee: 135,
				create_base_fee: 175,
				gas_price: self.gas_price,
				max_depth: 100,
				block_gas_limit: self.block_gas_limit,
			}.build_storage()
			.unwrap(),
		);
		runtime_io::TestExternalities::new(t)
	}
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
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 8)  ;; Length of "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 12)  ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer.
				(i32.const 0)   ;; Pointer to input data buffer address
				(i32.const 0)   ;; Length of input data buffer
			)
		)
	)
	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")
)
"#;

#[test]
fn contract_transfer() {
	const CONTRACT_SHOULD_TRANSFER_VALUE: u64 = 6;
	const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		<CodeOf<Test>>::insert(1, code_transfer.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&1, 11);
		Balances::increase_total_stake_by(11);

		assert_ok!(Contract::call(Origin::signed(0), 1, 3, 100_000, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 3 - value sent with the transaction
			// 2 * 10 - gas used by the contract (10) multiplied by gas price (2)
			// 2 * 135 - base gas fee for call (by transaction)
			// 2 * 135 - base gas fee for call (by the contract)
			100_000_000 - 3 - (2 * 10) - (2 * 135) - (2 * 135),
		);
		assert_eq!(
			Balances::free_balance(&1),
			11 + 3 - CONTRACT_SHOULD_TRANSFER_VALUE,
		);
		assert_eq!(
			Balances::free_balance(&CONTRACT_SHOULD_TRANSFER_TO),
			CONTRACT_SHOULD_TRANSFER_VALUE,
		);

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					balances::RawEvent::NewAccount(
						CONTRACT_SHOULD_TRANSFER_TO,
						0,
						balances::NewAccountOutcome::NoHint
					)
				),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(0, 1, 3)),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(1, CONTRACT_SHOULD_TRANSFER_TO, 6)),
			},
		]);
	});
}

#[test]
fn contract_transfer_takes_creation_fee() {
	const CONTRACT_SHOULD_TRANSFER_VALUE: u64 = 6;
	const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

	with_externalities(&mut ExtBuilder::default().creation_fee(105).build(), || {
		<CodeOf<Test>>::insert(1, code_transfer.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&1, 11);
		Balances::increase_total_stake_by(11);

		assert_ok!(Contract::call(Origin::signed(0), 1, 3, 100_000, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 3 - value sent with the transaction
			// 2 * 10 - gas used by the contract (10) multiplied by gas price (2)
			// 2 * 135 - base gas fee for call (by transaction)
			// 2 * 135 - base gas fee for call (by the contract)
			// 104 - (rounded) fee per creation (by the contract)
			100_000_000 - 3 - (2 * 10) - (2 * 135) - (2 * 135) - 104,
		);
		assert_eq!(
			Balances::free_balance(&1),
			11 + 3 - CONTRACT_SHOULD_TRANSFER_VALUE,
		);
		assert_eq!(
			Balances::free_balance(&CONTRACT_SHOULD_TRANSFER_TO),
			CONTRACT_SHOULD_TRANSFER_VALUE,
		);
	});
}

#[test]
fn contract_transfer_takes_transfer_fee() {
	const CONTRACT_SHOULD_TRANSFER_VALUE: u64 = 6;
	const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

	with_externalities(&mut ExtBuilder::default().creation_fee(105).transfer_fee(45).build(), || {
		<CodeOf<Test>>::insert(1, code_transfer.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&1, 11);
		Balances::increase_total_stake_by(11);

		// Create destination account here so we can check that transfer fee
		// is charged (and creation fee is not).
		Balances::set_free_balance(&CONTRACT_SHOULD_TRANSFER_TO, 25);

		assert_ok!(Contract::call(Origin::signed(0), 1, 3, 100_000, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 3 - value sent with the transaction
			// 2 * 10 - gas used by the contract (10) multiplied by gas price (2)
			// 2 * 135 - base gas fee for call (by transaction)
			// 44 - (rounded from 45) fee per transfer (by transaction)
			// 2 * 135 - base gas fee for call (by the contract)
			// 44 - (rounded from 45) fee per transfer (by the contract)
			100_000_000 - 3 - (2 * 10) - (2 * 135) - 44 - (2 * 135) - 44,
		);
		assert_eq!(
			Balances::free_balance(&1),
			11 + 3 - CONTRACT_SHOULD_TRANSFER_VALUE,
		);
		assert_eq!(
			Balances::free_balance(&CONTRACT_SHOULD_TRANSFER_TO),
			25 + CONTRACT_SHOULD_TRANSFER_VALUE,
		);
	});
}

#[test]
fn contract_transfer_oog() {
	const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		<CodeOf<Test>>::insert(1, code_transfer.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&1, 11);
		Balances::increase_total_stake_by(11);

		assert_ok!(Contract::call(Origin::signed(0), 1, 3, 135 + 135 + 7, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 3 - value sent with the transaction
			// 2 * 7 - gas used by the contract (7) multiplied by gas price (2)
			// 2 * 135 - base gas fee for call (by transaction)
			// 2 * 135 - base gas fee for call (by contract)
			100_000_000 - 3 - (2 * 7) - (2 * 135) - (2 * 135),
		);

		// Transaction level transfer should succeed.
		assert_eq!(Balances::free_balance(&1), 14);
		// But `ext_call` should not.
		assert_eq!(Balances::free_balance(&CONTRACT_SHOULD_TRANSFER_TO), 0);

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(0, 1, 3)),
			},
		]);
	});
}

#[test]
fn contract_transfer_max_depth() {
	const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		<CodeOf<Test>>::insert(CONTRACT_SHOULD_TRANSFER_TO, code_transfer.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&CONTRACT_SHOULD_TRANSFER_TO, 11);
		Balances::increase_total_stake_by(11);

		assert_ok!(Contract::call(Origin::signed(0), CONTRACT_SHOULD_TRANSFER_TO, 3, 100_000, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 3 - value sent with the transaction
			// 2 * 10 * 100 - gas used by the contract (10) multiplied by gas price (2)
			//                multiplied by max depth (100).
			// 2 * 135 * 100 - base gas fee for call (by transaction) multiplied by max depth (100).
			100_000_000 - 3 - (2 * 10 * 100) - (2 * 135 * 100),
		);
		assert_eq!(Balances::free_balance(&CONTRACT_SHOULD_TRANSFER_TO), 14);
	});
}

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

/// Returns code that uses `ext_create` runtime call.
///
/// Takes bytecode of the contract that needs to be deployed.
fn code_create(constructor: &[u8]) -> String {
	format!(
		r#"
(module
	;; ext_create(
	;;     code_ptr: u32,
	;;     code_len: u32,
	;;     gas: u64,
	;;     value_ptr: u32,
	;;     value_len: u32,
	;;     input_data_ptr: u32,
	;;     input_data_len: u32,
	;; ) -> u32
	(import "env" "ext_create" (func $ext_create (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_create
				(i32.const 12)   ;; Pointer to `code`
				(i32.const {code_len}) ;; Length of `code`
				(i64.const 0)   ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)   ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer
				(i32.const 0)   ;; Pointer to input data buffer address
				(i32.const 0)   ;; Length of input data buffer
			)
		)
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Embedded wasm code.
	(data (i32.const 12) "{escaped_constructor}")
)
"#,
		escaped_constructor = escaped_bytestring(constructor),
		code_len = constructor.len(),
	)
}

#[test]
fn contract_create() {
	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
	let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();
	let code_create = wabt::wat2wasm(&code_create(&code_ctor_transfer)).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&1, 0);
		Balances::set_free_balance(&9, 30);
		Balances::increase_total_stake_by(30);

		<CodeOf<Test>>::insert(1, code_create.to_vec());

		// When invoked, the contract at address `1` must create a contract with 'transfer' code.
		assert_ok!(Contract::call(Origin::signed(0), 1, 11, 100_000, Vec::new()));

		let derived_address = <Test as Trait>::DetermineContractAddress::contract_address_for(
			&code_ctor_transfer,
			&[],
			&1,
		);

		// 11 - value sent with the transaction
		// 2 * 139 - gas spent by the deployer contract (139) multiplied by gas price (2)
		// 2 * 135 - base gas fee for call (top level)
		// 2 * 175 - base gas fee for create (by contract)
		// ((21 / 2) * 2) - price per account creation
		let expected_gas_after_create =
			100_000_000 - 11 - (2 * 139) - (2 * 135) - (2 * 175) - ((21 / 2) * 2);
		assert_eq!(Balances::free_balance(&0), expected_gas_after_create);
		assert_eq!(Balances::free_balance(&1), 8);
		assert_eq!(Balances::free_balance(&derived_address), 3);

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					balances::RawEvent::NewAccount(
						derived_address,
						0,
						balances::NewAccountOutcome::NoHint
					)
				),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(0, 1, 11)),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(1, 2, 3)),
			},
		]);

		// Initiate transfer to the newly created contract.
		assert_ok!(Contract::call(Origin::signed(0), derived_address, 22, 100_000, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 22 - value sent with the transaction
			// (2 * 10) - gas used by the contract
			// (2 * 135) - base gas fee for call (top level)
			// (2 * 135) - base gas fee for call (by transfer contract)
			expected_gas_after_create - 22 - (2 * 10) - (2 * 135) - (2 * 135),
		);
		assert_eq!(Balances::free_balance(&derived_address), 22 - 3);
		assert_eq!(Balances::free_balance(&9), 36);
	});
}

#[test]
fn top_level_create() {
	let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
	let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();

	with_externalities(&mut ExtBuilder::default().gas_price(3).build(), || {
		let derived_address = <Test as Trait>::DetermineContractAddress::contract_address_for(
			&code_ctor_transfer,
			&[],
			&0,
		);

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);
		Balances::set_free_balance(&derived_address, 30);
		Balances::increase_total_stake_by(30);

		assert_ok!(Contract::create(
			Origin::signed(0),
			11,
			100_000,
			code_ctor_transfer.clone(),
			Vec::new(),
		));

		// 11 - value sent with the transaction
		// (3 * 129) - gas spent by the init_code.
		// (3 * 175) - base gas fee for create (175) (top level) multipled by gas price (3)
		// ((21 / 3) * 3) - price for contract creation
		assert_eq!(
			Balances::free_balance(&0),
			100_000_000 - 11 - (3 * 129) - (3 * 175) - ((21 / 3) * 3)
		);
		assert_eq!(Balances::free_balance(&derived_address), 30 + 11);

		assert_eq!(<CodeOf<Test>>::get(&derived_address), code_transfer);

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(0, derived_address, 11)),
			},
		]);
	});
}

const CODE_NOP: &'static str = r#"
(module
	(func (export "call")
		nop
	)
)
"#;

#[test]
fn refunds_unused_gas() {
	let code_nop = wabt::wat2wasm(CODE_NOP).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		<CodeOf<Test>>::insert(1, code_nop.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);

		assert_ok!(Contract::call(Origin::signed(0), 1, 0, 100_000, Vec::new()));

		assert_eq!(Balances::free_balance(&0), 100_000_000 - 4 - (2 * 135));
	});
}

#[test]
fn call_with_zero_value() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		<CodeOf<Test>>::insert(1, vec![]);

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);

		assert_ok!(Contract::call(Origin::signed(0), 1, 0, 100_000, Vec::new()));

		assert_eq!(Balances::free_balance(&0), 100_000_000 - (2 * 135));
	});
}

#[test]
fn create_with_zero_endowment() {
	let code_nop = wabt::wat2wasm(CODE_NOP).unwrap();

	with_externalities(&mut ExtBuilder::default().build(), || {
		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);

		assert_ok!(Contract::create(Origin::signed(0), 0, 100_000, code_nop, Vec::new()));

		assert_eq!(
			Balances::free_balance(&0),
			// 4 - for the gas spent by the constructor
			// 2 * 175 - base gas fee for create (175) multiplied by gas price (2) (top level)
			100_000_000 - 4 - (2 * 175),
		);
	});
}

#[test]
fn account_removal_removes_storage() {
	with_externalities(
		&mut ExtBuilder::default().existential_deposit(100).build(),
		|| {
			// Setup two accounts with free balance above than exsistential threshold.
			{
				Balances::set_free_balance(&1, 110);
				Balances::increase_total_stake_by(110);
				<StorageOf<Test>>::insert(1, b"foo".to_vec(), b"1".to_vec());
				<StorageOf<Test>>::insert(1, b"bar".to_vec(), b"2".to_vec());

				Balances::set_free_balance(&2, 110);
				Balances::increase_total_stake_by(110);
				<StorageOf<Test>>::insert(2, b"hello".to_vec(), b"3".to_vec());
				<StorageOf<Test>>::insert(2, b"world".to_vec(), b"4".to_vec());
			}

			// Transfer funds from account 1 of such amount that after this transfer
			// the balance of account 1 is will be below than exsistential threshold.
			//
			// This should lead to the removal of all storage associated with this account.
			assert_ok!(Balances::transfer(Origin::signed(1), 2.into(), 20));

			// Verify that all entries from account 1 is removed, while
			// entries from account 2 is in place.
			{
				assert_eq!(<StorageOf<Test>>::get(1, b"foo".to_vec()), None);
				assert_eq!(<StorageOf<Test>>::get(1, b"bar".to_vec()), None);

				assert_eq!(
					<StorageOf<Test>>::get(2, b"hello".to_vec()),
					Some(b"3".to_vec())
				);
				assert_eq!(
					<StorageOf<Test>>::get(2, b"world".to_vec()),
					Some(b"4".to_vec())
				);
			}
		},
	);
}

const CODE_UNREACHABLE: &'static str = r#"
(module
	(func (export "call")
		nop
		unreachable
	)
)
"#;

#[test]
fn top_level_call_refunds_even_if_fails() {
	let code_unreachable = wabt::wat2wasm(CODE_UNREACHABLE).unwrap();
	with_externalities(&mut ExtBuilder::default().gas_price(4).build(), || {
		<CodeOf<Test>>::insert(1, code_unreachable.to_vec());

		Balances::set_free_balance(&0, 100_000_000);
		Balances::increase_total_stake_by(100_000_000);

		assert_err!(
			Contract::call(Origin::signed(0), 1, 0, 100_000, Vec::new()),
			"vm execute returned error while call"
		);

		assert_eq!(Balances::free_balance(&0), 100_000_000 - (4 * 3) - (4 * 135));

		assert_eq!(System::events(), vec![]);
	});
}

const CODE_LOOP: &'static str = r#"
(module
	(func (export "call")
		(loop
			(br 0)
		)
	)
)
"#;

#[test]
fn block_gas_limit() {
	let code_loop = wabt::wat2wasm(CODE_LOOP).unwrap();
	with_externalities(
		&mut ExtBuilder::default().block_gas_limit(100_000).build(),
		|| {
			<CodeOf<Test>>::insert(1, code_loop.to_vec());

			Balances::set_free_balance(&0, 100_000_000);
			Balances::increase_total_stake_by(100_000_000);

			// Spend 50_000 units of gas (OOG).
			assert_err!(
				Contract::call(Origin::signed(0), 1, 0, 50_000, Vec::new()),
				"vm execute returned error while call"
			);

			// Ensure we can't spend more gas than available in block gas limit.
			assert_err!(
				Contract::call(Origin::signed(0), 1, 0, 50_001, Vec::new()),
				"block gas limit is reached"
			);

			// However, we can spend another 50_000
			assert_err!(
				Contract::call(Origin::signed(0), 1, 0, 50_000, Vec::new()),
				"vm execute returned error while call"
			);
		},
	);
}

const CODE_INPUT_DATA: &'static str = r#"
(module
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

			(return)
		)
		unreachable
	)
)
"#;

#[test]
fn input_data() {
	let code_input_data = wabt::wat2wasm(CODE_INPUT_DATA).unwrap();
	with_externalities(
		&mut ExtBuilder::default().build(),
		|| {
			<CodeOf<Test>>::insert(1, code_input_data.to_vec());

			Balances::set_free_balance(&0, 100_000_000);
			Balances::increase_total_stake_by(100_000_000);

			assert_ok!(Contract::call(Origin::signed(0), 1, 0, 50_000, vec![0, 1, 2, 3]));

			// all asserts are made within contract code itself.
		},
	);
}
