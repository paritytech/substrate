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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

// TODO: #1417 Add more integration tests
// also remove the #![allow(unused)] below.

#![allow(unused)]

use crate::{
	BalanceOf, ComputeDispatchFee, ContractAddressFor, ContractInfo, ContractInfoOf, GenesisConfig,
	Module, RawAliveContractInfo, RawEvent, Trait, TrieId, TrieIdFromParentCounter, Schedule,
	TrieIdGenerator, CheckBlockGasLimit, account_db::{AccountDb, DirectAccountDb, OverlayAccountDb},
};
use assert_matches::assert_matches;
use hex_literal::*;
use codec::{Decode, Encode, KeyedVec};
use sp_runtime::{
	Perbill, BuildStorage, transaction_validity::{InvalidTransaction, ValidTransaction},
	traits::{BlakeTwo256, Hash, IdentityLookup, SignedExtension},
	testing::{Digest, DigestItem, Header, UintAuthorityId, H256},
};
use frame_support::{
	assert_ok, assert_err, impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
	storage::child, StorageMap, StorageValue, traits::{Currency, Get},
	weights::{DispatchInfo, DispatchClass, Weight},
};
use std::{cell::RefCell, sync::atomic::{AtomicUsize, Ordering}};
use sp_core::storage::well_known_keys;
use frame_system::{self as system, EventRecord, Phase};

mod contract {
	// Re-export contents of the root. This basically
	// needs to give a name for the current crate.
	// This hack is required for `impl_outer_event!`.
	pub use super::super::*;
	use frame_support::impl_outer_event;
}

use pallet_balances as balances;

impl_outer_event! {
	pub enum MetaEvent for Test {
		balances<T>, contract<T>,
	}
}
impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system { }
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		balances::Balances,
		contract::Contract,
	}
}

thread_local! {
	static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
	static TRANSFER_FEE: RefCell<u64> = RefCell::new(0);
	static INSTANTIATION_FEE: RefCell<u64> = RefCell::new(0);
	static BLOCK_GAS_LIMIT: RefCell<u64> = RefCell::new(0);
}

pub struct ExistentialDeposit;
impl Get<u64> for ExistentialDeposit {
	fn get() -> u64 { EXISTENTIAL_DEPOSIT.with(|v| *v.borrow()) }
}

pub struct TransferFee;
impl Get<u64> for TransferFee {
	fn get() -> u64 { TRANSFER_FEE.with(|v| *v.borrow()) }
}

pub struct CreationFee;
impl Get<u64> for CreationFee {
	fn get() -> u64 { INSTANTIATION_FEE.with(|v| *v.borrow()) }
}

pub struct BlockGasLimit;
impl Get<u64> for BlockGasLimit {
	fn get() -> u64 { BLOCK_GAS_LIMIT.with(|v| *v.borrow()) }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = ();
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = MetaEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
	type ModuleToIndex = ();
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type OnReapAccount = (System, Contract);
	type OnNewAccount = ();
	type Event = MetaEvent;
	type DustRemoval = ();
	type TransferPayment = ();
	type ExistentialDeposit = ExistentialDeposit;
	type CreationFee = CreationFee;
}
parameter_types! {
	pub const MinimumPeriod: u64 = 1;
}
impl pallet_timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
}
parameter_types! {
	pub const SignedClaimHandicap: u64 = 2;
	pub const TombstoneDeposit: u64 = 16;
	pub const StorageSizeOffset: u32 = 8;
	pub const RentByteFee: u64 = 4;
	pub const RentDepositOffset: u64 = 10_000;
	pub const SurchargeReward: u64 = 150;
	pub const TransactionBaseFee: u64 = 2;
	pub const TransactionByteFee: u64 = 6;
	pub const ContractFee: u64 = 21;
	pub const CallBaseFee: u64 = 135;
	pub const InstantiateBaseFee: u64 = 175;
	pub const MaxDepth: u32 = 100;
	pub const MaxValueSize: u32 = 16_384;
}
impl Trait for Test {
	type Currency = Balances;
	type Time = Timestamp;
	type Randomness = Randomness;
	type Call = Call;
	type DetermineContractAddress = DummyContractAddressFor;
	type Event = MetaEvent;
	type ComputeDispatchFee = DummyComputeDispatchFee;
	type TrieIdGenerator = DummyTrieIdGenerator;
	type GasPayment = ();
	type RentPayment = ();
	type SignedClaimHandicap = SignedClaimHandicap;
	type TombstoneDeposit = TombstoneDeposit;
	type StorageSizeOffset = StorageSizeOffset;
	type RentByteFee = RentByteFee;
	type RentDepositOffset = RentDepositOffset;
	type SurchargeReward = SurchargeReward;
	type CreationFee = CreationFee;
	type TransactionBaseFee = TransactionBaseFee;
	type TransactionByteFee = TransactionByteFee;
	type ContractFee = ContractFee;
	type CallBaseFee = CallBaseFee;
	type InstantiateBaseFee = InstantiateBaseFee;
	type MaxDepth = MaxDepth;
	type MaxValueSize = MaxValueSize;
	type BlockGasLimit = BlockGasLimit;
}

type Balances = pallet_balances::Module<Test>;
type Timestamp = pallet_timestamp::Module<Test>;
type Contract = Module<Test>;
type System = frame_system::Module<Test>;
type Randomness = pallet_randomness_collective_flip::Module<Test>;

pub struct DummyContractAddressFor;
impl ContractAddressFor<H256, u64> for DummyContractAddressFor {
	fn contract_address_for(_code_hash: &H256, _data: &[u8], origin: &u64) -> u64 {
		*origin + 1
	}
}

pub struct DummyTrieIdGenerator;
impl TrieIdGenerator<u64> for DummyTrieIdGenerator {
	fn trie_id(account_id: &u64) -> TrieId {
		use sp_core::storage::well_known_keys;

		let new_seed = super::AccountCounter::mutate(|v| {
			*v = v.wrapping_add(1);
			*v
		});

		// TODO: see https://github.com/paritytech/substrate/issues/2325
		let mut res = vec![];
		res.extend_from_slice(well_known_keys::CHILD_STORAGE_KEY_PREFIX);
		res.extend_from_slice(b"default:");
		res.extend_from_slice(&new_seed.to_le_bytes());
		res.extend_from_slice(&account_id.to_le_bytes());
		res
	}
}

pub struct DummyComputeDispatchFee;
impl ComputeDispatchFee<Call, u64> for DummyComputeDispatchFee {
	fn compute_dispatch_fee(call: &Call) -> u64 {
		69
	}
}

const ALICE: u64 = 1;
const BOB: u64 = 2;
const CHARLIE: u64 = 3;
const DJANGO: u64 = 4;

pub struct ExtBuilder {
	existential_deposit: u64,
	gas_price: u64,
	block_gas_limit: u64,
	transfer_fee: u64,
	instantiation_fee: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 0,
			gas_price: 2,
			block_gas_limit: 100_000_000,
			transfer_fee: 0,
			instantiation_fee: 0,
		}
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn gas_price(mut self, gas_price: u64) -> Self {
		self.gas_price = gas_price;
		self
	}
	pub fn block_gas_limit(mut self, block_gas_limit: u64) -> Self {
		self.block_gas_limit = block_gas_limit;
		self
	}
	pub fn transfer_fee(mut self, transfer_fee: u64) -> Self {
		self.transfer_fee = transfer_fee;
		self
	}
	pub fn instantiation_fee(mut self, instantiation_fee: u64) -> Self {
		self.instantiation_fee = instantiation_fee;
		self
	}
	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
		TRANSFER_FEE.with(|v| *v.borrow_mut() = self.transfer_fee);
		INSTANTIATION_FEE.with(|v| *v.borrow_mut() = self.instantiation_fee);
		BLOCK_GAS_LIMIT.with(|v| *v.borrow_mut() = self.block_gas_limit);
	}
	pub fn build(self) -> sp_io::TestExternalities {
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::<Test> {
			current_schedule: Schedule {
				enable_println: true,
				..Default::default()
			},
			gas_price: self.gas_price,
		}.assimilate_storage(&mut t).unwrap();
		sp_io::TestExternalities::new(t)
	}
}

/// Generate Wasm binary and code hash from wabt source.
fn compile_module<T>(wabt_module: &str)
	-> Result<(Vec<u8>, <T::Hashing as Hash>::Output), wabt::Error>
	where T: frame_system::Trait
{
	let wasm = wabt::wat2wasm(wabt_module)?;
	let code_hash = T::Hashing::hash(&wasm);
	Ok((wasm, code_hash))
}

// Perform a simple transfer to a non-existent account supplying way more gas than needed.
// Then we check that the all unused gas is refunded.
#[test]
fn refunds_unused_gas() {
	ExtBuilder::default().gas_price(2).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 100_000_000);

		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, Vec::new()));

		// 2 * 135 - gas price multiplied by the call base fee.
		assert_eq!(Balances::free_balance(ALICE), 100_000_000 - (2 * 135));
	});
}

#[test]
fn account_removal_removes_storage() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let trie_id1 = <Test as Trait>::TrieIdGenerator::trie_id(&1);
		let trie_id2 = <Test as Trait>::TrieIdGenerator::trie_id(&2);
		let key1 = &[1; 32];
		let key2 = &[2; 32];

		// Set up two accounts with free balance above the existential threshold.
		{
			Balances::deposit_creating(&1, 110);
			ContractInfoOf::<Test>::insert(1, &ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id1.clone(),
				storage_size: <Test as Trait>::StorageSizeOffset::get(),
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(1),
				rent_allowance: 40,
				last_write: None,
			}));

			let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
			overlay.set_storage(&1, key1.clone(), Some(b"1".to_vec()));
			overlay.set_storage(&1, key2.clone(), Some(b"2".to_vec()));
			DirectAccountDb.commit(overlay.into_change_set());

			Balances::deposit_creating(&2, 110);
			ContractInfoOf::<Test>::insert(2, &ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id2.clone(),
				storage_size: <Test as Trait>::StorageSizeOffset::get(),
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(2),
				rent_allowance: 40,
				last_write: None,
			}));

			let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
			overlay.set_storage(&2, key1.clone(), Some(b"3".to_vec()));
			overlay.set_storage(&2, key2.clone(), Some(b"4".to_vec()));
			DirectAccountDb.commit(overlay.into_change_set());
		}

		// Transfer funds from account 1 of such amount that after this transfer
		// the balance of account 1 will be below the existential threshold.
		//
		// This should lead to the removal of all storage associated with this account.
		assert_ok!(Balances::transfer(Origin::signed(1), 2, 20));

		// Verify that all entries from account 1 is removed, while
		// entries from account 2 is in place.
		{
			assert!(<dyn AccountDb<Test>>::get_storage(&DirectAccountDb, &1, Some(&trie_id1), key1).is_none());
			assert!(<dyn AccountDb<Test>>::get_storage(&DirectAccountDb, &1, Some(&trie_id1), key2).is_none());

			assert_eq!(
				<dyn AccountDb<Test>>::get_storage(&DirectAccountDb, &2, Some(&trie_id2), key1),
				Some(b"3".to_vec())
			);
			assert_eq!(
				<dyn AccountDb<Test>>::get_storage(&DirectAccountDb, &2, Some(&trie_id2), key2),
				Some(b"4".to_vec())
			);
		}
	});
}

const CODE_RETURN_FROM_START_FN: &str = r#"
(module
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "ext_deposit_event" (func $ext_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(start $start)
	(func $start
		(call $ext_deposit_event
			(i32.const 0) ;; The topics buffer
			(i32.const 0) ;; The topics buffer's length
			(i32.const 8) ;; The data buffer
			(i32.const 4) ;; The data buffer's length
		)
		(call $ext_return
			(i32.const 8)
			(i32.const 4)
		)
		(unreachable)
	)

	(func (export "call")
		(unreachable)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\01\02\03\04")
)
"#;

#[test]
fn instantiate_and_call_and_deposit_event() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_RETURN_FROM_START_FN).unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Check at the end to get hash on error easily
		let creation = Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000,
			code_hash.into(),
			vec![],
		);

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					pallet_balances::RawEvent::NewAccount(BOB, 100)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(ALICE, BOB, 100)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::ContractExecution(BOB, vec![1, 2, 3, 4])),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Instantiated(ALICE, BOB)),
				topics: vec![],
			}
		]);

		assert_ok!(creation);
		assert!(ContractInfoOf::<Test>::exists(BOB));
	});
}

const CODE_DISPATCH_CALL: &str = r#"
(module
	(import "env" "ext_dispatch_call" (func $ext_dispatch_call (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_dispatch_call
			(i32.const 8) ;; Pointer to the start of encoded call buffer
			(i32.const 11) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\00\03\00\00\00\00\00\00\00\C8")
)
"#;

#[test]
fn dispatch_call() {
	// This test can fail due to the encoding changes. In case it becomes too annoying
	// let's rewrite so as we use this module controlled call or we serialize it in runtime.
	let encoded = Encode::encode(&Call::Balances(pallet_balances::Call::transfer(CHARLIE, 50)));
	assert_eq!(&encoded[..], &hex!("00000300000000000000C8")[..]);

	let (wasm, code_hash) = compile_module::<Test>(CODE_DISPATCH_CALL).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Let's keep this assert even though it's redundant. If you ever need to update the
		// wasm source this test will fail and will show you the actual hash.
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
		]);

		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000,
			code_hash.into(),
			vec![],
		));

		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB, // newly created account
			0,
			100_000,
			vec![],
		));

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					pallet_balances::RawEvent::NewAccount(BOB, 100)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(ALICE, BOB, 100)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Instantiated(ALICE, BOB)),
				topics: vec![],
			},

			// Dispatching the call.
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					pallet_balances::RawEvent::NewAccount(CHARLIE, 50)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					pallet_balances::RawEvent::Transfer(BOB, CHARLIE, 50, 0)
				),
				topics: vec![],
			},

			// Event emited as a result of dispatch.
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Dispatched(BOB, true)),
				topics: vec![],
			}
		]);
	});
}

const CODE_DISPATCH_CALL_THEN_TRAP: &str = r#"
(module
	(import "env" "ext_dispatch_call" (func $ext_dispatch_call (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_dispatch_call
			(i32.const 8) ;; Pointer to the start of encoded call buffer
			(i32.const 11) ;; Length of the buffer
		)
		(unreachable) ;; trap so that the top level transaction fails
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\00\03\00\00\00\00\00\00\00\C8")
)
"#;

#[test]
fn dispatch_call_not_dispatched_after_top_level_transaction_failure() {
	// This test can fail due to the encoding changes. In case it becomes too annoying
	// let's rewrite so as we use this module controlled call or we serialize it in runtime.
	let encoded = Encode::encode(&Call::Balances(pallet_balances::Call::transfer(CHARLIE, 50)));
	assert_eq!(&encoded[..], &hex!("00000300000000000000C8")[..]);

	let (wasm, code_hash) = compile_module::<Test>(CODE_DISPATCH_CALL_THEN_TRAP).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Let's keep this assert even though it's redundant. If you ever need to update the
		// wasm source this test will fail and will show you the actual hash.
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
		]);

		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000,
			code_hash.into(),
			vec![],
		));

		// Call the newly instantiated contract. The contract is expected to dispatch a call
		// and then trap.
		assert_err!(
			Contract::call(
				Origin::signed(ALICE),
				BOB, // newly created account
				0,
				100_000,
				vec![],
			),
			"contract trapped during execution"
		);
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(
					pallet_balances::RawEvent::NewAccount(BOB, 100)
				),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Transfer(ALICE, BOB, 100)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Instantiated(ALICE, BOB)),
				topics: vec![],
			},
			// ABSENCE of events which would be caused by dispatched Balances::transfer call
		]);
	});
}

const CODE_SET_RENT: &str = r#"
(module
	(import "env" "ext_dispatch_call" (func $ext_dispatch_call (param i32 i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32 i32)))
	(import "env" "ext_set_rent_allowance" (func $ext_set_rent_allowance (param i32 i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; insert a value of 4 bytes into storage
	(func $call_0
		(call $ext_set_storage
			(i32.const 1)
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; remove the value inserted by call_1
	(func $call_1
		(call $ext_set_storage
			(i32.const 1)
			(i32.const 0)
			(i32.const 0)
			(i32.const 0)
		)
	)

	;; transfer 50 to ALICE
	(func $call_2
		(call $ext_dispatch_call
			(i32.const 68)
			(i32.const 11)
		)
	)

	;; do nothing
	(func $call_else)

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	;; Dispatch the call according to input size
	(func (export "call")
		(local $input_size i32)
		(set_local $input_size
			(call $ext_scratch_size)
		)
		(block $IF_ELSE
			(block $IF_2
				(block $IF_1
					(block $IF_0
						(br_table $IF_0 $IF_1 $IF_2 $IF_ELSE
							(get_local $input_size)
						)
						(unreachable)
					)
					(call $call_0)
					return
				)
				(call $call_1)
				return
			)
			(call $call_2)
			return
		)
		(call $call_else)
	)

	;; Set into storage a 4 bytes value
	;; Set call set_rent_allowance with input
	(func (export "deploy")
		(local $input_size i32)
		(set_local $input_size
			(call $ext_scratch_size)
		)
		(call $ext_set_storage
			(i32.const 0)
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)
		(call $ext_scratch_read
			(i32.const 0)
			(i32.const 0)
			(get_local $input_size)
		)
		(call $ext_set_rent_allowance
			(i32.const 0)
			(get_local $input_size)
		)
	)

	;; Encoding of 10 in balance
	(data (i32.const 0) "\28")

	;; Encoding of call transfer 50 to CHARLIE
	(data (i32.const 68) "\00\00\03\00\00\00\00\00\00\00\C8")
)
"#;

/// Input data for each call in set_rent code
mod call {
	pub fn set_storage_4_byte() -> Vec<u8> { vec![] }
	pub fn remove_storage_4_byte() -> Vec<u8> { vec![0] }
	pub fn transfer() -> Vec<u8> { vec![0, 0] }
	pub fn null() -> Vec<u8> { vec![0, 0, 0] }
}

/// Test correspondence of set_rent code and its hash.
/// Also test that encoded extrinsic in code correspond to the correct transfer
#[test]
fn test_set_rent_code_and_hash() {
	// This test can fail due to the encoding changes. In case it becomes too annoying
	// let's rewrite so as we use this module controlled call or we serialize it in runtime.
	let encoded = Encode::encode(&Call::Balances(pallet_balances::Call::transfer(CHARLIE, 50)));
	assert_eq!(&encoded[..], &hex!("00000300000000000000C8")[..]);

	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// If you ever need to update the wasm source this test will fail
		// and will show you the actual hash.
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(code_hash.into())),
				topics: vec![],
			},
		]);
	});
}

#[test]
fn storage_size() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	// Storage size
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			30_000,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.storage_size, <Test as Trait>::StorageSizeOffset::get() + 4);

		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::set_storage_4_byte()));
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.storage_size, <Test as Trait>::StorageSizeOffset::get() + 4 + 4);

		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::remove_storage_4_byte()));
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.storage_size, <Test as Trait>::StorageSizeOffset::get() + 4);
	});
}

fn initialize_block(number: u64) {
	System::initialize(
		&number,
		&[0u8; 32].into(),
		&[0u8; 32].into(),
		&Default::default(),
		Default::default(),
	);
}

#[test]
fn deduct_blocks() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			30_000,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));

		// Check creation
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, 1_000);

		// Advance 4 blocks
		initialize_block(5);

		// Trigger rent through call
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()));

		// Check result
		let rent = (8 + 4 - 3) // storage size = size_offset + deploy_set_storage - deposit_offset
			* 4 // rent byte price
			* 4; // blocks to rent
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, 1_000 - rent);
		assert_eq!(bob_contract.deduct_block, 5);
		assert_eq!(Balances::free_balance(BOB), 30_000 - rent);

		// Advance 7 blocks more
		initialize_block(12);

		// Trigger rent through call
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()));

		// Check result
		let rent_2 = (8 + 4 - 2) // storage size = size_offset + deploy_set_storage - deposit_offset
			* 4 // rent byte price
			* 7; // blocks to rent
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, 1_000 - rent - rent_2);
		assert_eq!(bob_contract.deduct_block, 12);
		assert_eq!(Balances::free_balance(BOB), 30_000 - rent - rent_2);

		// Second call on same block should have no effect on rent
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()));

		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, 1_000 - rent - rent_2);
		assert_eq!(bob_contract.deduct_block, 12);
		assert_eq!(Balances::free_balance(BOB), 30_000 - rent - rent_2);
	});
}

#[test]
fn call_contract_removals() {
	removals(|| {
		// Call on already-removed account might fail, and this is fine.
		Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null());
		true
	});
}

#[test]
fn inherent_claim_surcharge_contract_removals() {
	removals(|| Contract::claim_surcharge(Origin::NONE, BOB, Some(ALICE)).is_ok());
}

#[test]
fn signed_claim_surcharge_contract_removals() {
	removals(|| Contract::claim_surcharge(Origin::signed(ALICE), BOB, None).is_ok());
}

#[test]
fn claim_surcharge_malus() {
	// Test surcharge malus for inherent
	claim_surcharge(4, || Contract::claim_surcharge(Origin::NONE, BOB, Some(ALICE)).is_ok(), true);
	claim_surcharge(3, || Contract::claim_surcharge(Origin::NONE, BOB, Some(ALICE)).is_ok(), true);
	claim_surcharge(2, || Contract::claim_surcharge(Origin::NONE, BOB, Some(ALICE)).is_ok(), true);
	claim_surcharge(1, || Contract::claim_surcharge(Origin::NONE, BOB, Some(ALICE)).is_ok(), false);

	// Test surcharge malus for signed
	claim_surcharge(4, || Contract::claim_surcharge(Origin::signed(ALICE), BOB, None).is_ok(), true);
	claim_surcharge(3, || Contract::claim_surcharge(Origin::signed(ALICE), BOB, None).is_ok(), false);
	claim_surcharge(2, || Contract::claim_surcharge(Origin::signed(ALICE), BOB, None).is_ok(), false);
	claim_surcharge(1, || Contract::claim_surcharge(Origin::signed(ALICE), BOB, None).is_ok(), false);
}

/// Claim surcharge with the given trigger_call at the given blocks.
/// if removes is true then assert that the contract is a tombstonedead
fn claim_surcharge(blocks: u64, trigger_call: impl Fn() -> bool, removes: bool) {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));

		// Advance blocks
		initialize_block(blocks);

		// Trigger rent through call
		assert!(trigger_call());

		if removes {
			assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		} else {
			assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().is_some());
		}
	});
}

/// Test for all kind of removals for the given trigger:
/// * if balance is reached and balance > subsistence threshold
/// * if allowance is exceeded
/// * if balance is reached and balance < subsistence threshold
fn removals(trigger_call: impl Fn() -> bool) {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	// Balance reached and superior to subsistence threshold
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm.clone()));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));

		let subsistence_threshold = 50 /*existential_deposit*/ + 16 /*tombstone_deposit*/;

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert_eq!(ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap().rent_allowance, 1_000);
		assert_eq!(Balances::free_balance(BOB), 100);

		// Advance blocks
		initialize_block(10);

		// Trigger rent through call
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		assert_eq!(Balances::free_balance(BOB), subsistence_threshold);

		// Advance blocks
		initialize_block(20);

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		assert_eq!(Balances::free_balance(BOB), subsistence_threshold);
	});

	// Allowance exceeded
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm.clone()));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			1_000,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(100u32).encode() // rent allowance
		));

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert_eq!(ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap().rent_allowance, 100);
		assert_eq!(Balances::free_balance(BOB), 1_000);

		// Advance blocks
		initialize_block(10);

		// Trigger rent through call
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		// Balance should be initial balance - initial rent_allowance
		assert_eq!(Balances::free_balance(BOB), 900);

		// Advance blocks
		initialize_block(20);

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		assert_eq!(Balances::free_balance(BOB), 900);
	});

	// Balance reached and inferior to subsistence threshold
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm.clone()));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			50+Balances::minimum_balance(),
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert_eq!(ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap().rent_allowance, 1_000);
		assert_eq!(Balances::free_balance(BOB), 50 + Balances::minimum_balance());

		// Transfer funds
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::transfer()));
		assert_eq!(ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap().rent_allowance, 1_000);
		assert_eq!(Balances::free_balance(BOB), Balances::minimum_balance());

		// Advance blocks
		initialize_block(10);

		// Trigger rent through call
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).is_none());
		assert_eq!(Balances::free_balance(BOB), Balances::minimum_balance());

		// Advance blocks
		initialize_block(20);

		// Trigger rent must have no effect
		assert!(trigger_call());
		assert!(ContractInfoOf::<Test>::get(BOB).is_none());
		assert_eq!(Balances::free_balance(BOB), Balances::minimum_balance());
	});
}

#[test]
fn call_removed_contract() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();

	// Balance reached and superior to subsistence threshold
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm.clone()));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000, code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(1_000u32).encode() // rent allowance
		));

		// Calling contract should succeed.
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()));

		// Advance blocks
		initialize_block(10);

		// Calling contract should remove contract and fail.
		assert_err!(
			Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()),
			"contract has been evicted"
		);
		// Calling a contract that is about to evict shall emit an event.
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::Evicted(BOB, true)),
				topics: vec![],
			},
		]);

		// Subsequent contract calls should also fail.
		assert_err!(
			Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()),
			"contract has been evicted"
		);
	})
}

const CODE_CHECK_DEFAULT_RENT_ALLOWANCE: &str = r#"
(module
	(import "env" "ext_rent_allowance" (func $ext_rent_allowance))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call"))

	(func (export "deploy")
		;; fill the scratch buffer with the rent allowance.
		(call $ext_rent_allowance)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to <BalanceOf<T>>::max_value().
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 0xFFFFFFFFFFFFFFFF)
			)
		)
	)
)
"#;

#[test]
fn default_rent_allowance_on_instantiate() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_CHECK_DEFAULT_RENT_ALLOWANCE).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			30_000,
			100_000,
			code_hash.into(),
			vec![],
		));

		// Check creation
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, <BalanceOf<Test>>::max_value());

		// Advance blocks
		initialize_block(5);

		// Trigger rent through call
		assert_ok!(Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()));

		// Check contract is still alive
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive();
		assert!(bob_contract.is_some())
	});
}

const CODE_RESTORATION: &str = r#"
(module
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32 i32)))
	(import "env" "ext_restore_to" (func $ext_restore_to (param i32 i32 i32 i32 i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_restore_to
			;; Pointer and length of the encoded dest buffer.
			(i32.const 256)
			(i32.const 8)
			;; Pointer and length of the encoded code hash buffer
			(i32.const 264)
			(i32.const 32)
			;; Pointer and length of the encoded rent_allowance buffer
			(i32.const 296)
			(i32.const 8)
			;; Pointer and number of items in the delta buffer.
			;; This buffer specifies multiple keys for removal before restoration.
			(i32.const 100)
			(i32.const 1)
		)
	)
	(func (export "deploy")
		;; Data to restore
		(call $ext_set_storage
			(i32.const 0)
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)

		;; ACL
		(call $ext_set_storage
			(i32.const 100)
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; Data to restore
	(data (i32.const 0) "\28")

	;; Buffer that has ACL storage keys.
	(data (i32.const 100) "\01")

	;; Address of bob
	(data (i32.const 256) "\02\00\00\00\00\00\00\00")

	;; Code hash of SET_RENT
	(data (i32.const 264)
		"\14\eb\65\3c\86\98\d6\b2\3d\8d\3c\4a\54\c6\c4\71"
		"\b9\fc\19\36\df\ca\a0\a1\f2\dc\ad\9d\e5\36\0b\25"
	)

	;; Rent allowance
	(data (i32.const 296) "\32\00\00\00\00\00\00\00")
)
"#;

#[test]
fn restorations_dirty_storage_and_different_storage() {
	restoration(true, true);
}

#[test]
fn restorations_dirty_storage() {
	restoration(false, true);
}

#[test]
fn restoration_different_storage() {
	restoration(true, false);
}

#[test]
fn restoration_success() {
	restoration(false, false);
}

fn restoration(test_different_storage: bool, test_restore_to_with_dirty_storage: bool) {
	let (set_rent_wasm, set_rent_code_hash) = compile_module::<Test>(CODE_SET_RENT).unwrap();
	let (restoration_wasm, restoration_code_hash) =
		compile_module::<Test>(CODE_RESTORATION).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, restoration_wasm));
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, set_rent_wasm));

		// If you ever need to update the wasm source this test will fail
		// and will show you the actual hash.
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(1, 1_000_000)),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(restoration_code_hash.into())),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(RawEvent::CodeStored(set_rent_code_hash.into())),
				topics: vec![],
			},
		]);

		// Create an account with address `BOB` with code `CODE_SET_RENT`.
		// The input parameter sets the rent allowance to 0.
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			30_000,
			100_000,
			set_rent_code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(0u32).encode()
		));

		// Check if `BOB` was created successfully and that the rent allowance is
		// set to 0.
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, 0);

		if test_different_storage {
			assert_ok!(Contract::call(
				Origin::signed(ALICE),
				BOB, 0, 100_000,
				call::set_storage_4_byte())
			);
		}

		// Advance 4 blocks, to the 5th.
		initialize_block(5);

		/// Preserve `BOB`'s code hash for later introspection.
		let bob_code_hash = ContractInfoOf::<Test>::get(BOB).unwrap()
			.get_alive().unwrap().code_hash;
		// Call `BOB`, which makes it pay rent. Since the rent allowance is set to 0
		// we expect that it will get removed leaving tombstone.
		assert_err!(
			Contract::call(Origin::signed(ALICE), BOB, 0, 100_000, call::null()),
			"contract has been evicted"
		);
		assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: MetaEvent::contract(
					RawEvent::Evicted(BOB.clone(), true)
				),
				topics: vec![],
			},
		]);

		/// Create another account with the address `DJANGO` with `CODE_RESTORATION`.
		///
		/// Note that we can't use `ALICE` for creating `DJANGO` so we create yet another
		/// account `CHARLIE` and create `DJANGO` with it.
		Balances::deposit_creating(&CHARLIE, 1_000_000);
		assert_ok!(Contract::instantiate(
			Origin::signed(CHARLIE),
			30_000,
			100_000,
			restoration_code_hash.into(),
			<Test as pallet_balances::Trait>::Balance::from(0u32).encode()
		));

		// Before performing a call to `DJANGO` save its original trie id.
		let django_trie_id = ContractInfoOf::<Test>::get(DJANGO).unwrap()
			.get_alive().unwrap().trie_id;

		if !test_restore_to_with_dirty_storage {
			// Advance 1 block, to the 6th.
			initialize_block(6);
		}

		// Perform a call to `DJANGO`. This should either perform restoration successfully or
		// fail depending on the test parameters.
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			DJANGO,
			0,
			100_000,
			vec![],
		));

		if test_different_storage || test_restore_to_with_dirty_storage {
			// Parametrization of the test imply restoration failure. Check that `DJANGO` aka
			// restoration contract is still in place and also that `BOB` doesn't exist.
			assert!(ContractInfoOf::<Test>::get(BOB).unwrap().get_tombstone().is_some());
			let django_contract = ContractInfoOf::<Test>::get(DJANGO).unwrap()
				.get_alive().unwrap();
			assert_eq!(django_contract.storage_size, 16);
			assert_eq!(django_contract.trie_id, django_trie_id);
			assert_eq!(django_contract.deduct_block, System::block_number());
			match (test_different_storage, test_restore_to_with_dirty_storage) {
				(true, false) => {
					assert_eq!(System::events(), vec![
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::contract(
								RawEvent::Restored(DJANGO, BOB, bob_code_hash, 50, false)
							),
							topics: vec![],
						},
					]);
				}
				(_, true) => {
					assert_eq!(System::events(), vec![
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::contract(RawEvent::Evicted(BOB, true)),
							topics: vec![],
						},
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(CHARLIE, 1_000_000)),
							topics: vec![],
						},
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::balances(pallet_balances::RawEvent::NewAccount(DJANGO, 30_000)),
							topics: vec![],
						},
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::contract(RawEvent::Transfer(CHARLIE, DJANGO, 30_000)),
							topics: vec![],
						},
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::contract(RawEvent::Instantiated(CHARLIE, DJANGO)),
							topics: vec![],
						},
						EventRecord {
							phase: Phase::ApplyExtrinsic(0),
							event: MetaEvent::contract(RawEvent::Restored(
								DJANGO,
								BOB,
								bob_code_hash,
								50,
								false,
							)),
							topics: vec![],
						},
					]);
				}
				_ => unreachable!(),
			}
		} else {
			// Here we expect that the restoration is succeeded. Check that the restoration
			// contract `DJANGO` ceased to exist and that `BOB` returned back.
			println!("{:?}", ContractInfoOf::<Test>::get(BOB));
			let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap()
				.get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 50);
			assert_eq!(bob_contract.storage_size, 12);
			assert_eq!(bob_contract.trie_id, django_trie_id);
			assert_eq!(bob_contract.deduct_block, System::block_number());
			assert!(ContractInfoOf::<Test>::get(DJANGO).is_none());
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: MetaEvent::balances(balances::RawEvent::ReapedAccount(DJANGO, 0)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: MetaEvent::contract(
						RawEvent::Restored(DJANGO, BOB, bob_contract.code_hash, 50, true)
					),
					topics: vec![],
				},
			]);
		}
	});
}

const CODE_STORAGE_SIZE: &str = r#"
(module
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32 i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 16 16))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 4)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 32)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 4)		;; Count of bytes to copy.
		)

		;; place a garbage value in storage, the size of which is specified by the call input.
		(call $ext_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 1)		;; Value is not null
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 32))	;; Size of value
		)

		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 0)		;; Pointer to storage key
				)
				(i32.const 0)
			)
		)

		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.load (i32.const 32))
			)
		)
	)

	(func (export "deploy"))

	(data (i32.const 0) "\01")	;; Storage key (32 B)
)
"#;

#[test]
fn storage_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_STORAGE_SIZE).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			30_000,
			100_000,
			code_hash.into(),
			vec![],
		));

		// Check creation
		let bob_contract = ContractInfoOf::<Test>::get(BOB).unwrap().get_alive().unwrap();
		assert_eq!(bob_contract.rent_allowance, <BalanceOf<Test>>::max_value());

		// Call contract with allowed storage value.
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB,
			0,
			100_000,
			Encode::encode(&self::MaxValueSize::get()),
		));

		// Call contract with too large a storage value.
		assert_err!(
			Contract::call(
				Origin::signed(ALICE),
				BOB,
				0,
				100_000,
				Encode::encode(&(self::MaxValueSize::get() + 1)),
			),
			"contract trapped during execution"
		);
	});
}

const CODE_RETURN_WITH_DATA: &str = r#"
(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_scratch_write" (func $ext_scratch_write (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; Deploy routine is the same as call.
	(func (export "deploy") (result i32)
		(call $call)
	)

	;; Call reads the first 4 bytes (LE) as the exit status and returns the rest as output data.
	(func $call (export "call") (result i32)
		(local $buf_size i32)
		(local $exit_status i32)

		;; Find out the size of the scratch buffer
		(set_local $buf_size (call $ext_scratch_size))

		;; Copy scratch buffer into this contract memory.
		(call $ext_scratch_read
			(i32.const 0)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(get_local $buf_size)		;; Count of bytes to copy.
		)

		;; Copy all but the first 4 bytes of the input data as the output data.
		(call $ext_scratch_write
			(i32.const 4)	;; Pointer to the data to return.
			(i32.sub		;; Count of bytes to copy.
				(get_local $buf_size)
				(i32.const 4)
			)
		)

		;; Return the first 4 bytes of the input data as the exit status.
		(i32.load (i32.const 0))
	)
)
"#;

const CODE_CALLER_CONTRACT: &str = r#"
(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_instantiate" (func $ext_instantiate (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_println" (func $ext_println (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func $current_balance (param $sp i32) (result i64)
		(call $ext_balance)
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 8))
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 8))
			(i32.const 0)
			(i32.const 8)
		)
		(i64.load (i32.sub (get_local $sp) (i32.const 8)))
	)

	(func (export "deploy"))

	(func (export "call")
		(local $sp i32)
		(local $exit_code i32)
		(local $balance i64)

		;; Input data is the code hash of the contract to be deployed.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 32)
			)
		)

		;; Copy code hash from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 24)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 32)		;; Count of bytes to copy.
		)

		;; Read current balance into local variable.
		(set_local $sp (i32.const 1024))
		(set_local $balance
			(call $current_balance (get_local $sp))
		)

		;; Fail to deploy the contract since it returns a non-zero exit status.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x11))
		)

		;; Check that scratch buffer is empty since contract instantiation failed.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Fail to deploy the contract due to insufficient gas.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 200)	;; How much gas to devote for the execution.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x0100))
		)

		;; Check that scratch buffer is empty since contract instantiation failed.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Deploy the contract successfully.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x00))
		)

		;; Check that scratch buffer contains the address of the new contract.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 8))
		)

		;; Copy contract address from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 16)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Check that balance has been deducted.
		(set_local $balance
			(i64.sub (get_local $balance) (i64.load (i32.const 0)))
		)
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Call the new contract and expect it to return failing exit code.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x11))
		)

		;; Check that scratch buffer contains the expected return data.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 3))
		)
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
			(i32.const 3)
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x00776655)
			)
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Fail to call the contract due to insufficient gas.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 100)	;; How much gas to devote for the execution.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x0100))
		)

		;; Check that scratch buffer is empty since call trapped.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Call the contract successfully.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x00))
		)

		;; Check that scratch buffer contains the expected return data.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 4))
		)
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
			(i32.const 4)
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x77665544)
			)
		)

		;; Check that balance has been deducted.
		(set_local $balance
			(i64.sub (get_local $balance) (i64.load (i32.const 0)))
		)
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)
	)

	(data (i32.const 0) "\00\80")		;; The value to transfer on instantiation and calls.
										;; Chosen to be greater than existential deposit.
	(data (i32.const 8) "\00\11\22\33\44\55\66\77")		;; The input data to instantiations and calls.
)
"#;

#[test]
fn deploy_and_call_other_contract() {
	let (callee_wasm, callee_code_hash) = compile_module::<Test>(CODE_RETURN_WITH_DATA).unwrap();
	let (caller_wasm, caller_code_hash) = compile_module::<Test>(CODE_CALLER_CONTRACT).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, callee_wasm));
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, caller_wasm));

		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100_000,
			100_000,
			caller_code_hash.into(),
			vec![],
		));

		// Call BOB contract, which attempts to instantiate and call the callee contract and
		// makes various assertions on the results from those calls.
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB,
			0,
			200_000,
			callee_code_hash.as_ref().to_vec(),
		));
	});
}

const CODE_SELF_DESTRUCT: &str = r#"
(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_address" (func $ext_address))
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy"))

	(func (export "call")
		;; If the input data is not empty, then recursively call self with empty input data.
		;; This should trap instead of self-destructing since a contract cannot be removed live in
		;; the execution stack cannot be removed. If the recursive call traps, then trap here as
		;; well.
		(if (call $ext_scratch_size)
			(then
				(call $ext_address)

				;; Expect address to be 8 bytes.
				(call $assert
					(i32.eq
						(call $ext_scratch_size)
						(i32.const 8)
					)
				)

				;; Read own address into memory.
				(call $ext_scratch_read
					(i32.const 16)	;; Pointer to write address to
					(i32.const 0)	;; Offset into scrach buffer
					(i32.const 8)	;; Length of encoded address
				)

				;; Recursively call self with empty imput data.
				(call $assert
					(i32.eq
						(call $ext_call
							(i32.const 16)	;; Pointer to own address
							(i32.const 8)	;; Length of own address
							(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
							(i32.const 8)	;; Pointer to the buffer with value to transfer
							(i32.const 8)	;; Length of the buffer with value to transfer
							(i32.const 0)	;; Pointer to input data buffer address
							(i32.const 0)	;; Length of input data buffer
						)
						(i32.const 0)
					)
				)
			)
		)

		;; Send entire remaining balance to the 0 address.
		(call $ext_balance)

		;; Balance should be encoded as a u64.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; Read balance into memory.
		(call $ext_scratch_read
			(i32.const 8)	;; Pointer to write balance to
			(i32.const 0)	;; Offset into scrach buffer
			(i32.const 8)	;; Length of encoded balance
		)

		;; Self-destruct by sending full balance to the 0 address.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 0)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 8)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)
	)
)
"#;

#[test]
fn self_destruct_by_draining_balance() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SELF_DESTRUCT).unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Instantiate the BOB contract.
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100_000,
			100_000,
			code_hash.into(),
			vec![],
		));

		// Check that the BOB contract has been instantiated.
		assert_matches!(
			ContractInfoOf::<Test>::get(BOB),
			Some(ContractInfo::Alive(_))
		);

		// Call BOB with no input data, forcing it to self-destruct.
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB,
			0,
			100_000,
			vec![],
		));

		// Check that BOB is now dead.
		assert!(ContractInfoOf::<Test>::get(BOB).is_none());
	});
}

#[test]
fn cannot_self_destruct_while_live() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SELF_DESTRUCT).unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Instantiate the BOB contract.
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100_000,
			100_000,
			code_hash.into(),
			vec![],
		));

		// Check that the BOB contract has been instantiated.
		assert_matches!(
			ContractInfoOf::<Test>::get(BOB),
			Some(ContractInfo::Alive(_))
		);

		// Call BOB with input data, forcing it make a recursive call to itself to
		// self-destruct, resulting in a trap.
		assert_err!(
			Contract::call(
				Origin::signed(ALICE),
				BOB,
				0,
				100_000,
				vec![0],
			),
			"contract trapped during execution"
		);

		// Check that BOB is still alive.
		assert_matches!(
			ContractInfoOf::<Test>::get(BOB),
			Some(ContractInfo::Alive(_))
		);
	});
}

const CODE_DESTROY_AND_TRANSFER: &str = r#"
(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32 i32)))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_instantiate" (func $ext_instantiate (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy")
		;; Input data is the code hash of the contract to be deployed.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 32)
			)
		)

		;; Copy code hash from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 48)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 32)		;; Count of bytes to copy.
		)

		;; Deploy the contract with the provided code hash.
		(call $assert
			(i32.eq
				(call $ext_instantiate
					(i32.const 48)	;; Pointer to the code hash.
					(i32.const 32)	;; Length of the code hash.
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer.
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)

		;; Read the address of the instantiated contract into memory.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)
		(call $ext_scratch_read
			(i32.const 80)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Store the return address.
		(call $ext_set_storage
			(i32.const 16)	;; Pointer to the key
			(i32.const 1)	;; Value is not null
			(i32.const 80)	;; Pointer to the value
			(i32.const 8)	;; Length of the value
		)
	)

	(func (export "call")
		;; Read address of destination contract from storage.
		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 16)	;; Pointer to the key
				)
				(i32.const 0)
			)
		)
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)
		(call $ext_scratch_read
			(i32.const 80)		;; The pointer where to store the contract address.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Calling the destination contract with non-empty input data should fail.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 1)	;; Length of input data buffer
				)
				(i32.const 0x0100)
			)
		)

		;; Call the destination contract regularly, forcing it to self-destruct.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 8)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)

		;; Calling the destination address with non-empty input data should now work since the
		;; contract has been removed. Also transfer a balance to the address so we can ensure this
		;; does not keep the contract alive.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 1)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)
	)

	(data (i32.const 0) "\00\00\01")		;; Endowment to send when creating contract.
	(data (i32.const 8) "")		;; Value to send when calling contract.
	(data (i32.const 16) "")	;; The key to store the contract address under.
)
"#;

// This tests that one contract cannot prevent another from self-destructing by sending it
// additional funds after it has been drained.
#[test]
fn destroy_contract_and_transfer_funds() {
	let (callee_wasm, callee_code_hash) = compile_module::<Test>(CODE_SELF_DESTRUCT).unwrap();
	let (caller_wasm, caller_code_hash) = compile_module::<Test>(CODE_DESTROY_AND_TRANSFER).unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, callee_wasm));
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, caller_wasm));

		// This deploys the BOB contract, which in turn deploys the CHARLIE contract during
		// construction.
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			200_000,
			100_000,
			caller_code_hash.into(),
			callee_code_hash.as_ref().to_vec(),
		));

		// Check that the CHARLIE contract has been instantiated.
		assert_matches!(
			ContractInfoOf::<Test>::get(CHARLIE),
			Some(ContractInfo::Alive(_))
		);

		// Call BOB, which calls CHARLIE, forcing CHARLIE to self-destruct.
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB,
			0,
			100_000,
			CHARLIE.encode(),
		));

		// Check that CHARLIE has moved on to the great beyond (ie. died).
		assert!(ContractInfoOf::<Test>::get(CHARLIE).is_none());
	});
}

const CODE_SELF_DESTRUCTING_CONSTRUCTOR: &str = r#"
(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy")
		;; Send entire remaining balance to the 0 address.
		(call $ext_balance)

		;; Balance should be encoded as a u64.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; Read balance into memory.
		(call $ext_scratch_read
			(i32.const 8)	;; Pointer to write balance to
			(i32.const 0)	;; Offset into scrach buffer
			(i32.const 8)	;; Length of encoded balance
		)

		;; Self-destruct by sending full balance to the 0 address.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 0)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 8)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)
	)

	(func (export "call"))
)
"#;

#[test]
fn cannot_self_destruct_in_constructor() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_SELF_DESTRUCTING_CONSTRUCTOR).unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));

		// Fail to instantiate the BOB contract since its final balance is below existential
		// deposit.
		assert_err!(
			Contract::instantiate(
				Origin::signed(ALICE),
				100_000,
				100_000,
				code_hash.into(),
				vec![],
			),
			"insufficient remaining balance"
		);
	});
}

#[test]
fn check_block_gas_limit_works() {
	ExtBuilder::default().block_gas_limit(50).build().execute_with(|| {
		let info = DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: true };
		let check = CheckBlockGasLimit::<Test>(Default::default());
		let call: Call = crate::Call::put_code(1000, vec![]).into();

		assert_eq!(
			check.validate(&0, &call, info, 0), InvalidTransaction::ExhaustsResources.into(),
		);

		let call: Call = crate::Call::update_schedule(Default::default()).into();
		assert_eq!(check.validate(&0, &call, info, 0), Ok(Default::default()));
	});
}

const CODE_GET_RUNTIME_STORAGE: &str = r#"
(module
	(import "env" "ext_get_runtime_storage"
		(func $ext_get_runtime_storage (param i32 i32) (result i32))
	)
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_scratch_write" (func $ext_scratch_write (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func $call (export "call")
		;; Load runtime storage for the first key and assert that it exists.
		(call $assert
			(i32.eq
				(call $ext_get_runtime_storage
					(i32.const 16)
					(i32.const 4)
				)
				(i32.const 0)
			)
		)

		;; assert $ext_scratch_size == 4
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 4)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 4)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 4)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i32 value of 0x14144020.
		(call $assert
			(i32.eq
				(i32.load
					(i32.const 4)
				)
				(i32.const 0x14144020)
			)
		)

		;; Load the second key and assert that it doesn't exist.
		(call $assert
			(i32.eq
				(call $ext_get_runtime_storage
					(i32.const 20)
					(i32.const 4)
				)
				(i32.const 1)
			)
		)
	)

	;; The first key, 4 bytes long.
	(data (i32.const 16) "\01\02\03\04")
	;; The second key, 4 bytes long.
	(data (i32.const 20) "\02\03\04\05")
)
"#;

#[test]
fn get_runtime_storage() {
	let (wasm, code_hash) = compile_module::<Test>(CODE_GET_RUNTIME_STORAGE).unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		Balances::deposit_creating(&ALICE, 1_000_000);

		frame_support::storage::unhashed::put_raw(
			&[1, 2, 3, 4],
			0x14144020u32.to_le_bytes().to_vec().as_ref()
		);

		assert_ok!(Contract::put_code(Origin::signed(ALICE), 100_000, wasm));
		assert_ok!(Contract::instantiate(
			Origin::signed(ALICE),
			100,
			100_000,
			code_hash.into(),
			vec![],
		));
		assert_ok!(Contract::call(
			Origin::signed(ALICE),
			BOB,
			0,
			100_000,
			vec![],
		));
	});
}
