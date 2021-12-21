// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	chain_extension::{
		ChainExtension, Environment, Ext, InitState, Result as ExtensionResult, RetVal,
		ReturnFlags, SysConfig, UncheckedFrom,
	},
	exec::Frame,
	storage::Storage,
	wasm::{PrefabWasmModule, ReturnCode as RuntimeReturnCode},
	weights::WeightInfo,
	BalanceOf, Code, CodeStorage, Config, ContractInfoOf, DefaultAddressGenerator, Error, Pallet,
	Schedule,
};
use assert_matches::assert_matches;
use codec::Encode;
use frame_support::{
	assert_err, assert_err_ignore_postinfo, assert_noop, assert_ok,
	dispatch::DispatchErrorWithPostInfo,
	parameter_types,
	storage::child,
	traits::{
		BalanceStatus, ConstU32, ConstU64, Contains, Currency, OnInitialize, ReservableCurrency,
	},
	weights::{constants::WEIGHT_PER_SECOND, DispatchClass, PostDispatchInfo, Weight},
};
use frame_system::{self as system, EventRecord, Phase};
use pretty_assertions::assert_eq;
use sp_core::Bytes;
use sp_io::hashing::blake2_256;
use sp_runtime::{
	testing::{Header, H256},
	traits::{BlakeTwo256, Convert, Hash, IdentityLookup},
	AccountId32,
};
use std::cell::RefCell;

use crate as pallet_contracts;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		Randomness: pallet_randomness_collective_flip::{Pallet, Storage},
		Utility: pallet_utility::{Pallet, Call, Storage, Event},
		Contracts: pallet_contracts::{Pallet, Call, Storage, Event<T>},
	}
);

#[macro_use]
pub mod test_utils {
	use super::{Balances, Test};
	use crate::{
		exec::AccountIdOf, storage::Storage, AccountCounter, CodeHash, Config, ContractInfoOf,
	};
	use frame_support::traits::Currency;

	pub fn place_contract(address: &AccountIdOf<Test>, code_hash: CodeHash<Test>) {
		let seed = <AccountCounter<Test>>::mutate(|counter| {
			*counter += 1;
			*counter
		});
		let trie_id = Storage::<Test>::generate_trie_id(address, seed);
		set_balance(address, <Test as Config>::Currency::minimum_balance() * 10);
		let contract = Storage::<Test>::new_contract(&address, trie_id, code_hash).unwrap();
		<ContractInfoOf<Test>>::insert(address, contract);
	}
	pub fn set_balance(who: &AccountIdOf<Test>, amount: u64) {
		let imbalance = Balances::deposit_creating(who, amount);
		drop(imbalance);
	}
	pub fn get_balance(who: &AccountIdOf<Test>) -> u64 {
		Balances::free_balance(who)
	}
	macro_rules! assert_return_code {
		( $x:expr , $y:expr $(,)? ) => {{
			use sp_std::convert::TryInto;
			assert_eq!(u32::from_le_bytes($x.data[..].try_into().unwrap()), $y as u32);
		}};
	}
	macro_rules! assert_refcount {
		( $code_hash:expr , $should:expr $(,)? ) => {{
			let is = crate::OwnerInfoOf::<Test>::get($code_hash).map(|m| m.refcount()).unwrap();
			assert_eq!(is, $should);
		}};
	}
}

thread_local! {
	static TEST_EXTENSION: RefCell<TestExtension> = Default::default();
}

pub struct TestExtension {
	enabled: bool,
	last_seen_buffer: Vec<u8>,
	last_seen_inputs: (u32, u32, u32, u32),
}

impl TestExtension {
	fn disable() {
		TEST_EXTENSION.with(|e| e.borrow_mut().enabled = false)
	}

	fn last_seen_buffer() -> Vec<u8> {
		TEST_EXTENSION.with(|e| e.borrow().last_seen_buffer.clone())
	}

	fn last_seen_inputs() -> (u32, u32, u32, u32) {
		TEST_EXTENSION.with(|e| e.borrow().last_seen_inputs.clone())
	}
}

impl Default for TestExtension {
	fn default() -> Self {
		Self { enabled: true, last_seen_buffer: vec![], last_seen_inputs: (0, 0, 0, 0) }
	}
}

impl ChainExtension<Test> for TestExtension {
	fn call<E>(func_id: u32, env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
		E: Ext<T = Test>,
		<E::T as SysConfig>::AccountId: UncheckedFrom<<E::T as SysConfig>::Hash> + AsRef<[u8]>,
	{
		match func_id {
			0 => {
				let mut env = env.buf_in_buf_out();
				let input = env.read(2)?;
				env.write(&input, false, None)?;
				TEST_EXTENSION.with(|e| e.borrow_mut().last_seen_buffer = input);
				Ok(RetVal::Converging(func_id))
			},
			1 => {
				let env = env.only_in();
				TEST_EXTENSION.with(|e| {
					e.borrow_mut().last_seen_inputs =
						(env.val0(), env.val1(), env.val2(), env.val3())
				});
				Ok(RetVal::Converging(func_id))
			},
			2 => {
				let mut env = env.buf_in_buf_out();
				let weight = env.read(2)?[1].into();
				env.charge_weight(weight)?;
				Ok(RetVal::Converging(func_id))
			},
			3 => Ok(RetVal::Diverging { flags: ReturnFlags::REVERT, data: vec![42, 99] }),
			_ => {
				panic!("Passed unknown func_id to test chain extension: {}", func_id);
			},
		}
	}

	fn enabled() -> bool {
		TEST_EXTENSION.with(|e| e.borrow().enabled)
	}
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(2 * WEIGHT_PER_SECOND);
	pub static ExistentialDeposit: u64 = 1;
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId32;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}
impl pallet_randomness_collective_flip::Config for Test {}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<1>;
	type WeightInfo = ();
}
impl pallet_utility::Config for Test {
	type Event = Event;
	type Call = Call;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
}
parameter_types! {
	pub const MaxValueSize: u32 = 16_384;
	pub const DeletionWeightLimit: Weight = 500_000_000_000;
	pub const MaxCodeSize: u32 = 2 * 1024;
	pub MySchedule: Schedule<Test> = <Schedule<Test>>::default();
	pub const TransactionByteFee: u64 = 0;
	pub static DepositPerByte: BalanceOf<Test> = 1;
	pub const DepositPerItem: BalanceOf<Test> = 2;
}

impl Convert<Weight, BalanceOf<Self>> for Test {
	fn convert(w: Weight) -> BalanceOf<Self> {
		w
	}
}

/// A filter whose filter function can be swapped at runtime.
pub struct TestFilter;

thread_local! {
	static CALL_FILTER: RefCell<fn(&Call) -> bool> = RefCell::new(|_| true);
}

impl TestFilter {
	pub fn set_filter(filter: fn(&Call) -> bool) {
		CALL_FILTER.with(|fltr| *fltr.borrow_mut() = filter);
	}
}

impl Contains<Call> for TestFilter {
	fn contains(call: &Call) -> bool {
		CALL_FILTER.with(|fltr| fltr.borrow()(call))
	}
}

impl Config for Test {
	type Time = Timestamp;
	type Randomness = Randomness;
	type Currency = Balances;
	type Event = Event;
	type Call = Call;
	type CallFilter = TestFilter;
	type CallStack = [Frame<Self>; 31];
	type WeightPrice = Self;
	type WeightInfo = ();
	type ChainExtension = TestExtension;
	type DeletionQueueDepth = ConstU32<1024>;
	type DeletionWeightLimit = DeletionWeightLimit;
	type Schedule = MySchedule;
	type DepositPerByte = DepositPerByte;
	type DepositPerItem = DepositPerItem;
	type AddressGenerator = DefaultAddressGenerator;
}

pub const ALICE: AccountId32 = AccountId32::new([1u8; 32]);
pub const BOB: AccountId32 = AccountId32::new([2u8; 32]);
pub const CHARLIE: AccountId32 = AccountId32::new([3u8; 32]);
pub const DJANGO: AccountId32 = AccountId32::new([4u8; 32]);

pub const GAS_LIMIT: Weight = 10_000_000_000;

pub struct ExtBuilder {
	existential_deposit: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self { existential_deposit: ExistentialDeposit::get() }
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn set_associated_consts(&self) {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
	}
	pub fn build(self) -> sp_io::TestExternalities {
		use env_logger::{Builder, Env};
		let env = Env::new().default_filter_or("runtime=debug");
		let _ = Builder::from_env(env).is_test(true).try_init();
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> { balances: vec![] }
			.assimilate_storage(&mut t)
			.unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

/// Load a given wasm module represented by a .wat file and returns a wasm binary contents along
/// with it's hash.
///
/// The fixture files are located under the `fixtures/` directory.
fn compile_module<T>(fixture_name: &str) -> wat::Result<(Vec<u8>, <T::Hashing as Hash>::Output)>
where
	T: frame_system::Config,
{
	let fixture_path = ["fixtures/", fixture_name, ".wat"].concat();
	let wasm_binary = wat::parse_file(fixture_path)?;
	let code_hash = T::Hashing::hash(&wasm_binary);
	Ok((wasm_binary, code_hash))
}

// Perform a call to a plain account.
// The actual transfer fails because we can only call contracts.
// Then we check that at least the base costs where charged (no runtime gas costs.)
#[test]
fn calling_plain_account_fails() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 100_000_000);
		let base_cost = <<Test as Config>::WeightInfo as WeightInfo>::call();

		assert_eq!(
			Contracts::call(Origin::signed(ALICE), BOB, 0, GAS_LIMIT, None, Vec::new()),
			Err(DispatchErrorWithPostInfo {
				error: Error::<Test>::ContractNotFound.into(),
				post_info: PostDispatchInfo {
					actual_weight: Some(base_cost),
					pays_fee: Default::default(),
				},
			})
		);
	});
}

#[test]
fn instantiate_and_call_and_deposit_event() {
	let (wasm, code_hash) = compile_module::<Test>("return_from_start_fn").unwrap();

	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let value = 100;

		// We determine the storage deposit limit after uploading because it depends on ALICEs free
		// balance which is changed by uploading a module.
		assert_ok!(Contracts::upload_code(Origin::signed(ALICE), wasm, None));

		// Drop previous events
		initialize_block(2);

		// Check at the end to get hash on error easily
		assert_ok!(Contracts::instantiate(
			Origin::signed(ALICE),
			value,
			GAS_LIMIT,
			None,
			code_hash,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		assert!(ContractInfoOf::<Test>::contains_key(&addr));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::NewAccount { account: addr.clone() }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: value,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::ContractEmitted {
						contract: addr.clone(),
						data: vec![1, 2, 3, 4]
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone()
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn deposit_event_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>("event_size").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Call contract with allowed storage value.
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT * 2, // we are copying a huge buffer,
			None,
			<Test as Config>::Schedule::get().limits.payload_len.encode(),
		));

		// Call contract with too large a storage value.
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr,
				0,
				GAS_LIMIT,
				None,
				(<Test as Config>::Schedule::get().limits.payload_len + 1).encode(),
			),
			Error::<Test>::ValueTooLarge,
		);
	});
}

#[test]
fn run_out_of_gas() {
	let (wasm, code_hash) = compile_module::<Test>("run_out_of_gas").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100 * min_balance,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Call the contract with a fixed gas limit. It must run out of gas because it just
		// loops forever.
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr, // newly created account
				0,
				1_000_000_000_000,
				None,
				vec![],
			),
			Error::<Test>::OutOfGas,
		);
	});
}

fn initialize_block(number: u64) {
	System::initialize(&number, &[0u8; 32].into(), &Default::default(), Default::default());
}

#[test]
fn storage_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>("storage_size").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		ContractInfoOf::<Test>::get(&addr).unwrap();

		// Call contract with allowed storage value.
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT * 2, // we are copying a huge buffer
			None,
			<Test as Config>::Schedule::get().limits.payload_len.encode(),
		));

		// Call contract with too large a storage value.
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr,
				0,
				GAS_LIMIT,
				None,
				(<Test as Config>::Schedule::get().limits.payload_len + 1).encode(),
			),
			Error::<Test>::ValueTooLarge,
		);
	});
}

#[test]
fn deploy_and_call_other_contract() {
	let (caller_wasm, caller_code_hash) = compile_module::<Test>("caller_contract").unwrap();
	let (callee_wasm, callee_code_hash) = compile_module::<Test>("return_with_data").unwrap();
	let caller_addr = Contracts::contract_address(&ALICE, &caller_code_hash, &[]);
	let callee_addr = Contracts::contract_address(&caller_addr, &callee_code_hash, &[]);

	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			caller_wasm,
			vec![],
			vec![],
		));
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			callee_wasm,
			0u32.to_le_bytes().encode(),
			vec![42],
		));

		// Drop previous events
		initialize_block(2);

		// Call BOB contract, which attempts to instantiate and call the callee contract and
		// makes various assertions on the results from those calls.
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			caller_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			callee_code_hash.as_ref().to_vec(),
		));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::NewAccount {
						account: callee_addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Endowed {
						account: callee_addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: callee_addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: callee_addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: caller_addr.clone(),
						to: callee_addr.clone(),
						amount: 32768, // hard coded in wasm
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::Instantiated {
						deployer: caller_addr.clone(),
						contract: callee_addr.clone(),
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: caller_addr.clone(),
						to: callee_addr.clone(),
						amount: 32768,
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn cannot_self_destruct_through_draning() {
	let (wasm, code_hash) = compile_module::<Test>("drain").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			1_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));

		// Call BOB which makes it send all funds to the zero address
		// The contract code asserts that the transfer was successful
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Make sure the account wasn't remove by sending all free balance away.
		assert_eq!(
			<Test as Config>::Currency::total_balance(&addr),
			<Test as Config>::Currency::minimum_balance(),
		);
	});
}

#[test]
fn cannot_self_destruct_through_storage_refund_after_price_change() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated and has the minimum balance
		let info = ContractInfoOf::<Test>::get(&addr).unwrap();
		assert_eq!(info.storage_deposit, min_balance);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// Create 100 bytes of storage with a price of per byte
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			100u32.to_le_bytes().to_vec()
		));

		// Increase the byte price and trigger a refund. This could potentially destroy the account
		// because the refund removes the reserved existential deposit. This should not happen.
		DEPOSIT_PER_BYTE.with(|c| *c.borrow_mut() = 500);
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			0u32.to_le_bytes().to_vec()
		));

		// Make sure the account wasn't removed by the refund
		assert_eq!(
			<Test as Config>::Currency::total_balance(&addr),
			<Test as Config>::Currency::minimum_balance(),
		);
	});
}

#[test]
fn cannot_self_destruct_by_refund_after_slash() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// create 100 more reserved balance
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			98u32.encode(),
		));

		// Drop previous events
		initialize_block(2);

		// slash parts of the 100 so that the next refund ould remove the account
		// because it the value it stored for `storage_deposit` becomes out of sync
		let _ = <Test as Config>::Currency::slash(&addr, 90);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance + 10);

		// trigger a refund of 50 which would bring the contract below min when actually refunded
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			48u32.encode(),
		));

		// Make sure the account kept the minimum balance and was not destroyed
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// even though it was not charged it is still substracted from the storage deposit tracker
		assert_eq!(ContractInfoOf::<Test>::get(&addr).unwrap().storage_deposit, 550);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Slashed {
						who: addr.clone(),
						amount: 90,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::ReserveRepatriated {
						from: addr.clone(),
						to: ALICE,
						amount: 10,
						destination_status: BalanceStatus::Free,
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn cannot_self_destruct_while_live() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));

		// Call BOB with input data, forcing it make a recursive call to itself to
		// self-destruct, resulting in a trap.
		assert_err_ignore_postinfo!(
			Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![0],),
			Error::<Test>::ContractTrapped,
		);

		// Check that BOB is still there.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));
	});
}

#[test]
fn self_destruct_works() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(1_000).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let _ = Balances::deposit_creating(&DJANGO, 1_000_000);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));

		// Drop all previous events
		initialize_block(2);

		// Call BOB without input data which triggers termination.
		assert_matches!(
			Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
			Ok(_)
		);

		// Check that code is still there but refcount dropped to zero.
		assert_refcount!(&code_hash, 0);

		// Check that account is gone
		assert!(ContractInfoOf::<Test>::get(&addr).is_none());
		assert_eq!(Balances::total_balance(&addr), 0);

		// check that the beneficiary (django) got remaining balance
		assert_eq!(Balances::free_balance(DJANGO), 1_000_000 + 100_000);

		pretty_assertions::assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: addr.clone(),
						to: DJANGO,
						amount: 100_000,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::Terminated {
						contract: addr.clone(),
						beneficiary: DJANGO
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::KilledAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::ReserveRepatriated {
						from: addr.clone(),
						to: ALICE,
						amount: 1_000,
						destination_status: BalanceStatus::Free,
					}),
					topics: vec![],
				},
			],
		);
	});
}

// This tests that one contract cannot prevent another from self-destructing by sending it
// additional funds after it has been drained.
#[test]
fn destroy_contract_and_transfer_funds() {
	let (callee_wasm, callee_code_hash) = compile_module::<Test>("self_destruct").unwrap();
	let (caller_wasm, caller_code_hash) = compile_module::<Test>("destroy_and_transfer").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			200_000,
			GAS_LIMIT,
			None,
			callee_wasm,
			vec![],
			vec![42]
		));

		// This deploys the BOB contract, which in turn deploys the CHARLIE contract during
		// construction.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			200_000,
			GAS_LIMIT,
			None,
			caller_wasm,
			callee_code_hash.as_ref().to_vec(),
			vec![],
		));
		let addr_bob = Contracts::contract_address(&ALICE, &caller_code_hash, &[]);
		let addr_charlie = Contracts::contract_address(&addr_bob, &callee_code_hash, &[0x47, 0x11]);

		// Check that the CHARLIE contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr_charlie), Some(_));

		// Call BOB, which calls CHARLIE, forcing CHARLIE to self-destruct.
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr_bob,
			0,
			GAS_LIMIT,
			None,
			addr_charlie.encode(),
		));

		// Check that CHARLIE has moved on to the great beyond (ie. died).
		assert!(ContractInfoOf::<Test>::get(&addr_charlie).is_none());
	});
}

#[test]
fn cannot_self_destruct_in_constructor() {
	let (wasm, _) = compile_module::<Test>("self_destructing_constructor").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Fail to instantiate the BOB because the contructor calls seal_terminate.
		assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				None,
				wasm,
				vec![],
				vec![],
			),
			Error::<Test>::TerminatedInConstructor,
		);
	});
}

#[test]
fn crypto_hashes() {
	let (wasm, code_hash) = compile_module::<Test>("crypto_hashes").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the CRYPTO_HASHES contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		// Perform the call.
		let input = b"_DEAD_BEEF";
		use sp_io::hashing::*;
		// Wraps a hash function into a more dynamic form usable for testing.
		macro_rules! dyn_hash_fn {
			($name:ident) => {
				Box::new(|input| $name(input).as_ref().to_vec().into_boxed_slice())
			};
		}
		// All hash functions and their associated output byte lengths.
		let test_cases: &[(Box<dyn Fn(&[u8]) -> Box<[u8]>>, usize)] = &[
			(dyn_hash_fn!(sha2_256), 32),
			(dyn_hash_fn!(keccak_256), 32),
			(dyn_hash_fn!(blake2_256), 32),
			(dyn_hash_fn!(blake2_128), 16),
		];
		// Test the given hash functions for the input: "_DEAD_BEEF"
		for (n, (hash_fn, expected_size)) in test_cases.iter().enumerate() {
			// We offset data in the contract tables by 1.
			let mut params = vec![(n + 1) as u8];
			params.extend_from_slice(input);
			let result =
				<Pallet<Test>>::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, params, false)
					.result
					.unwrap();
			assert!(!result.did_revert());
			let expected = hash_fn(input.as_ref());
			assert_eq!(&result.data[..*expected_size], &*expected);
		}
	})
}

#[test]
fn transfer_return_code() {
	let (wasm, code_hash) = compile_module::<Test>("transfer_return_code").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Contract has only the minimal balance so any transfer will fail.
		Balances::make_free_balance_be(&addr, min_balance);
		let result = Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![], false)
			.result
			.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough total balance in order to not go below the min balance
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails.
		Balances::make_free_balance_be(&addr, min_balance + 100);
		Balances::reserve(&addr, min_balance + 100).unwrap();
		let result = Contracts::bare_call(ALICE, addr, 0, GAS_LIMIT, None, vec![], false)
			.result
			.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);
	});
}

#[test]
fn call_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("call_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![0],
			vec![],
		),);
		let addr_bob = Contracts::contract_address(&ALICE, &caller_hash, &[]);
		Balances::make_free_balance_be(&addr_bob, min_balance);

		// Contract calls into Django which is no valid contract
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			None,
			AsRef::<[u8]>::as_ref(&DJANGO).to_vec(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::NotCallable);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(CHARLIE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			callee_code,
			vec![0],
			vec![],
		),);
		let addr_django = Contracts::contract_address(&CHARLIE, &callee_hash, &[]);
		Balances::make_free_balance_be(&addr_django, min_balance);

		// Contract has only the minimal balance so any transfer will fail.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			None,
			AsRef::<[u8]>::as_ref(&addr_django)
				.iter()
				.chain(&0u32.to_le_bytes())
				.cloned()
				.collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough total balance in order to not go below the min balance
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails.
		Balances::make_free_balance_be(&addr_bob, min_balance + 100);
		Balances::reserve(&addr_bob, min_balance + 100).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			None,
			AsRef::<[u8]>::as_ref(&addr_django)
				.iter()
				.chain(&0u32.to_le_bytes())
				.cloned()
				.collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but callee reverts because "1" is passed.
		Balances::make_free_balance_be(&addr_bob, min_balance + 1000);
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			None,
			AsRef::<[u8]>::as_ref(&addr_django)
				.iter()
				.chain(&1u32.to_le_bytes())
				.cloned()
				.collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob,
			0,
			GAS_LIMIT,
			None,
			AsRef::<[u8]>::as_ref(&addr_django)
				.iter()
				.chain(&2u32.to_le_bytes())
				.cloned()
				.collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);
	});
}

#[test]
fn instantiate_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("instantiate_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * min_balance);
		let callee_hash = callee_hash.as_ref().to_vec();

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			callee_code,
			vec![],
			vec![],
		),);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &caller_hash, &[]);

		// Contract has only the minimal balance so any transfer will fail.
		Balances::make_free_balance_be(&addr, min_balance);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			callee_hash.clone(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough total balance in order to not go below the min_balance
		// threshold when transfering the balance but this balance is reserved so
		// the transfer still fails.
		Balances::make_free_balance_be(&addr, min_balance + 10_000);
		Balances::reserve(&addr, min_balance + 10_000).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			callee_hash.clone(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but the passed code hash is invalid
		Balances::make_free_balance_be(&addr, min_balance + 10_000);
		let result =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![0; 33], false)
				.result
				.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CodeNotFound);

		// Contract has enough balance but callee reverts because "1" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			callee_hash.iter().chain(&1u32.to_le_bytes()).cloned().collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			None,
			callee_hash.iter().chain(&2u32.to_le_bytes()).cloned().collect(),
			false,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);
	});
}

#[test]
fn disabled_chain_extension_wont_deploy() {
	let (code, _hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		TestExtension::disable();
		assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				3 * min_balance,
				GAS_LIMIT,
				None,
				code,
				vec![],
				vec![],
			),
			"module uses chain extensions but chain extensions are disabled",
		);
	});
}

#[test]
fn disabled_chain_extension_errors_on_call() {
	let (code, hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		TestExtension::disable();
		assert_err_ignore_postinfo!(
			Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
			Error::<Test>::NoChainExtension,
		);
	});
}

#[test]
fn chain_extension_works() {
	let (code, hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// The contract takes a up to 2 byte buffer where the first byte passed is used as
		// as func_id to the chain extension which behaves differently based on the
		// func_id.

		// 0 = read input buffer and pass it through as output
		let result =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![0, 99], false);
		let gas_consumed = result.gas_consumed;
		assert_eq!(TestExtension::last_seen_buffer(), vec![0, 99]);
		assert_eq!(result.result.unwrap().data, Bytes(vec![0, 99]));

		// 1 = treat inputs as integer primitives and store the supplied integers
		Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![1], false)
			.result
			.unwrap();
		// those values passed in the fixture
		assert_eq!(TestExtension::last_seen_inputs(), (4, 1, 16, 12));

		// 2 = charge some extra weight (amount supplied in second byte)
		let result =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![2, 42], false);
		assert_ok!(result.result);
		assert_eq!(result.gas_consumed, gas_consumed + 42);

		// 3 = diverging chain extension call that sets flags to 0x1 and returns a fixed buffer
		let result = Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![3], false)
			.result
			.unwrap();
		assert_eq!(result.flags, ReturnFlags::REVERT);
		assert_eq!(result.data, Bytes(vec![42, 99]));
	});
}

#[test]
fn lazy_removal_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf<Test>>::get(&addr).unwrap();
		let trie = &info.child_trie_info();

		// Put value into the contracts child trie
		child::put(trie, &[99], &42);

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		// But value should be still there as the lazy removal did not run, yet.
		assert_matches!(child::get(trie, &[99]), Some(42));

		// Run the lazy removal
		Contracts::on_initialize(Weight::max_value());

		// Value should be gone now
		assert_matches!(child::get::<i32>(trie, &[99]), None);
	});
}

#[test]
fn lazy_removal_partial_remove_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();

	// We create a contract with some extra keys above the weight limit
	let extra_keys = 7u32;
	let weight_limit = 5_000_000_000;
	let (_, max_keys) = Storage::<Test>::deletion_budget(1, weight_limit);
	let vals: Vec<_> = (0..max_keys + extra_keys)
		.map(|i| (blake2_256(&i.encode()), (i as u32), (i as u32).encode()))
		.collect();

	let mut ext = ExtBuilder::default().existential_deposit(50).build();

	let trie = ext.execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf<Test>>::get(&addr).unwrap();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(&info.trie_id, &val.0, Some(val.2.clone()), None).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, info.clone());

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		let trie = info.child_trie_info();

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), Some(val.1));
		}

		trie.clone()
	});

	// The lazy removal limit only applies to the backend but not to the overlay.
	// This commits all keys from the overlay to the backend.
	ext.commit_all().unwrap();

	ext.execute_with(|| {
		// Run the lazy removal
		let weight_used = Storage::<Test>::process_deletion_queue_batch(weight_limit);

		// Weight should be exhausted because we could not even delete all keys
		assert_eq!(weight_used, weight_limit);

		let mut num_deleted = 0u32;
		let mut num_remaining = 0u32;

		for val in &vals {
			match child::get::<u32>(&trie, &blake2_256(&val.0)) {
				None => num_deleted += 1,
				Some(x) if x == val.1 => num_remaining += 1,
				Some(_) => panic!("Unexpected value in contract storage"),
			}
		}

		// All but one key is removed
		assert_eq!(num_deleted + num_remaining, vals.len() as u32);
		assert_eq!(num_deleted, max_keys);
		assert_eq!(num_remaining, extra_keys);
	});
}

#[test]
fn lazy_removal_does_no_run_on_full_block() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf<Test>>::get(&addr).unwrap();
		let max_keys = 30;

		// Create some storage items for the contract.
		let vals: Vec<_> = (0..max_keys)
			.map(|i| (blake2_256(&i.encode()), (i as u32), (i as u32).encode()))
			.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(&info.trie_id, &val.0, Some(val.2.clone()), None).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, info.clone());

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		let trie = info.child_trie_info();

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), Some(val.1));
		}

		// Fill up the block which should prevent the lazy storage removal from running.
		System::register_extra_weight_unchecked(
			<Test as system::Config>::BlockWeights::get().max_block,
			DispatchClass::Mandatory,
		);

		// Run the lazy removal without any limit so that all keys would be removed if there
		// had been some weight left in the block.
		let weight_used = Contracts::on_initialize(Weight::max_value());
		let base = <<Test as Config>::WeightInfo as WeightInfo>::on_initialize();
		assert_eq!(weight_used, base);

		// All the keys are still in place
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), Some(val.1));
		}

		// Run the lazy removal directly which disregards the block limits
		Storage::<Test>::process_deletion_queue_batch(Weight::max_value());

		// Now the keys should be gone
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), None);
		}
	});
}

#[test]
fn lazy_removal_does_not_use_all_weight() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();

	let weight_limit = 5_000_000_000;
	let mut ext = ExtBuilder::default().existential_deposit(50).build();

	let (trie, vals, weight_per_key) = ext.execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf<Test>>::get(&addr).unwrap();
		let (weight_per_key, max_keys) = Storage::<Test>::deletion_budget(1, weight_limit);

		// We create a contract with one less storage item than we can remove within the limit
		let vals: Vec<_> = (0..max_keys - 1)
			.map(|i| (blake2_256(&i.encode()), (i as u32), (i as u32).encode()))
			.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(&info.trie_id, &val.0, Some(val.2.clone()), None).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, info.clone());

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		let trie = info.child_trie_info();

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), Some(val.1));
		}

		(trie, vals, weight_per_key)
	});

	// The lazy removal limit only applies to the backend but not to the overlay.
	// This commits all keys from the overlay to the backend.
	ext.commit_all().unwrap();

	ext.execute_with(|| {
		// Run the lazy removal
		let weight_used = Storage::<Test>::process_deletion_queue_batch(weight_limit);

		// We have one less key in our trie than our weight limit suffices for
		assert_eq!(weight_used, weight_limit - weight_per_key);

		// All the keys are removed
		for val in vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), None);
		}
	});
}

#[test]
fn deletion_queue_full() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// fill the deletion queue up until its limit
		Storage::<Test>::fill_queue_with_dummies();

		// Terminate the contract should fail
		assert_err_ignore_postinfo!(
			Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
			Error::<Test>::DeletionQueueFull,
		);

		// Contract should exist because removal failed
		<ContractInfoOf<Test>>::get(&addr).unwrap();
	});
}

#[test]
fn refcounter() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Create two contracts with the same code and check that they do in fact share it.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			wasm.clone(),
			vec![],
			vec![0],
		));
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			wasm.clone(),
			vec![],
			vec![1],
		));
		assert_refcount!(code_hash, 2);

		// Sharing should also work with the usual instantiate call
		assert_ok!(Contracts::instantiate(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code_hash,
			vec![],
			vec![2],
		));
		assert_refcount!(code_hash, 3);

		// addresses of all three existing contracts
		let addr0 = Contracts::contract_address(&ALICE, &code_hash, &[0]);
		let addr1 = Contracts::contract_address(&ALICE, &code_hash, &[1]);
		let addr2 = Contracts::contract_address(&ALICE, &code_hash, &[2]);

		// Terminating one contract should decrement the refcount
		assert_ok!(Contracts::call(Origin::signed(ALICE), addr0, 0, GAS_LIMIT, None, vec![]));
		assert_refcount!(code_hash, 2);

		// remove another one
		assert_ok!(Contracts::call(Origin::signed(ALICE), addr1, 0, GAS_LIMIT, None, vec![]));
		assert_refcount!(code_hash, 1);

		// Pristine code should still be there
		crate::PristineCode::<Test>::get(code_hash).unwrap();

		// remove the last contract
		assert_ok!(Contracts::call(Origin::signed(ALICE), addr2, 0, GAS_LIMIT, None, vec![]));
		assert_refcount!(code_hash, 0);

		// refcount is `0` but code should still exists because it needs to be removed manually
		assert!(crate::PristineCode::<Test>::contains_key(&code_hash));
		assert!(crate::CodeStorage::<Test>::contains_key(&code_hash));
	});
}

#[test]
fn reinstrument_does_charge() {
	let (wasm, code_hash) = compile_module::<Test>("return_with_data").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let zero = 0u32.to_le_bytes().encode();
		let code_len = wasm.len() as u32;

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			wasm,
			zero.clone(),
			vec![],
		));

		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Call the contract two times without reinstrument

		let result0 =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, zero.clone(), false);
		assert!(!result0.result.unwrap().did_revert());

		let result1 =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, zero.clone(), false);
		assert!(!result1.result.unwrap().did_revert());

		// They should match because both where called with the same schedule.
		assert_eq!(result0.gas_consumed, result1.gas_consumed);

		// We cannot change the schedule. Instead, we decrease the version of the deployed
		// contract below the current schedule's version.
		crate::CodeStorage::mutate(&code_hash, |code: &mut Option<PrefabWasmModule<Test>>| {
			code.as_mut().unwrap().decrement_version();
		});

		// This call should trigger reinstrumentation
		let result2 =
			Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, zero.clone(), false);
		assert!(!result2.result.unwrap().did_revert());
		assert!(result2.gas_consumed > result1.gas_consumed);
		assert_eq!(
			result2.gas_consumed,
			result1.gas_consumed + <Test as Config>::WeightInfo::reinstrument(code_len / 1024),
		);
	});
}

#[test]
fn debug_message_works() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_works").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(ALICE, addr, 0, GAS_LIMIT, None, vec![], true);

		assert_matches!(result.result, Ok(_));
		assert_eq!(std::str::from_utf8(&result.debug_message).unwrap(), "Hello World!");
	});
}

#[test]
fn debug_message_logging_disabled() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_logging_disabled").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		// disable logging by passing `false`
		let result = Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, vec![], false);
		assert_matches!(result.result, Ok(_));
		// the dispatchables always run without debugging
		assert_ok!(Contracts::call(Origin::signed(ALICE), addr, 0, GAS_LIMIT, None, vec![]));
		assert!(result.debug_message.is_empty());
	});
}

#[test]
fn debug_message_invalid_utf8() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_invalid_utf8").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(ALICE, addr, 0, GAS_LIMIT, None, vec![], true);
		assert_err!(result.result, <Error<Test>>::DebugMessageInvalidUTF8);
	});
}

#[test]
fn gas_estimation_nested_call_fixed_limit() {
	let (caller_code, caller_hash) = compile_module::<Test>("call_with_limit").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![],
			vec![0],
		),);
		let addr_caller = Contracts::contract_address(&ALICE, &caller_hash, &[0]);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			callee_code,
			vec![],
			vec![1],
		),);
		let addr_callee = Contracts::contract_address(&ALICE, &callee_hash, &[1]);

		let input: Vec<u8> = AsRef::<[u8]>::as_ref(&addr_callee)
			.iter()
			.cloned()
			.chain((GAS_LIMIT / 5).to_le_bytes())
			.collect();

		// Call in order to determine the gas that is required for this call
		let result = Contracts::bare_call(
			ALICE,
			addr_caller.clone(),
			0,
			GAS_LIMIT,
			None,
			input.clone(),
			false,
		);
		assert_ok!(&result.result);

		// We have a subcall with a fixed gas limit. This constitutes precharging.
		assert!(result.gas_required > result.gas_consumed);

		// Make the same call using the estimated gas. Should succeed.
		assert_ok!(
			Contracts::bare_call(
				ALICE,
				addr_caller,
				0,
				result.gas_required,
				Some(result.storage_deposit.charge_or_zero()),
				input,
				false,
			)
			.result
		);
	});
}

#[test]
#[cfg(feature = "unstable-interface")]
fn gas_estimation_call_runtime() {
	let (caller_code, caller_hash) = compile_module::<Test>("call_runtime").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![],
			vec![0],
		),);
		let addr_caller = Contracts::contract_address(&ALICE, &caller_hash, &[0]);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			callee_code,
			vec![],
			vec![1],
		),);
		let addr_callee = Contracts::contract_address(&ALICE, &callee_hash, &[1]);

		// Call something trivial with a huge gas limit so that we can observe the effects
		// of pre-charging. This should create a difference between consumed and required.
		let call = Call::Contracts(crate::Call::call {
			dest: addr_callee,
			value: 0,
			gas_limit: GAS_LIMIT / 3,
			storage_deposit_limit: None,
			data: vec![],
		});
		let result = Contracts::bare_call(
			ALICE,
			addr_caller.clone(),
			0,
			GAS_LIMIT,
			None,
			call.encode(),
			false,
		);
		assert_ok!(&result.result);

		assert!(result.gas_required > result.gas_consumed);

		// Make the same call using the required gas. Should succeed.
		assert_ok!(
			Contracts::bare_call(
				ALICE,
				addr_caller,
				0,
				result.gas_required,
				None,
				call.encode(),
				false,
			)
			.result
		);
	});
}

#[test]
#[cfg(feature = "unstable-interface")]
fn ecdsa_recover() {
	let (wasm, code_hash) = compile_module::<Test>("ecdsa_recover").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the ecdsa_recover contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		#[rustfmt::skip]
		let signature: [u8; 65] = [
			161, 234, 203,  74, 147, 96,  51, 212,   5, 174, 231,   9, 142,  48, 137, 201,
			162, 118, 192,  67, 239, 16,  71, 216, 125,  86, 167, 139,  70,   7,  86, 241,
			 33,  87, 154, 251,  81, 29, 160,   4, 176, 239,  88, 211, 244, 232, 232,  52,
			211, 234, 100, 115, 230, 47,  80,  44, 152, 166,  62,  50,   8,  13,  86, 175,
			 28,
		];
		#[rustfmt::skip]
		let message_hash: [u8; 32] = [
			162, 28, 244, 179, 96, 76, 244, 178, 188,  83, 230, 248, 143, 106,  77, 117,
			239, 95, 244, 171, 65, 95,  62, 153, 174, 166, 182,  28, 130,  73, 196, 208
		];
		#[rustfmt::skip]
		const EXPECTED_COMPRESSED_PUBLIC_KEY: [u8; 33] = [
			  2, 121, 190, 102, 126, 249, 220, 187, 172, 85, 160,  98, 149, 206, 135, 11,
			  7,   2, 155, 252, 219,  45, 206,  40, 217, 89, 242, 129,  91,  22, 248, 23,
			152,
		];
		let mut params = vec![];
		params.extend_from_slice(&signature);
		params.extend_from_slice(&message_hash);
		assert!(params.len() == 65 + 32);
		let result =
			<Pallet<Test>>::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, params, false)
				.result
				.unwrap();
		assert!(!result.did_revert());
		assert_eq!(result.data.as_ref(), &EXPECTED_COMPRESSED_PUBLIC_KEY);
	})
}

#[test]
fn upload_code_works() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Drop previous events
		initialize_block(2);

		assert!(!<CodeStorage<Test>>::contains_key(code_hash));
		assert_ok!(Contracts::upload_code(
			Origin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000))
		));
		assert!(<CodeStorage<Test>>::contains_key(code_hash));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn upload_code_limit_too_low() {
	let (wasm, _code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Drop previous events
		initialize_block(2);

		assert_noop!(
			Contracts::upload_code(Origin::signed(ALICE), wasm, Some(codec::Compact(100))),
			<Error<Test>>::StorageDepositLimitExhausted,
		);

		assert_eq!(System::events(), vec![]);
	});
}

#[test]
fn upload_code_not_enough_balance() {
	let (wasm, _code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 150);

		// Drop previous events
		initialize_block(2);

		assert_noop!(
			Contracts::upload_code(Origin::signed(ALICE), wasm, Some(codec::Compact(1_000))),
			<Error<Test>>::StorageDepositNotEnoughFunds,
		);

		assert_eq!(System::events(), vec![]);
	});
}

#[test]
fn remove_code_works() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Drop previous events
		initialize_block(2);

		assert_ok!(Contracts::upload_code(
			Origin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000))
		));

		assert!(<CodeStorage<Test>>::contains_key(code_hash));
		assert_ok!(Contracts::remove_code(Origin::signed(ALICE), code_hash));
		assert!(!<CodeStorage<Test>>::contains_key(code_hash));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Unreserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeRemoved { code_hash }),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn remove_code_wrong_origin() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Drop previous events
		initialize_block(2);

		assert_ok!(Contracts::upload_code(
			Origin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000))
		));

		assert_noop!(
			Contracts::remove_code(Origin::signed(BOB), code_hash),
			sp_runtime::traits::BadOrigin,
		);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn remove_code_in_use() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));

		// Drop previous events
		initialize_block(2);

		assert_noop!(
			Contracts::remove_code(Origin::signed(ALICE), code_hash),
			<Error<Test>>::CodeInUse,
		);

		assert_eq!(System::events(), vec![]);
	});
}

#[test]
fn remove_code_not_found() {
	let (_wasm, code_hash) = compile_module::<Test>("dummy").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Drop previous events
		initialize_block(2);

		assert_noop!(
			Contracts::remove_code(Origin::signed(ALICE), code_hash),
			<Error<Test>>::CodeNotFound,
		);

		assert_eq!(System::events(), vec![]);
	});
}

#[test]
fn instantiate_with_zero_balance_works() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Drop previous events
		initialize_block(2);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));

		// Make sure the account exists even though no free balance was send
		assert_eq!(<Test as Config>::Currency::free_balance(&addr), 0,);
		assert_eq!(
			<Test as Config>::Currency::total_balance(&addr),
			<Test as Config>::Currency::minimum_balance(),
		);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::NewAccount { account: addr.clone() }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn instantiate_with_below_existential_deposit_works() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Drop previous events
		initialize_block(2);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			50,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(_));

		// Make sure the account exists even though no free balance was send
		assert_eq!(<Test as Config>::Currency::free_balance(&addr), 50,);
		assert_eq!(
			<Test as Config>::Currency::total_balance(&addr),
			<Test as Config>::Currency::minimum_balance() + 50,
		);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::NewAccount { account: addr.clone() }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: 50,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 180,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn storage_deposit_works() {
	let (wasm, code_hash) = compile_module::<Test>("multi_store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let mut deposit = <Test as Config>::Currency::minimum_balance();

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Drop previous events
		initialize_block(2);

		// Create storage
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			42,
			GAS_LIMIT,
			None,
			(1_000u32, 5_000u32).encode(),
		));
		// 4 is for creating 2 storage items
		let charged0 = 4 + 1_000 + 5_000;
		deposit += charged0;
		assert_eq!(<ContractInfoOf<Test>>::get(&addr).unwrap().storage_deposit, deposit);

		// Add more storage (but also remove some)
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			(2_000u32, 4_900u32).encode(),
		));
		let charged1 = 1_000 - 100;
		deposit += charged1;
		assert_eq!(<ContractInfoOf<Test>>::get(&addr).unwrap().storage_deposit, deposit);

		// Remove more storage (but also add some)
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			(2_100u32, 900u32).encode(),
		));
		let refunded0 = 4_000 - 100;
		deposit -= refunded0;
		assert_eq!(<ContractInfoOf<Test>>::get(&addr).unwrap().storage_deposit, deposit);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: 42,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: charged0,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: charged0,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: charged1,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: charged1,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::ReserveRepatriated {
						from: addr.clone(),
						to: ALICE,
						amount: refunded0,
						destination_status: BalanceStatus::Free,
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn call_after_killed_account_needs_funding() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			700,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Drop previous events
		initialize_block(2);

		// Destroy the account of the contract by slashing.
		// Slashing can actually happen if the contract takes part in staking.
		// It is a corner case and we except the destruction of the account.
		let _ = <Test as Config>::Currency::slash(
			&addr,
			<Test as Config>::Currency::total_balance(&addr),
		);

		// Sending below the minimum balance will fail the call because it needs to create the
		// account in order to send balance there.
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				min_balance - 1,
				GAS_LIMIT,
				None,
				vec![],
			),
			<Error<Test>>::TransferFailed
		);

		// Sending zero should work as it does not do a transfer
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![],
		));

		// Sending minimum balance should work
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			min_balance,
			GAS_LIMIT,
			None,
			vec![],
		));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::KilledAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Slashed {
						who: addr.clone(),
						amount: min_balance + 700
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::System(frame_system::Event::NewAccount { account: addr.clone() }),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance
					}),
					topics: vec![],
				},
			]
		);
	});
}

#[test]
fn contract_reverted() {
	let (wasm, code_hash) = compile_module::<Test>("return_with_data").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let flags = ReturnFlags::REVERT;
		let buffer = [4u8, 8, 15, 16, 23, 42];
		let input = (flags.bits(), buffer).encode();

		// We just upload the code for later use
		assert_ok!(Contracts::upload_code(Origin::signed(ALICE), wasm.clone(), None));

		// Calling extrinsic: revert leads to an error
		assert_err_ignore_postinfo!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				0,
				GAS_LIMIT,
				None,
				code_hash,
				input.clone(),
				vec![],
			),
			<Error<Test>>::ContractReverted,
		);

		// Calling extrinsic: revert leads to an error
		assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				0,
				GAS_LIMIT,
				None,
				wasm,
				input.clone(),
				vec![],
			),
			<Error<Test>>::ContractReverted,
		);

		// Calling directly: revert leads to success but the flags indicate the error
		// This is just a different way of transporting the error that allows the read out
		// the `data` which is only there on success. Obviously, the contract isn't
		// instantiated.
		let result = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Existing(code_hash),
			input.clone(),
			vec![],
			false,
		)
		.result
		.unwrap();
		assert_eq!(result.result.flags, flags);
		assert_eq!(result.result.data.0, buffer);
		assert!(!<ContractInfoOf<Test>>::contains_key(result.account_id));

		// Pass empty flags and therefore successfully instantiate the contract for later use.
		let addr = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Existing(code_hash),
			ReturnFlags::empty().bits().encode(),
			vec![],
			false,
		)
		.result
		.unwrap()
		.account_id;

		// Calling extrinsic: revert leads to an error
		assert_err_ignore_postinfo!(
			Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, input.clone()),
			<Error<Test>>::ContractReverted,
		);

		// Calling directly: revert leads to success but the flags indicate the error
		let result = Contracts::bare_call(ALICE, addr.clone(), 0, GAS_LIMIT, None, input, false)
			.result
			.unwrap();
		assert_eq!(result.flags, flags);
		assert_eq!(result.data.0, buffer);
	});
}
