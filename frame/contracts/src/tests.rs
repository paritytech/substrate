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
	BalanceOf, ContractInfo, ContractInfoOf, GenesisConfig, Module,
	RawAliveContractInfo, RawEvent, Config, Schedule, gas::Gas,
	Error, ConfigCache, RuntimeReturnCode, storage::Storage,
	chain_extension::{
		Result as ExtensionResult, Environment, ChainExtension, Ext, SysConfig, RetVal,
		UncheckedFrom, InitState, ReturnFlags,
	},
	exec::AccountIdOf,
};
use assert_matches::assert_matches;
use codec::Encode;
use sp_runtime::{
	traits::{BlakeTwo256, Hash, IdentityLookup, Convert},
	testing::{Header, H256},
	AccountId32,
};
use sp_io::hashing::blake2_256;
use frame_support::{
	assert_ok, assert_err, assert_err_ignore_postinfo, impl_outer_dispatch, impl_outer_event,
	impl_outer_origin, parameter_types, StorageMap,
	traits::{Currency, ReservableCurrency, OnInitialize},
	weights::{Weight, PostDispatchInfo, DispatchClass, constants::WEIGHT_PER_SECOND},
	dispatch::DispatchErrorWithPostInfo,
	storage::child,
};
use frame_system::{self as system, EventRecord, Phase};

mod contracts {
	// Re-export contents of the root. This basically
	// needs to give a name for the current crate.
	// This hack is required for `impl_outer_event!`.
	pub use super::super::*;
	pub use frame_support::impl_outer_event;
}

use pallet_balances as balances;

impl_outer_event! {
	pub enum MetaEvent for Test {
		system<T>,
		balances<T>,
		contracts<T>,
	}
}
impl_outer_origin! {
	pub enum Origin for Test where system = frame_system { }
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		balances::Balances,
		contracts::Contracts,
	}
}

#[macro_use]
pub mod test_utils {
	use super::{Test, Balances};
	use crate::{
		ContractInfoOf, CodeHash,
		storage::Storage,
		exec::{StorageKey, AccountIdOf},
	};
	use frame_support::{StorageMap, traits::Currency};

	pub fn set_storage(addr: &AccountIdOf<Test>, key: &StorageKey, value: Option<Vec<u8>>) {
		let contract_info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		Storage::<Test>::write(addr, &contract_info.trie_id, key, value).unwrap();
	}
	pub fn get_storage(addr: &AccountIdOf<Test>, key: &StorageKey) -> Option<Vec<u8>> {
		let contract_info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		Storage::<Test>::read(&contract_info.trie_id, key)
	}
	pub fn place_contract(address: &AccountIdOf<Test>, code_hash: CodeHash<Test>) {
		let trie_id = Storage::<Test>::generate_trie_id(address);
		Storage::<Test>::place_contract(&address, trie_id, code_hash).unwrap()
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
		}}
	}
}

thread_local! {
	static TEST_EXTENSION: sp_std::cell::RefCell<TestExtension> = Default::default();
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
		Self {
			enabled: true,
			last_seen_buffer: vec![],
			last_seen_inputs: (0, 0, 0, 0),
		}
	}
}

impl ChainExtension for TestExtension {
	fn call<E: Ext>(func_id: u32, env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
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
				TEST_EXTENSION.with(|e|
					e.borrow_mut().last_seen_inputs = (
						env.val0(), env.val1(), env.val2(), env.val3()
					)
				);
				Ok(RetVal::Converging(func_id))
			},
			2 => {
				let mut env = env.buf_in_buf_out();
				let weight = env.read(2)?[1].into();
				env.charge_weight(weight)?;
				Ok(RetVal::Converging(func_id))
			},
			3 => {
				Ok(RetVal::Diverging{
					flags: ReturnFlags::REVERT,
					data: vec![42, 99],
				})
			},
			_ => {
				panic!("Passed unknown func_id to test chain extension: {}", func_id);
			}
		}
	}

	fn enabled() -> bool {
		TEST_EXTENSION.with(|e| e.borrow().enabled)
	}
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(2 * WEIGHT_PER_SECOND);
	pub static ExistentialDeposit: u64 = 0;
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
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
	type Event = MetaEvent;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type Balance = u64;
	type Event = MetaEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub const MinimumPeriod: u64 = 1;
}
impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}
parameter_types! {
	pub const SignedClaimHandicap: u64 = 2;
	pub const TombstoneDeposit: u64 = 16;
	pub const StorageSizeOffset: u32 = 8;
	pub const RentByteFee: u64 = 4;
	pub const RentDepositOffset: u64 = 10_000;
	pub const SurchargeReward: u64 = 150;
	pub const MaxDepth: u32 = 100;
	pub const MaxValueSize: u32 = 16_384;
	pub const DeletionQueueDepth: u32 = 1024;
	pub const DeletionWeightLimit: Weight = 500_000_000_000;
}

parameter_types! {
	pub const TransactionByteFee: u64 = 0;
}

impl Convert<Weight, BalanceOf<Self>> for Test {
	fn convert(w: Weight) -> BalanceOf<Self> {
		w
	}
}

impl Config for Test {
	type Time = Timestamp;
	type Randomness = Randomness;
	type Currency = Balances;
	type Event = MetaEvent;
	type RentPayment = ();
	type SignedClaimHandicap = SignedClaimHandicap;
	type TombstoneDeposit = TombstoneDeposit;
	type StorageSizeOffset = StorageSizeOffset;
	type RentByteFee = RentByteFee;
	type RentDepositOffset = RentDepositOffset;
	type SurchargeReward = SurchargeReward;
	type MaxDepth = MaxDepth;
	type MaxValueSize = MaxValueSize;
	type WeightPrice = Self;
	type WeightInfo = ();
	type ChainExtension = TestExtension;
	type DeletionQueueDepth = DeletionQueueDepth;
	type DeletionWeightLimit = DeletionWeightLimit;
}

type Balances = pallet_balances::Module<Test>;
type Timestamp = pallet_timestamp::Module<Test>;
type Contracts = Module<Test>;
type System = frame_system::Module<Test>;
type Randomness = pallet_randomness_collective_flip::Module<Test>;

pub const ALICE: AccountId32 = AccountId32::new([1u8; 32]);
pub const BOB: AccountId32 = AccountId32::new([2u8; 32]);
pub const CHARLIE: AccountId32 = AccountId32::new([3u8; 32]);
pub const DJANGO: AccountId32 = AccountId32::new([4u8; 32]);

const GAS_LIMIT: Gas = 10_000_000_000;

pub struct ExtBuilder {
	existential_deposit: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 1,
		}
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
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig {
			current_schedule: Schedule::<Test> {
				enable_println: true,
				..Default::default()
			},
		}.assimilate_storage(&mut t).unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

/// Load a given wasm module represented by a .wat file and returns a wasm binary contents along
/// with it's hash.
///
/// The fixture files are located under the `fixtures/` directory.
fn compile_module<T>(
	fixture_name: &str,
) -> wat::Result<(Vec<u8>, <T::Hashing as Hash>::Output)>
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
// Then we check that no gas was used because the base costs for calling are either charged
// as part of the `call` extrinsic or by `seal_call`.
#[test]
fn calling_plain_account_fails() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 100_000_000);

		assert_eq!(
			Contracts::call(Origin::signed(ALICE), BOB, 0, GAS_LIMIT, Vec::new()),
			Err(
				DispatchErrorWithPostInfo {
					error: Error::<Test>::NotCallable.into(),
					post_info: PostDispatchInfo {
						actual_weight: Some(0),
						pays_fee: Default::default(),
					},
				}
			)
		);
	});
}

#[test]
fn account_removal_does_not_remove_storage() {
	use self::test_utils::{set_storage, get_storage};

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let trie_id1 = Storage::<Test>::generate_trie_id(&ALICE);
		let trie_id2 = Storage::<Test>::generate_trie_id(&BOB);
		let key1 = &[1; 32];
		let key2 = &[2; 32];

		// Set up two accounts with free balance above the existential threshold.
		{
			let alice_contract_info = ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id1.clone(),
				storage_size: 0,
				empty_pair_count: 0,
				total_pair_count: 0,
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(1),
				rent_allowance: 40,
				last_write: None,
			});
			let _ = Balances::deposit_creating(&ALICE, 110);
			ContractInfoOf::<Test>::insert(ALICE, &alice_contract_info);
			set_storage(&ALICE, &key1, Some(b"1".to_vec()));
			set_storage(&ALICE, &key2, Some(b"2".to_vec()));

			let bob_contract_info = ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id2.clone(),
				storage_size: 0,
				empty_pair_count: 0,
				total_pair_count: 0,
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(2),
				rent_allowance: 40,
				last_write: None,
			});
			let _ = Balances::deposit_creating(&BOB, 110);
			ContractInfoOf::<Test>::insert(BOB, &bob_contract_info);
			set_storage(&BOB, &key1, Some(b"3".to_vec()));
			set_storage(&BOB, &key2, Some(b"4".to_vec()));
		}

		// Transfer funds from ALICE account of such amount that after this transfer
		// the balance of the ALICE account will be below the existential threshold.
		//
		// This does not remove the contract storage as we are not notified about a
		// account removal. This cannot happen in reality because a contract can only
		// remove itself by `seal_terminate`. There is no external event that can remove
		// the account appart from that.
		assert_ok!(Balances::transfer(Origin::signed(ALICE), BOB, 20));

		// Verify that no entries are removed.
		{
			assert_eq!(
				get_storage(&ALICE, key1),
				Some(b"1".to_vec())
			);
			assert_eq!(
				get_storage(&ALICE, key2),
				Some(b"2".to_vec())
			);

			assert_eq!(
				get_storage(&BOB, key1),
				Some(b"3".to_vec())
			);
			assert_eq!(
				get_storage(&BOB, key2),
				Some(b"4".to_vec())
			);
		}
	});
}

#[test]
fn instantiate_and_call_and_deposit_event() {
	let (wasm, code_hash) = compile_module::<Test>("return_from_start_fn").unwrap();

	ExtBuilder::default()
		.existential_deposit(100)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			let subsistence = super::ConfigCache::<Test>::subsistence_threshold_uncached();

			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Check at the end to get hash on error easily
			let creation = Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			);
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			pretty_assertions::assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::system(frame_system::RawEvent::NewAccount(ALICE.clone())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::balances(
						pallet_balances::RawEvent::Endowed(ALICE, 1_000_000)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::CodeStored(code_hash.into())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::system(frame_system::RawEvent::NewAccount(addr.clone())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::balances(
						pallet_balances::RawEvent::Endowed(addr.clone(), subsistence)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::balances(
						pallet_balances::RawEvent::Transfer(ALICE, addr.clone(), subsistence)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(
						RawEvent::ContractExecution(addr.clone(), vec![1, 2, 3, 4])
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::Instantiated(ALICE, addr.clone())),
					topics: vec![],
				}
			]);

			assert_ok!(creation);
			assert!(ContractInfoOf::<Test>::contains_key(&addr));
		});
}

#[test]
fn deposit_event_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>("event_size").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check creation
			let bob_contract = ContractInfoOf::<Test>::get(addr.clone())
				.unwrap()
				.get_alive()
				.unwrap();
			assert_eq!(bob_contract.rent_allowance, <BalanceOf<Test>>::max_value());

			// Call contract with allowed storage value.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT * 2, // we are copying a huge buffer,
				<Test as Config>::MaxValueSize::get().encode(),
			));

			// Call contract with too large a storage value.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE),
					addr,
					0,
					GAS_LIMIT,
					(<Test as Config>::MaxValueSize::get() + 1).encode(),
				),
				Error::<Test>::ValueTooLarge,
			);
		});
}

#[test]
fn run_out_of_gas() {
	let (wasm, code_hash) = compile_module::<Test>("run_out_of_gas").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);

			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100,
				GAS_LIMIT,
				code_hash.into(),
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
					67_500_000,
					vec![],
				),
				Error::<Test>::OutOfGas,
			);
		});
}

/// Input data for each call in set_rent code
mod call {
	use super::{AccountIdOf, Test};
	pub fn set_storage_4_byte() -> Vec<u8> { 0u32.to_le_bytes().to_vec() }
	pub fn remove_storage_4_byte() -> Vec<u8> { 1u32.to_le_bytes().to_vec() }
	pub fn transfer(to: &AccountIdOf<Test>) -> Vec<u8> {
		2u32.to_le_bytes().iter().chain(AsRef::<[u8]>::as_ref(to)).cloned().collect()
	}
	pub fn null() -> Vec<u8> { 3u32.to_le_bytes().to_vec() }
}

/// Test correspondence of set_rent code and its hash.
/// Also test that encoded extrinsic in code correspond to the correct transfer
#[test]
fn test_set_rent_code_and_hash() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// If you ever need to update the wasm source this test will fail
			// and will show you the actual hash.
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::system(frame_system::RawEvent::NewAccount(ALICE)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::balances(pallet_balances::RawEvent::Endowed(
						ALICE, 1_000_000
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::CodeStored(code_hash.into())),
					topics: vec![],
				},
			]);
		});
}

#[test]
fn storage_size() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	// Storage size
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let bob_contract = ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_alive()
				.unwrap();
			assert_eq!(
				bob_contract.storage_size,
				4
			);
			assert_eq!(
				bob_contract.total_pair_count,
				1,
			);
			assert_eq!(
				bob_contract.empty_pair_count,
				0,
			);

			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				call::set_storage_4_byte()
			));
			let bob_contract = ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_alive()
				.unwrap();
			assert_eq!(
				bob_contract.storage_size,
				4 + 4
			);
			assert_eq!(
				bob_contract.total_pair_count,
				2,
			);
			assert_eq!(
				bob_contract.empty_pair_count,
				0,
			);

			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				call::remove_storage_4_byte()
			));
			let bob_contract = ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_alive()
				.unwrap();
			assert_eq!(
				bob_contract.storage_size,
				4
			);
			assert_eq!(
				bob_contract.total_pair_count,
				1,
			);
			assert_eq!(
				bob_contract.empty_pair_count,
				0,
			);
		});
}

#[test]
fn empty_kv_pairs() {
	let (wasm, code_hash) = compile_module::<Test>("set_empty_storage").unwrap();

	ExtBuilder::default()
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let bob_contract = ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_alive()
				.unwrap();

			assert_eq!(
				bob_contract.storage_size,
				0,
			);
			assert_eq!(
				bob_contract.total_pair_count,
				1,
			);
			assert_eq!(
				bob_contract.empty_pair_count,
				1,
			);
		});
}

fn initialize_block(number: u64) {
	System::initialize(
		&number,
		&[0u8; 32].into(),
		&Default::default(),
		Default::default(),
	);
}

#[test]
fn deduct_blocks() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT, code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check creation
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 1_000);

			// Advance 4 blocks
			initialize_block(5);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check result
			let rent = (8 + 4 - 3) // storage size = size_offset + deploy_set_storage - deposit_offset
				* 4 // rent byte price
				* 4; // blocks to rent
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 1_000 - rent);
			assert_eq!(bob_contract.deduct_block, 5);
			assert_eq!(Balances::free_balance(&addr), 30_000 - rent);

			// Advance 7 blocks more
			initialize_block(12);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check result
			let rent_2 = (8 + 4 - 2) // storage size = size_offset + deploy_set_storage - deposit_offset
				* 4 // rent byte price
				* 7; // blocks to rent
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 1_000 - rent - rent_2);
			assert_eq!(bob_contract.deduct_block, 12);
			assert_eq!(Balances::free_balance(&addr), 30_000 - rent - rent_2);

			// Second call on same block should have no effect on rent
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 1_000 - rent - rent_2);
			assert_eq!(bob_contract.deduct_block, 12);
			assert_eq!(Balances::free_balance(&addr), 30_000 - rent - rent_2);
		});
}

#[test]
fn inherent_claim_surcharge_contract_removals() {
	removals(|addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok());
}

#[test]
fn signed_claim_surcharge_contract_removals() {
	removals(|addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok());
}

#[test]
fn claim_surcharge_malus() {
	// Test surcharge malus for inherent
	claim_surcharge(4, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(3, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(2, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(1, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), false);

	// Test surcharge malus for signed
	claim_surcharge(4, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), true);
	claim_surcharge(3, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
	claim_surcharge(2, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
	claim_surcharge(1, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
}

/// Claim surcharge with the given trigger_call at the given blocks.
/// If `removes` is true then assert that the contract is a tombstone.
fn claim_surcharge(blocks: u64, trigger_call: impl Fn(AccountIdOf<Test>) -> bool, removes: bool) {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100,
				GAS_LIMIT, code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Advance blocks
			initialize_block(blocks);

			// Trigger rent through call
			assert_eq!(trigger_call(addr.clone()), removes);

			if removes {
				assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_tombstone().is_some());
			} else {
				assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().is_some());
			}
		});
}

/// Test for all kind of removals for the given trigger:
/// * if balance is reached and balance > subsistence threshold
/// * if allowance is exceeded
/// * if balance is reached and balance < subsistence threshold
///	    * this case cannot be triggered by a contract: we check whether a tombstone is left
fn removals(trigger_call: impl Fn(AccountIdOf<Test>) -> bool) {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	// Balance reached and superior to subsistence threshold
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm.clone()));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100,
				GAS_LIMIT, code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			let subsistence_threshold = 50 /*existential_deposit*/ + 16 /*tombstone_deposit*/;

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap().rent_allowance, 1_000);
			assert_eq!(Balances::free_balance(&addr), 100);

			// Advance blocks
			initialize_block(10);

			// Trigger rent through call
			assert!(trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_tombstone().is_some());
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);

			// Advance blocks
			initialize_block(20);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_tombstone().is_some());
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);
		});

	// Allowance exceeded
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm.clone()));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				1_000,
				GAS_LIMIT,
				code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(100u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr)
					.unwrap()
					.get_alive()
					.unwrap()
					.rent_allowance,
				100
			);
			assert_eq!(Balances::free_balance(&addr), 1_000);

			// Advance blocks
			initialize_block(10);

			// Trigger rent through call
			assert!(trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_tombstone()
				.is_some());
			// Balance should be initial balance - initial rent_allowance
			assert_eq!(Balances::free_balance(&addr), 900);

			// Advance blocks
			initialize_block(20);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_tombstone()
				.is_some());
			assert_eq!(Balances::free_balance(&addr), 900);
		});

	// Balance reached and inferior to subsistence threshold
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			let subsistence_threshold =
				Balances::minimum_balance() + <Test as Config>::TombstoneDeposit::get();
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm.clone()));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				50 + subsistence_threshold,
				GAS_LIMIT,
				code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr)
					.unwrap()
					.get_alive()
					.unwrap()
					.rent_allowance,
				1_000
			);
			assert_eq!(
				Balances::free_balance(&addr),
				50 + subsistence_threshold,
			);

			// Transfer funds
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				call::transfer(&BOB),
			));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr)
					.unwrap()
					.get_alive()
					.unwrap()
					.rent_allowance,
				1_000
			);
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);

			// Advance blocks
			initialize_block(10);

			// Trigger rent through call
			assert!(trigger_call(addr.clone()));
			assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(ContractInfo::Tombstone(_)));
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);

			// Advance blocks
			initialize_block(20);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_matches!(ContractInfoOf::<Test>::get(&addr), Some(ContractInfo::Tombstone(_)));
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);
		});
}

#[test]
fn call_removed_contract() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	// Balance reached and superior to subsistence threshold
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm.clone()));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100,
				GAS_LIMIT, code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(1_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Calling contract should succeed.
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Advance blocks
			initialize_block(10);

			// Calling contract should deny access because rent cannot be paid.
			assert_err_ignore_postinfo!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null()),
				Error::<Test>::NotCallable
			);
			// No event is generated because the contract is not actually removed.
			assert_eq!(System::events(), vec![]);

			// Subsequent contract calls should also fail.
			assert_err_ignore_postinfo!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null()),
				Error::<Test>::NotCallable
			);

			// A snitch can now remove the contract
			assert_ok!(Contracts::claim_surcharge(Origin::none(), addr.clone(), Some(ALICE)));
			assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_tombstone().is_some());
		})
}

#[test]
fn default_rent_allowance_on_instantiate() {
	let (wasm, code_hash) = compile_module::<Test>("check_default_rent_allowance").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check creation
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, <BalanceOf<Test>>::max_value());

			// Advance blocks
			initialize_block(5);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check contract is still alive
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive();
			assert!(bob_contract.is_some())
		});
}

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
	let (set_rent_wasm, set_rent_code_hash) = compile_module::<Test>("set_rent").unwrap();
	let (restoration_wasm, restoration_code_hash) = compile_module::<Test>("restoration").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), restoration_wasm));
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), set_rent_wasm));

			// If you ever need to update the wasm source this test will fail
			// and will show you the actual hash.
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::system(frame_system::RawEvent::NewAccount(ALICE)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::balances(pallet_balances::RawEvent::Endowed(ALICE, 1_000_000)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::CodeStored(restoration_code_hash.into())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::CodeStored(set_rent_code_hash.into())),
					topics: vec![],
				},
			]);

			// Create an account with address `BOB` with code `CODE_SET_RENT`.
			// The input parameter sets the rent allowance to 0.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				set_rent_code_hash.into(),
				<Test as pallet_balances::Config>::Balance::from(0u32).encode(),
				vec![],
			));
			let addr_bob = Contracts::contract_address(&ALICE, &set_rent_code_hash, &[]);

			// Check if `BOB` was created successfully and that the rent allowance is
			// set to 0.
			let bob_contract = ContractInfoOf::<Test>::get(&addr_bob).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, 0);

			if test_different_storage {
				assert_ok!(Contracts::call(
					Origin::signed(ALICE),
					addr_bob.clone(), 0, GAS_LIMIT,
					call::set_storage_4_byte())
				);
			}

			// Advance 4 blocks, to the 5th.
			initialize_block(5);

			// Call `BOB`, which makes it pay rent. Since the rent allowance is set to 0
			// we expect that it is no longer callable but keeps existing until someone
			// calls `claim_surcharge`.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE), addr_bob.clone(), 0, GAS_LIMIT, call::null()
				),
				Error::<Test>::NotCallable
			);
			assert!(System::events().is_empty());
			assert!(ContractInfoOf::<Test>::get(&addr_bob).unwrap().get_alive().is_some());
			assert_ok!(Contracts::claim_surcharge(Origin::none(), addr_bob.clone(), Some(ALICE)));
			assert!(ContractInfoOf::<Test>::get(&addr_bob).unwrap().get_tombstone().is_some());
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(
						RawEvent::Evicted(addr_bob.clone(), true)
					),
					topics: vec![],
				},
			]);

			// Create another account with the address `DJANGO` with `CODE_RESTORATION`.
			//
			// Note that we can't use `ALICE` for creating `DJANGO` so we create yet another
			// account `CHARLIE` and create `DJANGO` with it.
			let _ = Balances::deposit_creating(&CHARLIE, 1_000_000);
			assert_ok!(Contracts::instantiate(
				Origin::signed(CHARLIE),
				30_000,
				GAS_LIMIT,
				restoration_code_hash.into(),
				vec![],
				vec![],
			));
			let addr_django = Contracts::contract_address(&CHARLIE, &restoration_code_hash, &[]);

			// Before performing a call to `DJANGO` save its original trie id.
			let django_trie_id = ContractInfoOf::<Test>::get(&addr_django).unwrap()
				.get_alive().unwrap().trie_id;

			// The trie is regarded as 'dirty' when it was written to in the current block.
			if !test_restore_to_with_dirty_storage {
				// Advance 1 block, to the 6th.
				initialize_block(6);
			}

			// Perform a call to `DJANGO`. This should either perform restoration successfully or
			// fail depending on the test parameters.
			let perform_the_restoration = || {
				Contracts::call(
					Origin::signed(ALICE),
					addr_django.clone(),
					0,
					GAS_LIMIT,
					set_rent_code_hash
						.as_ref()
						.iter()
						.chain(AsRef::<[u8]>::as_ref(&addr_bob))
						.cloned()
						.collect(),
				)
			};

			// The key that is used in the restorer contract but is not in the target contract.
			// Is supplied as delta to the restoration. We need it to check whether the key
			// is properly removed on success but still there on failure.
			let delta_key = {
				let mut key = [0u8; 32];
				key[0] = 1;
				key
			};

			if test_different_storage || test_restore_to_with_dirty_storage {
				// Parametrization of the test imply restoration failure. Check that `DJANGO` aka
				// restoration contract is still in place and also that `BOB` doesn't exist.
				let result = perform_the_restoration();
				assert!(ContractInfoOf::<Test>::get(&addr_bob).unwrap().get_tombstone().is_some());
				let django_contract = ContractInfoOf::<Test>::get(&addr_django).unwrap()
					.get_alive().unwrap();
				assert_eq!(django_contract.storage_size, 8);
				assert_eq!(django_contract.trie_id, django_trie_id);
				assert_eq!(django_contract.deduct_block, System::block_number());
				assert_eq!(
					Storage::<Test>::read(&django_trie_id, &delta_key),
					Some(vec![40, 0, 0, 0]),
				);
				match (test_different_storage, test_restore_to_with_dirty_storage) {
					(true, false) => {
						assert_err_ignore_postinfo!(
							result, Error::<Test>::InvalidTombstone,
						);
						assert_eq!(System::events(), vec![]);
					}
					(_, true) => {
						assert_err_ignore_postinfo!(
							result, Error::<Test>::InvalidContractOrigin,
						);
						pretty_assertions::assert_eq!(System::events(), vec![
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::contracts(RawEvent::Evicted(addr_bob, true)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::system(frame_system::RawEvent::NewAccount(CHARLIE)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::balances(pallet_balances::RawEvent::Endowed(CHARLIE, 1_000_000)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::system(frame_system::RawEvent::NewAccount(addr_django.clone())),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::balances(pallet_balances::RawEvent::Endowed(addr_django.clone(), 30_000)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::balances(
									pallet_balances::RawEvent::Transfer(CHARLIE, addr_django.clone(), 30_000)
								),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: MetaEvent::contracts(RawEvent::Instantiated(CHARLIE, addr_django.clone())),
								topics: vec![],
							},
						]);
					}
					_ => unreachable!(),
				}
			} else {
				assert_ok!(perform_the_restoration());

				// Here we expect that the restoration is succeeded. Check that the restoration
				// contract `DJANGO` ceased to exist and that `BOB` returned back.
				let bob_contract = ContractInfoOf::<Test>::get(&addr_bob).unwrap()
					.get_alive().unwrap();
				assert_eq!(bob_contract.rent_allowance, 50);
				assert_eq!(bob_contract.storage_size, 4);
				assert_eq!(bob_contract.trie_id, django_trie_id);
				assert_eq!(bob_contract.deduct_block, System::block_number());
				assert!(ContractInfoOf::<Test>::get(&addr_django).is_none());
				assert_matches!(Storage::<Test>::read(&django_trie_id, &delta_key), None);
				assert_eq!(System::events(), vec![
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::system(system::RawEvent::KilledAccount(addr_django.clone())),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::contracts(
							RawEvent::Restored(addr_django, addr_bob, bob_contract.code_hash, 50)
						),
						topics: vec![],
					},
				]);
			}
		});
}

#[test]
fn storage_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>("storage_size").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check creation
			let bob_contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(bob_contract.rent_allowance, <BalanceOf<Test>>::max_value());

			// Call contract with allowed storage value.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT * 2, // we are copying a huge buffer
				<Test as Config>::MaxValueSize::get().encode(),
			));

			// Call contract with too large a storage value.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE),
					addr,
					0,
					GAS_LIMIT,
					(<Test as Config>::MaxValueSize::get() + 1).encode(),
				),
				Error::<Test>::ValueTooLarge,
			);
		});
}

#[test]
fn deploy_and_call_other_contract() {
	let (callee_wasm, callee_code_hash) = compile_module::<Test>("return_with_data").unwrap();
	let (caller_wasm, caller_code_hash) = compile_module::<Test>("caller_contract").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), callee_wasm));
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), caller_wasm));

			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				caller_code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &caller_code_hash, &[]);

			// Call BOB contract, which attempts to instantiate and call the callee contract and
			// makes various assertions on the results from those calls.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr,
				0,
				GAS_LIMIT,
				callee_code_hash.as_ref().to_vec(),
			));
		});
}

#[test]
fn cannot_self_destruct_through_draning() {
	let (wasm, code_hash) = compile_module::<Test>("drain").unwrap();
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check that the BOB contract has been instantiated.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr),
				Some(ContractInfo::Alive(_))
			);

			// Call BOB which makes it send all funds to the zero address
			// The contract code asserts that the correct error value is returned.
			assert_ok!(
				Contracts::call(
					Origin::signed(ALICE),
					addr,
					0,
					GAS_LIMIT,
					vec![],
				)
			);
		});
}

#[test]
fn cannot_self_destruct_while_live() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check that the BOB contract has been instantiated.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr),
				Some(ContractInfo::Alive(_))
			);

			// Call BOB with input data, forcing it make a recursive call to itself to
			// self-destruct, resulting in a trap.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE),
					addr.clone(),
					0,
					GAS_LIMIT,
					vec![0],
				),
				Error::<Test>::ContractTrapped,
			);

			// Check that BOB is still alive.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr),
				Some(ContractInfo::Alive(_))
			);
		});
}

#[test]
fn self_destruct_works() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check that the BOB contract has been instantiated.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr),
				Some(ContractInfo::Alive(_))
			);

			// Call BOB without input data which triggers termination.
			assert_matches!(
				Contracts::call(
					Origin::signed(ALICE),
					addr.clone(),
					0,
					GAS_LIMIT,
					vec![],
				),
				Ok(_)
			);

			// Check that account is gone
			assert!(ContractInfoOf::<Test>::get(&addr).is_none());

			// check that the beneficiary (django) got remaining balance
			assert_eq!(Balances::free_balance(DJANGO), 100_000);
		});
}

// This tests that one contract cannot prevent another from self-destructing by sending it
// additional funds after it has been drained.
#[test]
fn destroy_contract_and_transfer_funds() {
	let (callee_wasm, callee_code_hash) = compile_module::<Test>("self_destruct").unwrap();
	let (caller_wasm, caller_code_hash) = compile_module::<Test>("destroy_and_transfer").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), callee_wasm));
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), caller_wasm));

			// This deploys the BOB contract, which in turn deploys the CHARLIE contract during
			// construction.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				200_000,
				GAS_LIMIT,
				caller_code_hash.into(),
				callee_code_hash.as_ref().to_vec(),
				vec![],
			));
			let addr_bob = Contracts::contract_address(&ALICE, &caller_code_hash, &[]);
			let addr_charlie = Contracts::contract_address(
				&addr_bob, &callee_code_hash, &[0x47, 0x11]
			);

			// Check that the CHARLIE contract has been instantiated.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr_charlie),
				Some(ContractInfo::Alive(_))
			);

			// Call BOB, which calls CHARLIE, forcing CHARLIE to self-destruct.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr_bob,
				0,
				GAS_LIMIT,
				addr_charlie.encode(),
			));

			// Check that CHARLIE has moved on to the great beyond (ie. died).
			assert!(ContractInfoOf::<Test>::get(&addr_charlie).is_none());
		});
}

#[test]
fn cannot_self_destruct_in_constructor() {
	let (wasm, code_hash) = compile_module::<Test>("self_destructing_constructor").unwrap();
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Fail to instantiate the BOB because the contructor calls seal_terminate.
			assert_err_ignore_postinfo!(
				Contracts::instantiate(
					Origin::signed(ALICE),
					100_000,
					GAS_LIMIT,
					code_hash.into(),
					vec![],
					vec![],
				),
				Error::<Test>::NewContractNotFunded,
			);
		});
}

#[test]
fn crypto_hashes() {
	let (wasm, code_hash) = compile_module::<Test>("crypto_hashes").unwrap();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

			// Instantiate the CRYPTO_HASHES contract.
			assert_ok!(Contracts::instantiate(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				code_hash.into(),
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
				let result = <Module<Test>>::bare_call(
					ALICE,
					addr.clone(),
					0,
					GAS_LIMIT,
					params,
				).exec_result.unwrap();
				assert!(result.is_success());
				let expected = hash_fn(input.as_ref());
				assert_eq!(&result.data[..*expected_size], &*expected);
			}
		})
}

#[test]
fn transfer_return_code() {
	let (wasm, code_hash) = compile_module::<Test>("transfer_return_code").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), wasm));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				code_hash.into(),
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::BelowSubsistenceThreshold);

		// Contract has enough total balance in order to not go below the subsistence
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails but with another return code.
		Balances::make_free_balance_be(&addr, subsistence + 100);
		Balances::reserve(&addr, subsistence + 100).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			vec![],
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);
	});
}

#[test]
fn call_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("call_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		let _ = Balances::deposit_creating(&CHARLIE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), caller_code));
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), callee_code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				caller_hash.into(),
				vec![0],
				vec![],
			),
		);
		let addr_bob = Contracts::contract_address(&ALICE, &caller_hash, &[]);

		// Contract calls into Django which is no valid contract
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&DJANGO).to_vec(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::NotCallable);

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(CHARLIE),
				subsistence,
				GAS_LIMIT,
				callee_hash.into(),
				vec![0],
				vec![],
			),
		);
		let addr_django = Contracts::contract_address(&CHARLIE, &callee_hash, &[]);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&0u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::BelowSubsistenceThreshold);

		// Contract has enough total balance in order to not go below the subsistence
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails but with another return code.
		Balances::make_free_balance_be(&addr_bob, subsistence + 100);
		Balances::reserve(&addr_bob, subsistence + 100).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&0u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but callee reverts because "1" is passed.
		Balances::make_free_balance_be(&addr_bob, subsistence + 1000);
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&1u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob,
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&2u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);

	});
}

#[test]
fn instantiate_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("instantiate_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		let _ = Balances::deposit_creating(&CHARLIE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), caller_code));
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), callee_code));
		let callee_hash = callee_hash.as_ref().to_vec();

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				caller_hash.into(),
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &caller_hash, &[]);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![0; 33],
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::BelowSubsistenceThreshold);

		// Contract has enough total balance in order to not go below the subsistence
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails but with another return code.
		Balances::make_free_balance_be(&addr, subsistence + 100);
		Balances::reserve(&addr, subsistence + 100).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![0; 33],
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but the passed code hash is invalid
		Balances::make_free_balance_be(&addr, subsistence + 1000);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![0; 33],
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CodeNotFound);

		// Contract has enough balance but callee reverts because "1" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			callee_hash.iter().chain(&1u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			callee_hash.iter().chain(&2u32.to_le_bytes()).cloned().collect(),
		).exec_result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);

	});
}

#[test]
fn disabled_chain_extension_wont_deploy() {
	let (code, _hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		TestExtension::disable();
		assert_eq!(
			Contracts::put_code(Origin::signed(ALICE), code),
			Err("module uses chain extensions but chain extensions are disabled".into()),
		);
	});
}

#[test]
fn disabled_chain_extension_errors_on_call() {
	let (code, hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));
		TestExtension::disable();
		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				vec![],
			),
			Error::<Test>::NoChainExtension,
		);
	});
}

#[test]
fn chain_extension_works() {
	let (code, hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));
		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// The contract takes a up to 2 byte buffer where the first byte passed is used as
		// as func_id to the chain extension which behaves differently based on the
		// func_id.

		// 0 = read input buffer and pass it through as output
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![0, 99],
		);
		let gas_consumed = result.gas_consumed;
		assert_eq!(TestExtension::last_seen_buffer(), vec![0, 99]);
		assert_eq!(result.exec_result.unwrap().data, vec![0, 99]);

		// 1 = treat inputs as integer primitives and store the supplied integers
		Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![1],
		).exec_result.unwrap();
		// those values passed in the fixture
		assert_eq!(TestExtension::last_seen_inputs(), (4, 1, 16, 12));

		// 2 = charge some extra weight (amount supplied in second byte)
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![2, 42],
		);
		assert_ok!(result.exec_result);
		assert_eq!(result.gas_consumed, gas_consumed + 42);

		// 3 = diverging chain extension call that sets flags to 0x1 and returns a fixed buffer
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![3],
		).exec_result.unwrap();
		assert_eq!(result.flags, ReturnFlags::REVERT);
		assert_eq!(result.data, vec![42, 99]);
	});
}

#[test]
fn lazy_removal_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let trie = &info.child_trie_info();

		// Put value into the contracts child trie
		child::put(trie, &[99], &42);

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
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
	let vals: Vec<_> = (0..max_keys + extra_keys).map(|i| {
		(blake2_256(&i.encode()), (i as u32), (i as u32).encode())
	})
	.collect();

	let mut ext = ExtBuilder::default().existential_deposit(50).build();

	let trie = ext.execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let trie = &info.child_trie_info();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				&addr,
				&info.trie_id,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), Some(val.1));
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
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let trie = &info.child_trie_info();
		let max_keys = 30;

		// Create some storage items for the contract.
		let vals: Vec<_> = (0..max_keys).map(|i| {
			(blake2_256(&i.encode()), (i as u32), (i as u32).encode())
		})
		.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				&addr,
				&info.trie_id,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), Some(val.1));
		}

		// Fill up the block which should prevent the lazy storage removal from running.
		System::register_extra_weight_unchecked(
			<Test as system::Config>::BlockWeights::get().max_block,
			DispatchClass::Mandatory,
		);

		// Run the lazy removal without any limit so that all keys would be removed if there
		// had been some weight left in the block.
		let weight_used = Contracts::on_initialize(Weight::max_value());
		let base = <<Test as crate::Config>::WeightInfo as crate::WeightInfo>::on_initialize();
		assert_eq!(weight_used, base);

		// All the keys are still in place
		for val in &vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), Some(val.1));
		}

		// Run the lazy removal directly which disregards the block limits
		Storage::<Test>::process_deletion_queue_batch(Weight::max_value());

		// Now the keys should be gone
		for val in &vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), None);
		}
	});
}


#[test]
fn lazy_removal_does_not_use_all_weight() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let trie = &info.child_trie_info();
		let weight_limit = 5_000_000_000;
		let (weight_per_key, max_keys) = Storage::<Test>::deletion_budget(1, weight_limit);

		// We create a contract with one less storage item than we can remove within the limit
		let vals: Vec<_> = (0..max_keys - 1).map(|i| {
			(blake2_256(&i.encode()), (i as u32), (i as u32).encode())
		})
		.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				&addr,
				&info.trie_id,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}

		// Terminate the contract
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
		));

		// Contract info should be gone
		assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), Some(val.1));
		}

		// Run the lazy removal
		let weight_used = Storage::<Test>::process_deletion_queue_batch(weight_limit);

		// We have one less key in our trie than our weight limit suffices for
		assert_eq!(weight_used, weight_limit - weight_per_key);

		// All the keys are removed
		for val in vals {
			assert_eq!(child::get::<u32>(trie, &blake2_256(&val.0)), None);
		}
	});
}

#[test]
fn deletion_queue_full() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = ConfigCache::<Test>::subsistence_threshold_uncached();
		let _ = Balances::deposit_creating(&ALICE, 10 * subsistence);
		assert_ok!(Contracts::put_code(Origin::signed(ALICE), code));

		assert_ok!(
			Contracts::instantiate(
				Origin::signed(ALICE),
				subsistence,
				GAS_LIMIT,
				hash.into(),
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// fill the deletion queue up until its limit
		Storage::<Test>::fill_queue_with_dummies();

		// Terminate the contract should fail
		assert_err_ignore_postinfo!(
			Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				vec![],
			),
			Error::<Test>::DeletionQueueFull,
		);

		// Contract should be alive because removal failed
		<ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();

		// make the contract ripe for eviction
		initialize_block(5);

		// eviction should fail for the same reason as termination
		assert_err!(
			Contracts::claim_surcharge(Origin::none(), addr.clone(), Some(ALICE)),
			Error::<Test>::DeletionQueueFull,
		);

		// Contract should be alive because removal failed
		<ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
	});
}
