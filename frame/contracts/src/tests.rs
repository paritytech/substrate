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
	BalanceOf, ContractInfo, ContractInfoOf, Pallet,
	Config, Schedule,
	Error, storage::Storage,
	chain_extension::{
		Result as ExtensionResult, Environment, ChainExtension, Ext, SysConfig, RetVal,
		UncheckedFrom, InitState, ReturnFlags,
	},
	exec::{AccountIdOf, Executable, Frame}, wasm::PrefabWasmModule,
	weights::WeightInfo,
	wasm::ReturnCode as RuntimeReturnCode,
	storage::RawAliveContractInfo,
};
use assert_matches::assert_matches;
use codec::Encode;
use sp_core::Bytes;
use sp_runtime::{
	traits::{BlakeTwo256, Hash, IdentityLookup, Convert},
	testing::{Header, H256},
	AccountId32, Perbill,
};
use sp_io::hashing::blake2_256;
use frame_support::{
	assert_ok, assert_err, assert_err_ignore_postinfo,
	parameter_types, assert_storage_noop,
	traits::{Currency, ReservableCurrency, OnInitialize},
	weights::{Weight, PostDispatchInfo, DispatchClass, constants::WEIGHT_PER_SECOND},
	dispatch::DispatchErrorWithPostInfo,
	storage::child,
};
use frame_system::{self as system, EventRecord, Phase};
use pretty_assertions::assert_eq;

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
		Randomness: pallet_randomness_collective_flip::{Pallet, Call, Storage},
		Contracts: pallet_contracts::{Pallet, Call, Storage, Event<T>},
	}
);

#[macro_use]
pub mod test_utils {
	use super::{Test, Balances, System};
	use crate::{
		ContractInfoOf, CodeHash,
		storage::{Storage, ContractInfo},
		exec::{StorageKey, AccountIdOf},
		Pallet as Contracts,
		TrieId, AccountCounter,
	};
	use frame_support::traits::Currency;

	pub fn set_storage(addr: &AccountIdOf<Test>, key: &StorageKey, value: Option<Vec<u8>>) {
		let mut contract_info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let block_number = System::block_number();
		Storage::<Test>::write(block_number, &mut contract_info, key, value).unwrap();
	}
	pub fn get_storage(addr: &AccountIdOf<Test>, key: &StorageKey) -> Option<Vec<u8>> {
		let contract_info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		Storage::<Test>::read(&contract_info.trie_id, key)
	}
	pub fn generate_trie_id(address: &AccountIdOf<Test>) -> TrieId {
		let seed = <AccountCounter<Test>>::mutate(|counter| {
			*counter += 1;
			*counter
		});
		Storage::<Test>::generate_trie_id(address, seed)
	}
	pub fn place_contract(address: &AccountIdOf<Test>, code_hash: CodeHash<Test>) {
		let trie_id = generate_trie_id(address);
		set_balance(address, Contracts::<Test>::subsistence_threshold() * 10);
		let contract = Storage::<Test>::new_contract(&address, trie_id, code_hash).unwrap();
		<ContractInfoOf<Test>>::insert(address, ContractInfo::Alive(contract));
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
	macro_rules! assert_refcount {
		( $code_hash:expr , $should:expr $(,)? ) => {{
			let is = crate::CodeStorage::<Test>::get($code_hash)
				.map(|m| m.refcount())
				.unwrap_or(0);
			assert_eq!(is, $should);
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
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type Balance = u64;
	type Event = Event;
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
	pub const DepositPerContract: u64 = 8 * DepositPerStorageByte::get();
	pub const DepositPerStorageByte: u64 = 10_000;
	pub const DepositPerStorageItem: u64 = 10_000;
	pub RentFraction: Perbill = Perbill::from_rational(4u32, 10_000u32);
	pub const SurchargeReward: u64 = 500_000;
	pub const MaxValueSize: u32 = 16_384;
	pub const DeletionQueueDepth: u32 = 1024;
	pub const DeletionWeightLimit: Weight = 500_000_000_000;
	pub const MaxCodeSize: u32 = 2 * 1024;
	pub MySchedule: Schedule<Test> = <Schedule<Test>>::default();
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
	type Event = Event;
	type RentPayment = ();
	type SignedClaimHandicap = SignedClaimHandicap;
	type TombstoneDeposit = TombstoneDeposit;
	type DepositPerContract = DepositPerContract;
	type DepositPerStorageByte = DepositPerStorageByte;
	type DepositPerStorageItem = DepositPerStorageItem;
	type RentFraction = RentFraction;
	type SurchargeReward = SurchargeReward;
	type CallStack = [Frame<Self>; 31];
	type WeightPrice = Self;
	type WeightInfo = ();
	type ChainExtension = TestExtension;
	type DeletionQueueDepth = DeletionQueueDepth;
	type DeletionWeightLimit = DeletionWeightLimit;
	type Schedule = MySchedule;
}

pub const ALICE: AccountId32 = AccountId32::new([1u8; 32]);
pub const BOB: AccountId32 = AccountId32::new([2u8; 32]);
pub const CHARLIE: AccountId32 = AccountId32::new([3u8; 32]);
pub const DJANGO: AccountId32 = AccountId32::new([4u8; 32]);

const GAS_LIMIT: Weight = 10_000_000_000;

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
// Then we check that at least the base costs where charged (no runtime gas costs.)
#[test]
fn calling_plain_account_fails() {
	ExtBuilder::default().build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 100_000_000);
		let base_cost = <<Test as Config>::WeightInfo as WeightInfo>::call(0);

		assert_eq!(
			Contracts::call(Origin::signed(ALICE), BOB, 0, GAS_LIMIT, Vec::new()),
			Err(
				DispatchErrorWithPostInfo {
					error: Error::<Test>::NotCallable.into(),
					post_info: PostDispatchInfo {
						actual_weight: Some(base_cost),
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
		let trie_id1 = test_utils::generate_trie_id(&ALICE);
		let trie_id2 = test_utils::generate_trie_id(&BOB);
		let key1 = &[1; 32];
		let key2 = &[2; 32];

		// Set up two accounts with free balance above the existential threshold.
		{
			let alice_contract_info = ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id1.clone(),
				storage_size: 0,
				pair_count: 0,
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(1),
				rent_allowance: 40,
				rent_payed: 0,
				last_write: None,
				_reserved: None,
			});
			let _ = Balances::deposit_creating(&ALICE, 110);
			ContractInfoOf::<Test>::insert(ALICE, &alice_contract_info);
			set_storage(&ALICE, &key1, Some(b"1".to_vec()));
			set_storage(&ALICE, &key2, Some(b"2".to_vec()));

			let bob_contract_info = ContractInfo::Alive(RawAliveContractInfo {
				trie_id: trie_id2.clone(),
				storage_size: 0,
				pair_count: 0,
				deduct_block: System::block_number(),
				code_hash: H256::repeat_byte(2),
				rent_allowance: 40,
				rent_payed: 0,
				last_write: None,
				_reserved: None,
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
			let subsistence = Pallet::<Test>::subsistence_threshold();

			// Check at the end to get hash on error easily
			let creation = Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			);
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::frame_system(frame_system::Event::NewAccount(ALICE.clone())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Endowed(ALICE, 1_000_000)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::frame_system(frame_system::Event::NewAccount(addr.clone())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Endowed(addr.clone(), subsistence * 100)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Transfer(ALICE, addr.clone(), subsistence * 100)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(crate::Event::CodeStored(code_hash.into())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(
						crate::Event::ContractEmitted(addr.clone(), vec![1, 2, 3, 4])
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(crate::Event::Instantiated(ALICE, addr.clone())),
					topics: vec![],
				},
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
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
				<Test as Config>::Schedule::get().limits.payload_len.encode(),
			));

			// Call contract with too large a storage value.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE),
					addr,
					0,
					GAS_LIMIT,
					(<Test as Config>::Schedule::get().limits.payload_len + 1).encode(),
				),
				Error::<Test>::ValueTooLarge,
			);
		});
}

#[test]
fn run_out_of_gas() {
	let (wasm, code_hash) = compile_module::<Test>("run_out_of_gas").unwrap();
	let subsistence = Pallet::<Test>::subsistence_threshold();

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);

			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100 * subsistence,
				GAS_LIMIT,
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
	#[allow(dead_code)]
	pub fn transfer(to: &AccountIdOf<Test>) -> Vec<u8> {
		2u32.to_le_bytes().iter().chain(AsRef::<[u8]>::as_ref(to)).cloned().collect()
	}
	pub fn null() -> Vec<u8> { 3u32.to_le_bytes().to_vec() }
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				// rent_allowance
				<Test as pallet_balances::Config>::Balance::from(10_000u32).encode(),
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
				bob_contract.pair_count,
				1,
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
				bob_contract.pair_count,
				2,
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
				bob_contract.pair_count,
				1,
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
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
				bob_contract.pair_count,
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
	let endowment: BalanceOf<Test> = 100_000;
	let allowance: BalanceOf<Test> = 70_000;

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				endowment,
				GAS_LIMIT,
				wasm,
				allowance.encode(),
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			let code_len: BalanceOf<Test> =
				PrefabWasmModule::<Test>::from_storage_noinstr(contract.code_hash)
					.unwrap()
					.occupied_storage()
					.into();

			// The instantiation deducted the rent for one block immediately
			let rent0 = <Test as Config>::RentFraction::get()
				// (base_deposit(8) + bytes in storage(4) + size of code) * byte_price
				// + 1 storage item (10_000) - free_balance
				.mul_ceil((8 + 4 + code_len) * 10_000 + 10_000 - endowment)
				// blocks to rent
				* 1;
			assert!(rent0 > 0);
			assert_eq!(contract.rent_allowance, allowance - rent0);
			assert_eq!(contract.deduct_block, 1);
			assert_eq!(Balances::free_balance(&addr), endowment - rent0);

			// Advance 4 blocks
			initialize_block(5);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check result
			let rent = <Test as Config>::RentFraction::get()
				.mul_ceil((8 + 4 + code_len) * 10_000 + 10_000 - (endowment - rent0))
				* 4;
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(contract.rent_allowance, allowance - rent0 - rent);
			assert_eq!(contract.deduct_block, 5);
			assert_eq!(Balances::free_balance(&addr), endowment - rent0 - rent);

			// Advance 2 blocks more
			initialize_block(7);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check result
			let rent_2 = <Test as Config>::RentFraction::get()
				.mul_ceil((8 + 4 + code_len) * 10_000 + 10_000 - (endowment - rent0 - rent))
				* 2;
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(contract.rent_allowance, allowance - rent0 - rent - rent_2);
			assert_eq!(contract.deduct_block, 7);
			assert_eq!(Balances::free_balance(&addr), endowment - rent0 - rent - rent_2);

			// Second call on same block should have no effect on rent
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			assert_eq!(contract.rent_allowance, allowance - rent0 - rent - rent_2);
			assert_eq!(contract.deduct_block, 7);
			assert_eq!(Balances::free_balance(&addr), endowment - rent0 - rent - rent_2)
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
	claim_surcharge(8, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(7, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(6, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), true);
	claim_surcharge(5, |addr| Contracts::claim_surcharge(Origin::none(), addr, Some(ALICE)).is_ok(), false);

	// Test surcharge malus for signed
	claim_surcharge(8, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), true);
	claim_surcharge(7, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
	claim_surcharge(6, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
	claim_surcharge(5, |addr| Contracts::claim_surcharge(Origin::signed(ALICE), addr, None).is_ok(), false);
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				wasm,
				<Test as pallet_balances::Config>::Balance::from(30_000u32).encode(), // rent allowance
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				70_000,
				GAS_LIMIT,
				wasm.clone(),
				<Test as pallet_balances::Config>::Balance::from(100_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let allowance = ContractInfoOf::<Test>::get(&addr)
				.unwrap().get_alive().unwrap().rent_allowance;
			let balance = Balances::free_balance(&addr);

			let subsistence_threshold = Pallet::<Test>::subsistence_threshold();

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap().rent_allowance,
				allowance,
			);
			assert_eq!(Balances::free_balance(&addr), balance);

			// Advance blocks
			initialize_block(27);

			// Trigger rent through call (should remove the contract)
			assert!(trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr).unwrap().get_tombstone().is_some());
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);

			// Advance blocks
			initialize_block(30);

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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				wasm.clone(),
				<Test as pallet_balances::Config>::Balance::from(70_000u32).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let allowance = ContractInfoOf::<Test>::get(&addr)
				.unwrap().get_alive().unwrap().rent_allowance;
			let balance = Balances::free_balance(&addr);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr)
					.unwrap()
					.get_alive()
					.unwrap()
					.rent_allowance,
				allowance,
			);
			assert_eq!(Balances::free_balance(&addr), balance);

			// Advance blocks
			initialize_block(27);

			// Trigger rent through call
			assert!(trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_tombstone()
				.is_some());
			// Balance should be initial balance - initial rent_allowance
			assert_eq!(Balances::free_balance(&addr), 30_000);

			// Advance blocks
			initialize_block(20);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert!(ContractInfoOf::<Test>::get(&addr)
				.unwrap()
				.get_tombstone()
				.is_some());
			assert_eq!(Balances::free_balance(&addr), 30_000);
		});

	// Balance reached and inferior to subsistence threshold
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			// Create
			let subsistence_threshold = Pallet::<Test>::subsistence_threshold();
			let _ = Balances::deposit_creating(&ALICE, subsistence_threshold * 1000);
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence_threshold * 100,
				GAS_LIMIT,
				wasm,
				(subsistence_threshold * 100).encode(), // rent allowance
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let allowance = ContractInfoOf::<Test>::get(&addr)
				.unwrap().get_alive().unwrap().rent_allowance;
			let balance = Balances::free_balance(&addr);

			// Trigger rent must have no effect
			assert!(!trigger_call(addr.clone()));
			assert_eq!(
				ContractInfoOf::<Test>::get(&addr)
					.unwrap()
					.get_alive()
					.unwrap()
					.rent_allowance,
				allowance,
			);
			assert_eq!(
				Balances::free_balance(&addr),
				balance,
			);

			// Make contract have exactly the subsistence threshold
			Balances::make_free_balance_be(&addr, subsistence_threshold);
			assert_eq!(Balances::free_balance(&addr), subsistence_threshold);

			// Advance blocks (should remove as balance is exactly subsistence)
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				// rent allowance
				<Test as pallet_balances::Config>::Balance::from(10_000u32).encode(),
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Calling contract should succeed.
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Advance blocks
			initialize_block(27);

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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();
			let code_len: BalanceOf<Test> =
			PrefabWasmModule::<Test>::from_storage_noinstr(contract.code_hash)
				.unwrap()
				.occupied_storage()
				.into();

			// The instantiation deducted the rent for one block immediately
			let first_rent = <Test as Config>::RentFraction::get()
				// (base_deposit(8) + code_len) * byte_price - free_balance
				.mul_ceil((8 + code_len) * 10_000 - 30_000)
				// blocks to rent
				* 1;
			assert_eq!(contract.rent_allowance, <BalanceOf<Test>>::max_value() - first_rent);

			// Advance blocks
			initialize_block(5);

			// Trigger rent through call
			assert_ok!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null())
			);

			// Check contract is still alive
			let contract = ContractInfoOf::<Test>::get(&addr).unwrap().get_alive();
			assert!(contract.is_some())
		});
}

#[test]
fn restorations_dirty_storage_and_different_storage() {
	restoration(true, true, false);
}

#[test]
fn restorations_dirty_storage() {
	restoration(false, true, false);
}

#[test]
fn restoration_different_storage() {
	restoration(true, false, false);
}

#[test]
fn restoration_code_evicted() {
	restoration(false, false, true);
}

#[test]
fn restoration_success() {
	restoration(false, false, false);
}

fn restoration(
	test_different_storage: bool,
	test_restore_to_with_dirty_storage: bool,
	test_code_evicted: bool
) {
	let (set_rent_wasm, set_rent_code_hash) = compile_module::<Test>("set_rent").unwrap();
	let (restoration_wasm, restoration_code_hash) = compile_module::<Test>("restoration").unwrap();
	let allowance: <Test as pallet_balances::Config>::Balance = 10_000;

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);

			// Create an account with address `BOB` with code `CODE_SET_RENT`.
			// The input parameter sets the rent allowance to 0.
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				set_rent_wasm.clone(),
				allowance.encode(),
				vec![],
			));
			let addr_bob = Contracts::contract_address(&ALICE, &set_rent_code_hash, &[]);

			let mut events = vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::frame_system(frame_system::Event::NewAccount(ALICE)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Endowed(ALICE, 1_000_000)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::frame_system(frame_system::Event::NewAccount(addr_bob.clone())),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Endowed(addr_bob.clone(), 30_000)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Transfer(ALICE, addr_bob.clone(), 30_000)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(
						crate::Event::CodeStored(set_rent_code_hash.into())
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(
						crate::Event::Instantiated(ALICE, addr_bob.clone())
					),
					topics: vec![],
				},
			];

			// Create another contract from the same code in order to increment the codes
			// refcounter so that it stays on chain.
			if !test_code_evicted {
				assert_ok!(Contracts::instantiate_with_code(
					Origin::signed(ALICE),
					20_000,
					GAS_LIMIT,
					set_rent_wasm,
					allowance.encode(),
					vec![1],
				));
				assert_refcount!(set_rent_code_hash, 2);
				let addr_dummy = Contracts::contract_address(&ALICE, &set_rent_code_hash, &[1]);
				events.extend([
					EventRecord {
						phase: Phase::Initialization,
						event: Event::frame_system(frame_system::Event::NewAccount(addr_dummy.clone())),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: Event::pallet_balances(
							pallet_balances::Event::Endowed(addr_dummy.clone(), 20_000)
						),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: Event::pallet_balances(
							pallet_balances::Event::Transfer(ALICE, addr_dummy.clone(), 20_000)
						),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: Event::pallet_contracts(
							crate::Event::Instantiated(ALICE, addr_dummy.clone())
						),
						topics: vec![],
					},
				].iter().cloned());
			}

			assert_eq!(System::events(), events);

			// Check if `BOB` was created successfully and that the rent allowance is below what
			// we specified as the first rent was already collected.
			let bob_contract = ContractInfoOf::<Test>::get(&addr_bob).unwrap().get_alive().unwrap();
			assert!(bob_contract.rent_allowance < allowance);

			if test_different_storage {
				assert_ok!(Contracts::call(
					Origin::signed(ALICE),
					addr_bob.clone(), 0, GAS_LIMIT,
					call::set_storage_4_byte())
				);
			}

			// Advance blocks in order to make the contract run out of money for rent.
			initialize_block(27);

			// Call `BOB`, which makes it pay rent. Since the rent allowance is set to 20_000
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
			if test_code_evicted {
				assert_refcount!(set_rent_code_hash, 0);
			} else {
				assert_refcount!(set_rent_code_hash, 1);
			}

			// Create another account with the address `DJANGO` with `CODE_RESTORATION`.
			//
			// Note that we can't use `ALICE` for creating `DJANGO` so we create yet another
			// account `CHARLIE` and create `DJANGO` with it.
			let _ = Balances::deposit_creating(&CHARLIE, 1_000_000);
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(CHARLIE),
				30_000,
				GAS_LIMIT,
				restoration_wasm,
				vec![],
				vec![],
			));
			let addr_django = Contracts::contract_address(&CHARLIE, &restoration_code_hash, &[]);

			// Before performing a call to `DJANGO` save its original trie id.
			let django_trie_id = ContractInfoOf::<Test>::get(&addr_django).unwrap()
				.get_alive().unwrap().trie_id;

			// The trie is regarded as 'dirty' when it was written to in the current block.
			if !test_restore_to_with_dirty_storage {
				// Advance 1 block.
				initialize_block(28);
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

			if test_different_storage || test_restore_to_with_dirty_storage || test_code_evicted {
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
				match (
					test_different_storage,
					test_restore_to_with_dirty_storage,
					test_code_evicted
				) {
					(true, false, false) => {
						assert_err_ignore_postinfo!(
							result, Error::<Test>::InvalidTombstone,
						);
						assert_eq!(System::events(), vec![]);
					}
					(_, true, false) => {
						assert_err_ignore_postinfo!(
							result, Error::<Test>::InvalidContractOrigin,
						);
						assert_eq!(System::events(), vec![
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_contracts(crate::Event::Evicted(addr_bob)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::frame_system(frame_system::Event::NewAccount(CHARLIE)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_balances(pallet_balances::Event::Endowed(CHARLIE, 1_000_000)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::frame_system(frame_system::Event::NewAccount(addr_django.clone())),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_balances(pallet_balances::Event::Endowed(addr_django.clone(), 30_000)),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_balances(
									pallet_balances::Event::Transfer(CHARLIE, addr_django.clone(), 30_000)
								),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_contracts(
									crate::Event::CodeStored(restoration_code_hash)
								),
								topics: vec![],
							},
							EventRecord {
								phase: Phase::Initialization,
								event: Event::pallet_contracts(
									crate::Event::Instantiated(CHARLIE, addr_django.clone())
								),
								topics: vec![],
							},

						]);
					},
					(false, false, true) => {
						assert_err_ignore_postinfo!(
							result, Error::<Test>::CodeNotFound,
						);
						assert_refcount!(set_rent_code_hash, 0);
						assert_eq!(System::events(), vec![]);
					},
					_ => unreachable!(),
				}
			} else {
				assert_ok!(perform_the_restoration());
				assert_refcount!(set_rent_code_hash, 2);

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
						event: Event::pallet_contracts(crate::Event::CodeRemoved(restoration_code_hash)),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: Event::frame_system(system::Event::KilledAccount(addr_django.clone())),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: Event::pallet_contracts(
							crate::Event::Restored(
								addr_django, addr_bob, bob_contract.code_hash, 50
							)
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
			ContractInfoOf::<Test>::get(&addr).unwrap().get_alive().unwrap();

			// Call contract with allowed storage value.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT * 2, // we are copying a huge buffer
				<Test as Config>::Schedule::get().limits.payload_len.encode(),
			));

			// Call contract with too large a storage value.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE),
					addr,
					0,
					GAS_LIMIT,
					(<Test as Config>::Schedule::get().limits.payload_len + 1).encode(),
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				caller_wasm,
				vec![],
				vec![],
			));
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				callee_wasm,
				0u32.to_le_bytes().encode(),
				vec![42],
			));

			// Call BOB contract, which attempts to instantiate and call the callee contract and
			// makes various assertions on the results from those calls.
			assert_ok!(Contracts::call(
				Origin::signed(ALICE),
				Contracts::contract_address(&ALICE, &caller_code_hash, &[]),
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

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				wasm,
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

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				wasm,
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
			let _ = Balances::deposit_creating(&DJANGO, 1_000_000);

			// Instantiate the BOB contract.
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			));
			let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

			// Check that the BOB contract has been instantiated.
			assert_matches!(
				ContractInfoOf::<Test>::get(&addr),
				Some(ContractInfo::Alive(_))
			);

			// Drop all previous events
			initialize_block(2);

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

			pretty_assertions::assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::frame_system(
						frame_system::Event::KilledAccount(addr.clone())
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_balances(
						pallet_balances::Event::Transfer(addr.clone(), DJANGO, 93_086)
					),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(crate::Event::CodeRemoved(code_hash)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::pallet_contracts(
						crate::Event::Terminated(addr.clone(), DJANGO)
					),
					topics: vec![],
				},
			]);

			// Check that account is gone
			assert!(ContractInfoOf::<Test>::get(&addr).is_none());

			// check that the beneficiary (django) got remaining balance
			// some rent was deducted before termination
			assert_eq!(Balances::free_balance(DJANGO), 1_093_086);
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
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				200_000,
				GAS_LIMIT,
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
				caller_wasm,
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
	let (wasm, _) = compile_module::<Test>("self_destructing_constructor").unwrap();
	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);

			// Fail to instantiate the BOB because the contructor calls seal_terminate.
			assert_err_ignore_postinfo!(
				Contracts::instantiate_with_code(
					Origin::signed(ALICE),
					100_000,
					GAS_LIMIT,
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

	ExtBuilder::default()
		.existential_deposit(50)
		.build()
		.execute_with(|| {
			let _ = Balances::deposit_creating(&ALICE, 1_000_000);

			// Instantiate the CRYPTO_HASHES contract.
			assert_ok!(Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				100_000,
				GAS_LIMIT,
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
				let result = <Pallet<Test>>::bare_call(
					ALICE,
					addr.clone(),
					0,
					GAS_LIMIT,
					params,
					false,
				).result.unwrap();
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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		Balances::make_free_balance_be(&addr, subsistence);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
			false,
		).result.unwrap();
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
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);
	});
}

#[test]
fn call_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("call_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				caller_code,
				vec![0],
				vec![],
			),
		);
		let addr_bob = Contracts::contract_address(&ALICE, &caller_hash, &[]);
		Balances::make_free_balance_be(&addr_bob, subsistence);

		// Contract calls into Django which is no valid contract
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&DJANGO).to_vec(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::NotCallable);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(CHARLIE),
				subsistence * 100,
				GAS_LIMIT,
				callee_code,
				vec![0],
				vec![],
			),
		);
		let addr_django = Contracts::contract_address(&CHARLIE, &callee_hash, &[]);
		Balances::make_free_balance_be(&addr_django, subsistence);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&0u32.to_le_bytes()).cloned().collect(),
			false,
		).result.unwrap();
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
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but callee reverts because "1" is passed.
		Balances::make_free_balance_be(&addr_bob, subsistence + 1000);
		let result = Contracts::bare_call(
			ALICE,
			addr_bob.clone(),
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&1u32.to_le_bytes()).cloned().collect(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr_bob,
			0,
			GAS_LIMIT,
			AsRef::<[u8]>::as_ref(&addr_django).iter().chain(&2u32.to_le_bytes()).cloned().collect(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);

	});
}

#[test]
fn instantiate_return_code() {
	let (caller_code, caller_hash) = compile_module::<Test>("instantiate_return_code").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("ok_trap_revert").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * subsistence);
		let callee_hash = callee_hash.as_ref().to_vec();

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				callee_code,
				vec![],
				vec![],
			),
		);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				caller_code,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &caller_hash, &[]);

		// Contract has only the minimal balance so any transfer will return BelowSubsistence.
		Balances::make_free_balance_be(&addr, subsistence);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			callee_hash.clone(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::BelowSubsistenceThreshold);

		// Contract has enough total balance in order to not go below the subsistence
		// threshold when transfering the balance but this balance is reserved so
		// the transfer still fails but with another return code.
		Balances::make_free_balance_be(&addr, subsistence + 10_000);
		Balances::reserve(&addr, subsistence + 10_000).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			callee_hash.clone(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but the passed code hash is invalid
		Balances::make_free_balance_be(&addr, subsistence + 10_000);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![0; 33],
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CodeNotFound);

		// Contract has enough balance but callee reverts because "1" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			callee_hash.iter().chain(&1u32.to_le_bytes()).cloned().collect(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeReverted);

		// Contract has enough balance but callee traps because "2" is passed.
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			callee_hash.iter().chain(&2u32.to_le_bytes()).cloned().collect(),
			false,
		).result.unwrap();
		assert_return_code!(result, RuntimeReturnCode::CalleeTrapped);

	});
}

#[test]
fn disabled_chain_extension_wont_deploy() {
	let (code, _hash) = compile_module::<Test>("chain_extension").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);
		TestExtension::disable();
		assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				3 * subsistence,
				GAS_LIMIT,
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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);
		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		TestExtension::disable();
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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);
		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
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
			false,
		);
		let gas_consumed = result.gas_consumed;
		assert_eq!(TestExtension::last_seen_buffer(), vec![0, 99]);
		assert_eq!(result.result.unwrap().data, Bytes(vec![0, 99]));

		// 1 = treat inputs as integer primitives and store the supplied integers
		Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![1],
			false,
		).result.unwrap();
		// those values passed in the fixture
		assert_eq!(TestExtension::last_seen_inputs(), (4, 1, 16, 12));

		// 2 = charge some extra weight (amount supplied in second byte)
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![2, 42],
			false,
		);
		assert_ok!(result.result);
		assert_eq!(result.gas_consumed, gas_consumed + 42);

		// 3 = diverging chain extension call that sets flags to 0x1 and returns a fixed buffer
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![3],
			false,
		).result.unwrap();
		assert_eq!(result.flags, ReturnFlags::REVERT);
		assert_eq!(result.data, Bytes(vec![42, 99]));
	});
}

#[test]
fn lazy_removal_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let mut info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				System::block_number(),
				&mut info,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, ContractInfo::Alive(info.clone()));

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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let mut info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let max_keys = 30;

		// Create some storage items for the contract.
		let vals: Vec<_> = (0..max_keys).map(|i| {
			(blake2_256(&i.encode()), (i as u32), (i as u32).encode())
		})
		.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				System::block_number(),
				&mut info,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, ContractInfo::Alive(info.clone()));

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
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
				vec![],
				vec![],
			),
		);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let mut info = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
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
				System::block_number(),
				&mut info,
				&val.0,
				Some(val.2.clone()),
			).unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, ContractInfo::Alive(info.clone()));

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

		let trie = info.child_trie_info();

		// But value should be still there as the lazy removal did not run, yet.
		for val in &vals {
			assert_eq!(child::get::<u32>(&trie, &blake2_256(&val.0)), Some(val.1));
		}

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
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let _ = Balances::deposit_creating(&ALICE, 1000 * subsistence);

		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				subsistence * 100,
				GAS_LIMIT,
				code,
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

#[test]
fn not_deployed_if_endowment_too_low_for_first_rent() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();

	// The instantiation deducted the rent for one block immediately
	let first_rent = <Test as Config>::RentFraction::get()
		// base_deposit + deploy_set_storage (4 bytes in 1 item) - free_balance
		.mul_ceil(80_000u32 + 40_000 + 10_000 - 30_000)
		// blocks to rent
		* 1;

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_storage_noop!(assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				(BalanceOf::<Test>::from(first_rent) - BalanceOf::<Test>::from(1u32))
					.encode(), // rent allowance
				vec![],
			),
			Error::<Test>::NewContractNotFunded,
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		assert_matches!(ContractInfoOf::<Test>::get(&addr), None);
	});
}

#[test]
fn surcharge_reward_is_capped() {
	let (wasm, code_hash) = compile_module::<Test>("set_rent").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			wasm,
			<BalanceOf<Test>>::from(10_000u32).encode(), // rent allowance
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let contract = <ContractInfoOf::<Test>>::get(&addr).unwrap().get_alive().unwrap();
		let balance = Balances::free_balance(&ALICE);
		let reward = <Test as Config>::SurchargeReward::get();

		// some rent should have payed due to instantiation
		assert_ne!(contract.rent_payed, 0);

		// the reward should be parameterized sufficiently high to make this test useful
		assert!(reward > contract.rent_payed);

		// make contract eligible for eviction
		initialize_block(40);

		// this should have removed the contract
		assert_ok!(Contracts::claim_surcharge(Origin::none(), addr.clone(), Some(ALICE)));

		// this reward does not take into account the last rent payment collected during eviction
		let capped_reward = reward.min(contract.rent_payed);

		// this is smaller than the actual reward because it does not take into account the
		// rent collected during eviction
		assert!(Balances::free_balance(&ALICE) > balance + capped_reward);

		// the full reward is not payed out because of the cap introduced by rent_payed
		assert!(Balances::free_balance(&ALICE) < balance + reward);
	});
}

#[test]
fn refcounter() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let subsistence = Pallet::<Test>::subsistence_threshold();

		// Create two contracts with the same code and check that they do in fact share it.
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			subsistence * 100,
			GAS_LIMIT,
			wasm.clone(),
			vec![],
			vec![0],
		));
		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			subsistence * 100,
			GAS_LIMIT,
			wasm.clone(),
			vec![],
			vec![1],
		));
		assert_refcount!(code_hash, 2);

		// Sharing should also work with the usual instantiate call
		assert_ok!(Contracts::instantiate(
			Origin::signed(ALICE),
			subsistence * 100,
			GAS_LIMIT,
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
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr0,
			0,
			GAS_LIMIT,
			vec![],
		));
		assert_refcount!(code_hash, 2);

		// make remaining contracts eligible for eviction
		initialize_block(40);

		// remove one of them
		assert_ok!(Contracts::claim_surcharge(Origin::none(), addr1, Some(ALICE)));
		assert_refcount!(code_hash, 1);

		// Pristine code should still be there
		crate::PristineCode::<Test>::get(code_hash).unwrap();

		// remove the last contract
		assert_ok!(Contracts::claim_surcharge(Origin::none(), addr2, Some(ALICE)));
		assert_refcount!(code_hash, 0);

		// all code should be gone
		assert_matches!(crate::PristineCode::<Test>::get(code_hash), None);
		assert_matches!(crate::CodeStorage::<Test>::get(code_hash), None);
	});
}

#[test]
fn reinstrument_does_charge() {
	let (wasm, code_hash) = compile_module::<Test>("return_with_data").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let subsistence = Pallet::<Test>::subsistence_threshold();
		let zero = 0u32.to_le_bytes().encode();
		let code_len = wasm.len() as u32;

		assert_ok!(Contracts::instantiate_with_code(
			Origin::signed(ALICE),
			subsistence * 100,
			GAS_LIMIT,
			wasm,
			zero.clone(),
			vec![],
		));

		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Call the contract two times without reinstrument

		let result0 = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			zero.clone(),
			false,
		);
		assert!(result0.result.unwrap().is_success());

		let result1 = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			zero.clone(),
			false,
		);
		assert!(result1.result.unwrap().is_success());

		// They should match because both where called with the same schedule.
		assert_eq!(result0.gas_consumed, result1.gas_consumed);

		// We cannot change the schedule. Instead, we decrease the version of the deployed
		// contract below the current schedule's version.
		crate::CodeStorage::mutate(&code_hash, |code: &mut Option<PrefabWasmModule<Test>>| {
			code.as_mut().unwrap().decrement_version();
		});

		// This call should trigger reinstrumentation
		let result2 = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			zero.clone(),
			false,
		);
		assert!(result2.result.unwrap().is_success());
		assert!(result2.gas_consumed > result1.gas_consumed);
		assert_eq!(
			result2.gas_consumed,
			result1.gas_consumed + <Test as Config>::WeightInfo::instrument(code_len / 1024),
		);
	});
}

#[test]
fn debug_message_works() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_works").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			vec![],
			true,
		);

		assert_matches!(result.result, Ok(_));
		assert_eq!(std::str::from_utf8(&result.debug_message).unwrap(), "Hello World!");
	});
}

#[test]
fn debug_message_logging_disabled() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_logging_disabled").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		// disable logging by passing `false`
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			vec![],
			false,
		);
		assert_matches!(result.result, Ok(_));
		// the dispatchables always run without debugging
		assert_ok!(Contracts::call(
			Origin::signed(ALICE),
			addr,
			0,
			GAS_LIMIT,
			vec![],
		));
		assert!(result.debug_message.is_empty());
	});
}

#[test]
fn debug_message_invalid_utf8() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_invalid_utf8").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(
			Contracts::instantiate_with_code(
				Origin::signed(ALICE),
				30_000,
				GAS_LIMIT,
				wasm,
				vec![],
				vec![],
			),
		);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			vec![],
			true,
		);
		assert_err!(result.result, <Error<Test>>::DebugMessageInvalidUTF8);
	});
}
