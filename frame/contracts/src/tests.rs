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
	exec::AccountIdOf,
};
use assert_matches::assert_matches;
use codec::Encode;
use sp_runtime::{
	traits::{BlakeTwo256, Hash, IdentityLookup, Convert},
	testing::{Header, H256},
	AccountId32,
};
use frame_support::{
	assert_ok, assert_err_ignore_postinfo, impl_outer_dispatch, impl_outer_event,
	impl_outer_origin, parameter_types, StorageMap,
	traits::{Currency, ReservableCurrency},
	weights::{Weight, PostDispatchInfo},
	dispatch::DispatchErrorWithPostInfo,
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

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
	pub static ExistentialDeposit: u64 = 0;
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
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
fn call_contract_removals() {
	removals(|addr| {
		// Call on already-removed account might fail, and this is fine.
		let _ = Contracts::call(Origin::signed(ALICE), addr, 0, GAS_LIMIT, call::null());
		true
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
			assert!(trigger_call(addr.clone()));

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
			assert!(trigger_call(addr.clone()));
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
			assert!(trigger_call(addr.clone()));
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
			assert!(trigger_call(addr.clone()));
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
			assert!(trigger_call(addr.clone()));
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
			assert!(trigger_call(addr.clone()));
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
			assert!(trigger_call(addr.clone()));
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

			// Calling contract should remove contract and fail.
			assert_err_ignore_postinfo!(
				Contracts::call(Origin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, call::null()),
				Error::<Test>::NotCallable
			);
			// Calling a contract that is about to evict shall emit an event.
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::contracts(RawEvent::Evicted(addr.clone(), true)),
					topics: vec![],
				},
			]);

			// Subsequent contract calls should also fail.
			assert_err_ignore_postinfo!(
				Contracts::call(Origin::signed(ALICE), addr, 0, GAS_LIMIT, call::null()),
				Error::<Test>::NotCallable
			);
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
			// we expect that it will get removed leaving tombstone.
			assert_err_ignore_postinfo!(
				Contracts::call(
					Origin::signed(ALICE), addr_bob.clone(), 0, GAS_LIMIT, call::null()
				),
				Error::<Test>::NotCallable
			);
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
