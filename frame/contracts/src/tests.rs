// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use self::test_utils::hash;
use crate::{
	chain_extension::{
		ChainExtension, Environment, Ext, InitState, RegisteredChainExtension,
		Result as ExtensionResult, RetVal, ReturnFlags, SysConfig, UncheckedFrom,
	},
	exec::{FixSizedKey, Frame},
	storage::Storage,
	tests::test_utils::{get_contract, get_contract_checked},
	wasm::{Determinism, PrefabWasmModule, ReturnCode as RuntimeReturnCode},
	weights::WeightInfo,
	BalanceOf, Code, CodeStorage, Config, ContractInfoOf, DefaultAddressGenerator, DeletionQueue,
	Error, Pallet, Schedule,
};
use assert_matches::assert_matches;
use codec::Encode;
use frame_support::{
	assert_err, assert_err_ignore_postinfo, assert_noop, assert_ok,
	dispatch::{DispatchClass, DispatchErrorWithPostInfo, PostDispatchInfo},
	parameter_types,
	storage::child,
	traits::{
		BalanceStatus, ConstU32, ConstU64, Contains, Currency, Get, LockableCurrency, OnIdle,
		OnInitialize, ReservableCurrency, WithdrawReasons,
	},
	weights::{constants::WEIGHT_PER_SECOND, Weight},
};
use frame_system::{self as system, EventRecord, Phase};
use pretty_assertions::{assert_eq, assert_ne};
use sp_io::hashing::blake2_256;
use sp_keystore::{testing::KeyStore, KeystoreExt};
use sp_runtime::{
	testing::{Header, H256},
	traits::{BlakeTwo256, Convert, Hash, IdentityLookup},
	AccountId32,
};
use std::sync::Arc;

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
	use super::{Balances, Hash, SysConfig, Test};
	use crate::{
		exec::AccountIdOf, storage::Storage, CodeHash, Config, ContractInfo, ContractInfoOf, Nonce,
	};
	use codec::Encode;
	use frame_support::traits::Currency;

	pub fn place_contract(address: &AccountIdOf<Test>, code_hash: CodeHash<Test>) {
		let nonce = <Nonce<Test>>::mutate(|counter| {
			*counter += 1;
			*counter
		});
		let trie_id = Storage::<Test>::generate_trie_id(address, nonce);
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
	pub fn get_contract(addr: &AccountIdOf<Test>) -> ContractInfo<Test> {
		get_contract_checked(addr).unwrap()
	}
	pub fn get_contract_checked(addr: &AccountIdOf<Test>) -> Option<ContractInfo<Test>> {
		ContractInfoOf::<Test>::get(addr)
	}
	pub fn hash<S: Encode>(s: &S) -> <<Test as SysConfig>::Hashing as Hash>::Output {
		<<Test as SysConfig>::Hashing as Hash>::hash_of(s)
	}
	macro_rules! assert_return_code {
		( $x:expr , $y:expr $(,)? ) => {{
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

impl Test {
	pub fn set_unstable_interface(unstable_interface: bool) {
		UNSTABLE_INTERFACE.with(|v| *v.borrow_mut() = unstable_interface);
	}
}

parameter_types! {
	static TestExtensionTestValue: TestExtension = Default::default();
}

#[derive(Clone)]
pub struct TestExtension {
	enabled: bool,
	last_seen_buffer: Vec<u8>,
	last_seen_inputs: (u32, u32, u32, u32),
}

#[derive(Default)]
pub struct RevertingExtension;

#[derive(Default)]
pub struct DisabledExtension;

#[derive(Default)]
pub struct TempStorageExtension {
	storage: u32,
}

impl TestExtension {
	fn disable() {
		TestExtensionTestValue::mutate(|e| e.enabled = false)
	}

	fn last_seen_buffer() -> Vec<u8> {
		TestExtensionTestValue::get().last_seen_buffer.clone()
	}

	fn last_seen_inputs() -> (u32, u32, u32, u32) {
		TestExtensionTestValue::get().last_seen_inputs
	}
}

impl Default for TestExtension {
	fn default() -> Self {
		Self { enabled: true, last_seen_buffer: vec![], last_seen_inputs: (0, 0, 0, 0) }
	}
}

impl ChainExtension<Test> for TestExtension {
	fn call<E>(&mut self, env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
		E: Ext<T = Test>,
		<E::T as SysConfig>::AccountId: UncheckedFrom<<E::T as SysConfig>::Hash> + AsRef<[u8]>,
	{
		let func_id = env.func_id();
		let id = env.ext_id() as u32 | func_id as u32;
		match func_id {
			0 => {
				let mut env = env.buf_in_buf_out();
				let input = env.read(8)?;
				env.write(&input, false, None)?;
				TestExtensionTestValue::mutate(|e| e.last_seen_buffer = input);
				Ok(RetVal::Converging(id))
			},
			1 => {
				let env = env.only_in();
				TestExtensionTestValue::mutate(|e| {
					e.last_seen_inputs = (env.val0(), env.val1(), env.val2(), env.val3())
				});
				Ok(RetVal::Converging(id))
			},
			2 => {
				let mut env = env.buf_in_buf_out();
				let weight = Weight::from_ref_time(env.read(5)?[4].into());
				env.charge_weight(weight)?;
				Ok(RetVal::Converging(id))
			},
			3 => Ok(RetVal::Diverging { flags: ReturnFlags::REVERT, data: vec![42, 99] }),
			_ => {
				panic!("Passed unknown id to test chain extension: {}", func_id);
			},
		}
	}

	fn enabled() -> bool {
		TestExtensionTestValue::get().enabled
	}
}

impl RegisteredChainExtension<Test> for TestExtension {
	const ID: u16 = 0;
}

impl ChainExtension<Test> for RevertingExtension {
	fn call<E>(&mut self, _env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
		E: Ext<T = Test>,
		<E::T as SysConfig>::AccountId: UncheckedFrom<<E::T as SysConfig>::Hash> + AsRef<[u8]>,
	{
		Ok(RetVal::Diverging { flags: ReturnFlags::REVERT, data: vec![0x4B, 0x1D] })
	}

	fn enabled() -> bool {
		TestExtensionTestValue::get().enabled
	}
}

impl RegisteredChainExtension<Test> for RevertingExtension {
	const ID: u16 = 1;
}

impl ChainExtension<Test> for DisabledExtension {
	fn call<E>(&mut self, _env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
		E: Ext<T = Test>,
		<E::T as SysConfig>::AccountId: UncheckedFrom<<E::T as SysConfig>::Hash> + AsRef<[u8]>,
	{
		panic!("Disabled chain extensions are never called")
	}

	fn enabled() -> bool {
		false
	}
}

impl RegisteredChainExtension<Test> for DisabledExtension {
	const ID: u16 = 2;
}

impl ChainExtension<Test> for TempStorageExtension {
	fn call<E>(&mut self, env: Environment<E, InitState>) -> ExtensionResult<RetVal>
	where
		E: Ext<T = Test>,
		<E::T as SysConfig>::AccountId: UncheckedFrom<<E::T as SysConfig>::Hash> + AsRef<[u8]>,
	{
		let func_id = env.func_id();
		match func_id {
			0 => self.storage = 42,
			1 => assert_eq!(self.storage, 42, "Storage is preserved inside the same call."),
			2 => {
				assert_eq!(self.storage, 0, "Storage is different for different calls.");
				self.storage = 99;
			},
			3 => assert_eq!(self.storage, 99, "Storage is preserved inside the same call."),
			_ => {
				panic!("Passed unknown id to test chain extension: {}", func_id);
			},
		}
		Ok(RetVal::Converging(0))
	}

	fn enabled() -> bool {
		TestExtensionTestValue::get().enabled
	}
}

impl RegisteredChainExtension<Test> for TempStorageExtension {
	const ID: u16 = 3;
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(
			(2u64 * WEIGHT_PER_SECOND).set_proof_size(u64::MAX),
		);
	pub static ExistentialDeposit: u64 = 1;
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId32;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
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
	type RuntimeEvent = RuntimeEvent;
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
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
}
parameter_types! {
	pub MySchedule: Schedule<Test> = {
		let mut schedule = <Schedule<Test>>::default();
		// We want stack height to be always enabled for tests so that this
		// instrumentation path is always tested implicitly.
		schedule.limits.stack_height = Some(512);
		schedule.instruction_weights.fallback = 1;
		schedule
	};
	pub static DepositPerByte: BalanceOf<Test> = 1;
	pub const DepositPerItem: BalanceOf<Test> = 2;
}

impl Convert<Weight, BalanceOf<Self>> for Test {
	fn convert(w: Weight) -> BalanceOf<Self> {
		w.ref_time()
	}
}

/// A filter whose filter function can be swapped at runtime.
pub struct TestFilter;

#[derive(Clone)]
pub struct Filters {
	filter: fn(&RuntimeCall) -> bool,
}

impl Default for Filters {
	fn default() -> Self {
		Filters { filter: (|_| true) }
	}
}

parameter_types! {
	static CallFilter: Filters = Default::default();
}

impl TestFilter {
	pub fn set_filter(filter: fn(&RuntimeCall) -> bool) {
		CallFilter::mutate(|fltr| fltr.filter = filter);
	}
}

impl Contains<RuntimeCall> for TestFilter {
	fn contains(call: &RuntimeCall) -> bool {
		(CallFilter::get().filter)(call)
	}
}

parameter_types! {
	pub const DeletionWeightLimit: Weight = Weight::from_ref_time(500_000_000_000);
	pub static UnstableInterface: bool = true;
}

impl Config for Test {
	type Time = Timestamp;
	type Randomness = Randomness;
	type Currency = Balances;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type CallFilter = TestFilter;
	type CallStack = [Frame<Self>; 31];
	type WeightPrice = Self;
	type WeightInfo = ();
	type ChainExtension =
		(TestExtension, DisabledExtension, RevertingExtension, TempStorageExtension);
	type DeletionQueueDepth = ConstU32<1024>;
	type DeletionWeightLimit = DeletionWeightLimit;
	type Schedule = MySchedule;
	type DepositPerByte = DepositPerByte;
	type DepositPerItem = DepositPerItem;
	type AddressGenerator = DefaultAddressGenerator;
	type MaxCodeLen = ConstU32<{ 128 * 1024 }>;
	type MaxStorageKeyLen = ConstU32<128>;
	type UnsafeUnstableInterface = UnstableInterface;
}

pub const ALICE: AccountId32 = AccountId32::new([1u8; 32]);
pub const BOB: AccountId32 = AccountId32::new([2u8; 32]);
pub const CHARLIE: AccountId32 = AccountId32::new([3u8; 32]);
pub const DJANGO: AccountId32 = AccountId32::new([4u8; 32]);

pub const GAS_LIMIT: Weight = Weight::from_ref_time(100_000_000_000).set_proof_size(256 * 1024);

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
		ext.register_extension(KeystoreExt(Arc::new(KeyStore::new())));
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

fn initialize_block(number: u64) {
	System::reset_events();
	System::initialize(&number, &[0u8; 32].into(), &Default::default());
}

struct ExtensionInput<'a> {
	extension_id: u16,
	func_id: u16,
	extra: &'a [u8],
}

impl<'a> ExtensionInput<'a> {
	fn to_vec(&self) -> Vec<u8> {
		((self.extension_id as u32) << 16 | (self.func_id as u32))
			.to_le_bytes()
			.iter()
			.chain(self.extra)
			.cloned()
			.collect()
	}
}

impl<'a> From<ExtensionInput<'a>> for Vec<u8> {
	fn from(input: ExtensionInput) -> Vec<u8> {
		input.to_vec()
	}
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
			Contracts::call(RuntimeOrigin::signed(ALICE), BOB, 0, GAS_LIMIT, None, Vec::new()),
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
	let (wasm, code_hash) = compile_module::<Test>("event_and_return_on_deploy").unwrap();

	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let value = 100;

		// We determine the storage deposit limit after uploading because it depends on ALICEs free
		// balance which is changed by uploading a module.
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm,
			None,
			Determinism::Deterministic
		));

		// Drop previous events
		initialize_block(2);

		// Check at the end to get hash on error easily
		assert_ok!(Contracts::instantiate(
			RuntimeOrigin::signed(ALICE),
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
					event: RuntimeEvent::System(frame_system::Event::NewAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: value,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::ContractEmitted {
						contract: addr.clone(),
						data: vec![1, 2, 3, 4]
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone()
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
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
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT.set_ref_time(GAS_LIMIT.ref_time() * 2), // we are copying a huge buffer,
			None,
			<Test as Config>::Schedule::get().limits.payload_len.encode(),
		));

		// Call contract with too large a storage value.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
				RuntimeOrigin::signed(ALICE),
				addr, // newly created account
				0,
				Weight::from_ref_time(1_000_000_000_000).set_proof_size(u64::MAX),
				None,
				vec![],
			),
			Error::<Test>::OutOfGas,
		);
	});
}

/// Check that contracts with the same account id have different trie ids.
/// Check the `Nonce` storage item for more information.
#[test]
fn instantiate_unique_trie_id() {
	let (wasm, code_hash) = compile_module::<Test>("self_destruct").unwrap();

	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm,
			None,
			Determinism::Deterministic,
		)
		.unwrap();
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Instantiate the contract and store its trie id for later comparison.
		assert_ok!(Contracts::instantiate(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			code_hash,
			vec![],
			vec![],
		));
		let trie_id = get_contract(&addr).trie_id;

		// Try to instantiate it again without termination should yield an error.
		assert_err_ignore_postinfo!(
			Contracts::instantiate(
				RuntimeOrigin::signed(ALICE),
				0,
				GAS_LIMIT,
				None,
				code_hash,
				vec![],
				vec![],
			),
			<Error<Test>>::DuplicateContract,
		);

		// Terminate the contract.
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![]
		));

		// Re-Instantiate after termination.
		assert_ok!(Contracts::instantiate(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			code_hash,
			vec![],
			vec![],
		));

		// Trie ids shouldn't match or we might have a collision
		assert_ne!(trie_id, get_contract(&addr).trie_id);
	});
}

#[test]
fn storage_max_value_limit() {
	let (wasm, code_hash) = compile_module::<Test>("storage_size").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Create
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		get_contract(&addr);

		// Call contract with allowed storage value.
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT.set_ref_time(GAS_LIMIT.ref_time() * 2), // we are copying a huge buffer
			None,
			<Test as Config>::Schedule::get().limits.payload_len.encode(),
		));

		// Call contract with too large a storage value.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			caller_wasm,
			vec![],
			vec![],
		));
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
					event: RuntimeEvent::System(frame_system::Event::NewAccount {
						account: callee_addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Endowed {
						account: callee_addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: callee_addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: callee_addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: caller_addr.clone(),
						to: callee_addr.clone(),
						amount: 32768, // hard coded in wasm
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Instantiated {
						deployer: caller_addr.clone(),
						contract: callee_addr.clone(),
					}),
					topics: vec![hash(&caller_addr), hash(&callee_addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: caller_addr.clone(),
						to: callee_addr.clone(),
						amount: 32768,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: caller_addr.clone(),
						contract: callee_addr.clone(),
					}),
					topics: vec![hash(&caller_addr), hash(&callee_addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: caller_addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&caller_addr)],
				},
			]
		);
	});
}

#[test]
fn delegate_call() {
	let (caller_wasm, caller_code_hash) = compile_module::<Test>("delegate_call").unwrap();
	let (callee_wasm, callee_code_hash) = compile_module::<Test>("delegate_call_lib").unwrap();
	let caller_addr = Contracts::contract_address(&ALICE, &caller_code_hash, &[]);

	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the 'caller'
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			caller_wasm,
			vec![],
			vec![],
		));
		// Only upload 'callee' code
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			callee_wasm,
			Some(codec::Compact(100_000)),
			Determinism::Deterministic,
		));

		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			caller_addr.clone(),
			1337,
			GAS_LIMIT,
			None,
			callee_code_hash.as_ref().to_vec(),
		));
	});
}

#[test]
fn cannot_self_destruct_through_draning() {
	let (wasm, code_hash) = compile_module::<Test>("drain").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			1_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		get_contract(&addr);

		// Call BOB which makes it send all funds to the zero address
		// The contract code asserts that the transfer was successful
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated and has the minimum balance
		assert_eq!(get_contract(&addr).total_deposit(), min_balance);
		assert_eq!(get_contract(&addr).extra_deposit(), 0);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// Create 100 bytes of storage with a price of per byte and a single storage item of price 2
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			100u32.to_le_bytes().to_vec()
		));
		assert_eq!(get_contract(&addr).total_deposit(), min_balance + 102);

		// Increase the byte price and trigger a refund. This should not have any influence because
		// the removal is pro rata and exactly those 100 bytes should have been removed.
		DEPOSIT_PER_BYTE.with(|c| *c.borrow_mut() = 500);
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			0u32.to_le_bytes().to_vec()
		));

		// Make sure the account wasn't removed by the refund
		assert_eq!(
			<Test as Config>::Currency::total_balance(&addr),
			get_contract(&addr).total_deposit(),
		);
		assert_eq!(get_contract(&addr).extra_deposit(), 2,);
	});
}

#[test]
fn cannot_self_destruct_by_refund_after_slash() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(500).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			48u32.encode(),
		));

		// Make sure the account kept the minimum balance and was not destroyed
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Slashed {
						who: addr.clone(),
						amount: 90,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::ReserveRepatriated {
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
			RuntimeOrigin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		get_contract(&addr);

		// Call BOB with input data, forcing it make a recursive call to itself to
		// self-destruct, resulting in a trap.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				vec![0],
			),
			Error::<Test>::ContractTrapped,
		);

		// Check that BOB is still there.
		get_contract(&addr);
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
			RuntimeOrigin::signed(ALICE),
			100_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		get_contract(&addr);

		// Drop all previous events
		initialize_block(2);

		// Call BOB without input data which triggers termination.
		assert_matches!(
			Contracts::call(RuntimeOrigin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
			Ok(_)
		);

		// Check that code is still there but refcount dropped to zero.
		assert_refcount!(&code_hash, 0);

		// Check that account is gone
		assert!(get_contract_checked(&addr).is_none());
		assert_eq!(Balances::total_balance(&addr), 0);

		// check that the beneficiary (django) got remaining balance
		assert_eq!(Balances::free_balance(DJANGO), 1_000_000 + 100_000);

		pretty_assertions::assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: addr.clone(),
						to: DJANGO,
						amount: 100_000,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Terminated {
						contract: addr.clone(),
						beneficiary: DJANGO
					}),
					topics: vec![hash(&addr), hash(&DJANGO)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::System(frame_system::Event::KilledAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::ReserveRepatriated {
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
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
		get_contract(&addr_charlie);

		// Call BOB, which calls CHARLIE, forcing CHARLIE to self-destruct.
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr_bob,
			0,
			GAS_LIMIT,
			None,
			addr_charlie.encode(),
		));

		// Check that CHARLIE has moved on to the great beyond (ie. died).
		assert!(get_contract_checked(&addr_charlie).is_none());
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
				RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
			let result = <Pallet<Test>>::bare_call(
				ALICE,
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				params,
				false,
				Determinism::Deterministic,
			)
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
			RuntimeOrigin::signed(ALICE),
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
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![],
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough total balance in order to not go below the min balance
		// threshold when transfering 100 balance but this balance is reserved so
		// the transfer still fails.
		Balances::make_free_balance_be(&addr, min_balance + 100);
		Balances::reserve(&addr, min_balance + 100).unwrap();
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			None,
			vec![],
			false,
			Determinism::Deterministic,
		)
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
			RuntimeOrigin::signed(ALICE),
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
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::NotCallable);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(CHARLIE),
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
			Determinism::Deterministic,
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
			Determinism::Deterministic,
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
			Determinism::Deterministic,
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
			Determinism::Deterministic,
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
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			callee_code,
			vec![],
			vec![],
		),);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
			Determinism::Deterministic,
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
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_return_code!(result, RuntimeReturnCode::TransferFailed);

		// Contract has enough balance but the passed code hash is invalid
		Balances::make_free_balance_be(&addr, min_balance + 10_000);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![0; 33],
			false,
			Determinism::Deterministic,
		)
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
			Determinism::Deterministic,
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
			Determinism::Deterministic,
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
				RuntimeOrigin::signed(ALICE),
				3 * min_balance,
				GAS_LIMIT,
				None,
				code,
				vec![],
				vec![],
			),
			<Error<Test>>::CodeRejected,
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
			RuntimeOrigin::signed(ALICE),
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
			Contracts::call(RuntimeOrigin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
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
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// 0 = read input buffer and pass it through as output
		let input: Vec<u8> = ExtensionInput { extension_id: 0, func_id: 0, extra: &[99] }.into();
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			input.clone(),
			false,
			Determinism::Deterministic,
		);
		assert_eq!(TestExtension::last_seen_buffer(), input);
		assert_eq!(result.result.unwrap().data, input);

		// 1 = treat inputs as integer primitives and store the supplied integers
		Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 0, func_id: 1, extra: &[] }.into(),
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		// those values passed in the fixture
		assert_eq!(TestExtension::last_seen_inputs(), (4, 4, 16, 12));

		// 2 = charge some extra weight (amount supplied in the fifth byte)
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 0, func_id: 2, extra: &[0] }.into(),
			false,
			Determinism::Deterministic,
		);
		assert_ok!(result.result);
		let gas_consumed = result.gas_consumed;
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 0, func_id: 2, extra: &[42] }.into(),
			false,
			Determinism::Deterministic,
		);
		assert_ok!(result.result);
		assert_eq!(result.gas_consumed.ref_time(), gas_consumed.ref_time() + 42);
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 0, func_id: 2, extra: &[95] }.into(),
			false,
			Determinism::Deterministic,
		);
		assert_ok!(result.result);
		assert_eq!(result.gas_consumed.ref_time(), gas_consumed.ref_time() + 95);

		// 3 = diverging chain extension call that sets flags to 0x1 and returns a fixed buffer
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 0, func_id: 3, extra: &[] }.into(),
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_eq!(result.flags, ReturnFlags::REVERT);
		assert_eq!(result.data, vec![42, 99]);

		// diverging to second chain extension that sets flags to 0x1 and returns a fixed buffer
		// We set the MSB part to 1 (instead of 0) which routes the request into the second
		// extension
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			ExtensionInput { extension_id: 1, func_id: 0, extra: &[] }.into(),
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_eq!(result.flags, ReturnFlags::REVERT);
		assert_eq!(result.data, vec![0x4B, 0x1D]);

		// Diverging to third chain extension that is disabled
		// We set the MSB part to 2 (instead of 0) which routes the request into the third extension
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				ExtensionInput { extension_id: 2, func_id: 0, extra: &[] }.into(),
			),
			Error::<Test>::NoChainExtension,
		);
	});
}

#[test]
fn chain_extension_temp_storage_works() {
	let (code, hash) = compile_module::<Test>("chain_extension_temp_storage").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &hash, &[]);

		// Call func 0 and func 1 back to back.
		let stop_recursion = 0u8;
		let mut input: Vec<u8> = ExtensionInput { extension_id: 3, func_id: 0, extra: &[] }.into();
		input.extend_from_slice(
			ExtensionInput { extension_id: 3, func_id: 1, extra: &[stop_recursion] }
				.to_vec()
				.as_ref(),
		);

		assert_ok!(
			Contracts::bare_call(
				ALICE,
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				input.clone(),
				false,
				Determinism::Deterministic
			)
			.result
		);
	})
}

#[test]
fn lazy_removal_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = get_contract(&addr);
		let trie = &info.child_trie_info();

		// Put value into the contracts child trie
		child::put(trie, &[99], &42);

		// Terminate the contract
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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
		Contracts::on_idle(System::block_number(), Weight::MAX);

		// Value should be gone now
		assert_matches!(child::get::<i32>(trie, &[99]), None);
	});
}

#[test]
fn lazy_removal_on_full_queue_works_on_initialize() {
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Fill the deletion queue with dummy values, so that on_initialize attempts
		// to clear the queue
		Storage::<Test>::fill_queue_with_dummies();

		let queue_len_initial = <DeletionQueue<Test>>::decode_len().unwrap_or(0);

		// Run the lazy removal
		Contracts::on_initialize(System::block_number());

		let queue_len_after_on_initialize = <DeletionQueue<Test>>::decode_len().unwrap_or(0);

		// Queue length should be decreased after call of on_initialize()
		assert!(queue_len_initial - queue_len_after_on_initialize > 0);
	});
}

#[test]
fn lazy_batch_removal_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let mut tries: Vec<child::ChildInfo> = vec![];

		for i in 0..3u8 {
			assert_ok!(Contracts::instantiate_with_code(
				RuntimeOrigin::signed(ALICE),
				min_balance * 100,
				GAS_LIMIT,
				None,
				code.clone(),
				vec![],
				vec![i],
			),);

			let addr = Contracts::contract_address(&ALICE, &hash, &[i]);
			let info = get_contract(&addr);
			let trie = &info.child_trie_info();

			// Put value into the contracts child trie
			child::put(trie, &[99], &42);

			// Terminate the contract. Contract info should be gone, but value should be still there
			// as the lazy removal did not run, yet.
			assert_ok!(Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				vec![]
			));

			assert!(!<ContractInfoOf::<Test>>::contains_key(&addr));
			assert_matches!(child::get(trie, &[99]), Some(42));

			tries.push(trie.clone())
		}

		// Run single lazy removal
		Contracts::on_idle(System::block_number(), Weight::MAX);

		// The single lazy removal should have removed all queued tries
		for trie in tries.iter() {
			assert_matches!(child::get::<i32>(trie, &[99]), None);
		}
	});
}

#[test]
fn lazy_removal_partial_remove_works() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();

	// We create a contract with some extra keys above the weight limit
	let extra_keys = 7u32;
	let weight_limit = Weight::from_ref_time(5_000_000_000);
	let (_, max_keys) = Storage::<Test>::deletion_budget(1, weight_limit);
	let vals: Vec<_> = (0..max_keys + extra_keys)
		.map(|i| (blake2_256(&i.encode()), (i as u32), (i as u32).encode()))
		.collect();

	let mut ext = ExtBuilder::default().existential_deposit(50).build();

	let trie = ext.execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = get_contract(&addr);

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				&info.trie_id,
				&val.0 as &FixSizedKey,
				Some(val.2.clone()),
				None,
				false,
			)
			.unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, info.clone());

		// Terminate the contract
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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
fn lazy_removal_does_no_run_on_full_queue_and_full_block() {
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		// Fill up the block which should prevent the lazy storage removal from running.
		System::register_extra_weight_unchecked(
			<Test as system::Config>::BlockWeights::get().max_block,
			DispatchClass::Mandatory,
		);

		// Fill the deletion queue with dummy values, so that on_initialize attempts
		// to clear the queue
		Storage::<Test>::fill_queue_with_dummies();

		// Check that on_initialize() tries to perform lazy removal but removes nothing
		//  as no more weight is left for that.
		let weight_used = Contracts::on_initialize(System::block_number());
		let base = <<Test as Config>::WeightInfo as WeightInfo>::on_process_deletion_queue_batch();
		assert_eq!(weight_used, base);

		// Check that the deletion queue is still full after execution of the
		// on_initialize() hook.
		let max_len: u32 = <Test as Config>::DeletionQueueDepth::get();
		let queue_len: u32 = <DeletionQueue<Test>>::decode_len().unwrap_or(0).try_into().unwrap();
		assert_eq!(max_len, queue_len);
	});
}

#[test]
fn lazy_removal_does_no_run_on_low_remaining_weight() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = get_contract(&addr);
		let trie = &info.child_trie_info();

		// Put value into the contracts child trie
		child::put(trie, &[99], &42);

		// Terminate the contract
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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

		// Assign a remaining weight which is too low for a successfull deletion of the contract
		let low_remaining_weight =
			<<Test as Config>::WeightInfo as WeightInfo>::on_process_deletion_queue_batch();

		// Run the lazy removal
		Contracts::on_idle(System::block_number(), low_remaining_weight);

		// Value should still be there, since remaining weight was too low for removal
		assert_matches!(child::get::<i32>(trie, &[99]), Some(42));

		// Run the lazy removal while deletion_queue is not full
		Contracts::on_initialize(System::block_number());

		// Value should still be there, since deletion_queue was not full
		assert_matches!(child::get::<i32>(trie, &[99]), Some(42));

		// Run on_idle with max remaining weight, this should remove the value
		Contracts::on_idle(System::block_number(), Weight::MAX);

		// Value should be gone
		assert_matches!(child::get::<i32>(trie, &[99]), None);
	});
}

#[test]
fn lazy_removal_does_not_use_all_weight() {
	let (code, hash) = compile_module::<Test>("self_destruct").unwrap();

	let weight_limit = Weight::from_ref_time(5_000_000_000);
	let mut ext = ExtBuilder::default().existential_deposit(50).build();

	let (trie, vals, weight_per_key) = ext.execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			code,
			vec![],
			vec![],
		),);

		let addr = Contracts::contract_address(&ALICE, &hash, &[]);
		let info = get_contract(&addr);
		let (weight_per_key, max_keys) = Storage::<Test>::deletion_budget(1, weight_limit);

		// We create a contract with one less storage item than we can remove within the limit
		let vals: Vec<_> = (0..max_keys - 1)
			.map(|i| (blake2_256(&i.encode()), (i as u32), (i as u32).encode()))
			.collect();

		// Put value into the contracts child trie
		for val in &vals {
			Storage::<Test>::write(
				&info.trie_id,
				&val.0 as &FixSizedKey,
				Some(val.2.clone()),
				None,
				false,
			)
			.unwrap();
		}
		<ContractInfoOf<Test>>::insert(&addr, info.clone());

		// Terminate the contract
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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
		assert_eq!(weight_used, weight_limit - Weight::from_ref_time(weight_per_key));

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
			RuntimeOrigin::signed(ALICE),
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
			Contracts::call(RuntimeOrigin::signed(ALICE), addr.clone(), 0, GAS_LIMIT, None, vec![],),
			Error::<Test>::DeletionQueueFull,
		);

		// Contract should exist because removal failed
		get_contract(&addr);
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
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			wasm.clone(),
			vec![],
			vec![0],
		));
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
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
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr0,
			0,
			GAS_LIMIT,
			None,
			vec![]
		));
		assert_refcount!(code_hash, 2);

		// remove another one
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr1,
			0,
			GAS_LIMIT,
			None,
			vec![]
		));
		assert_refcount!(code_hash, 1);

		// Pristine code should still be there
		crate::PristineCode::<Test>::get(code_hash).unwrap();

		// remove the last contract
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr2,
			0,
			GAS_LIMIT,
			None,
			vec![]
		));
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
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
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
			None,
			zero.clone(),
			false,
			Determinism::Deterministic,
		);
		assert!(!result0.result.unwrap().did_revert());

		let result1 = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			zero.clone(),
			false,
			Determinism::Deterministic,
		);
		assert!(!result1.result.unwrap().did_revert());

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
			None,
			zero.clone(),
			false,
			Determinism::Deterministic,
		);
		assert!(!result2.result.unwrap().did_revert());
		assert!(result2.gas_consumed.ref_time() > result1.gas_consumed.ref_time());
		assert_eq!(
			result2.gas_consumed.ref_time(),
			result1.gas_consumed.ref_time() +
				<Test as Config>::WeightInfo::reinstrument(code_len).ref_time(),
		);
	});
}

#[test]
fn debug_message_works() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_works").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			None,
			vec![],
			true,
			Determinism::Deterministic,
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
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		// disable logging by passing `false`
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![],
			false,
			Determinism::Deterministic,
		);
		assert_matches!(result.result, Ok(_));
		// the dispatchables always run without debugging
		assert_ok!(Contracts::call(RuntimeOrigin::signed(ALICE), addr, 0, GAS_LIMIT, None, vec![]));
		assert!(result.debug_message.is_empty());
	});
}

#[test]
fn debug_message_invalid_utf8() {
	let (wasm, code_hash) = compile_module::<Test>("debug_message_invalid_utf8").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			30_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		),);
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let result = Contracts::bare_call(
			ALICE,
			addr,
			0,
			GAS_LIMIT,
			None,
			vec![],
			true,
			Determinism::Deterministic,
		);
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
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![],
			vec![0],
		),);
		let addr_caller = Contracts::contract_address(&ALICE, &caller_hash, &[0]);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
			.chain((GAS_LIMIT / 5).ref_time().to_le_bytes())
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
			Determinism::Deterministic,
		);
		assert_ok!(&result.result);

		// We have a subcall with a fixed gas limit. This constitutes precharging.
		assert!(result.gas_required.ref_time() > result.gas_consumed.ref_time());

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
				Determinism::Deterministic,
			)
			.result
		);
	});
}

#[test]
fn gas_estimation_call_runtime() {
	use codec::Decode;
	let (caller_code, caller_hash) = compile_module::<Test>("call_runtime").unwrap();
	let (callee_code, callee_hash) = compile_module::<Test>("dummy").unwrap();
	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let min_balance = <Test as Config>::Currency::minimum_balance();
		let _ = Balances::deposit_creating(&ALICE, 1000 * min_balance);
		let _ = Balances::deposit_creating(&CHARLIE, 1000 * min_balance);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			min_balance * 100,
			GAS_LIMIT,
			None,
			caller_code,
			vec![],
			vec![0],
		),);
		let addr_caller = Contracts::contract_address(&ALICE, &caller_hash, &[0]);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
		let call = RuntimeCall::Contracts(crate::Call::call {
			dest: addr_callee,
			value: 0,
			gas_limit: GAS_LIMIT.set_ref_time(GAS_LIMIT.ref_time() / 3),
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
			Determinism::Deterministic,
		);
		// contract encodes the result of the dispatch runtime
		let outcome = u32::decode(&mut result.result.unwrap().data.as_ref()).unwrap();
		assert_eq!(outcome, 0);
		assert!(result.gas_required.ref_time() > result.gas_consumed.ref_time());

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
				Determinism::Deterministic,
			)
			.result
		);
	});
}

#[test]
fn ecdsa_recover() {
	let (wasm, code_hash) = compile_module::<Test>("ecdsa_recover").unwrap();

	ExtBuilder::default().existential_deposit(50).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the ecdsa_recover contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
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
		let result = <Pallet<Test>>::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			params,
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert!(!result.did_revert());
		assert_eq!(result.data, EXPECTED_COMPRESSED_PUBLIC_KEY);
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
			RuntimeOrigin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000)),
			Determinism::Deterministic,
		));
		assert!(<CodeStorage<Test>>::contains_key(code_hash));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![code_hash],
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
			Contracts::upload_code(
				RuntimeOrigin::signed(ALICE),
				wasm,
				Some(codec::Compact(100)),
				Determinism::Deterministic
			),
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
			Contracts::upload_code(
				RuntimeOrigin::signed(ALICE),
				wasm,
				Some(codec::Compact(1_000)),
				Determinism::Deterministic
			),
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
			RuntimeOrigin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000)),
			Determinism::Deterministic,
		));

		assert!(<CodeStorage<Test>>::contains_key(code_hash));
		assert_ok!(Contracts::remove_code(RuntimeOrigin::signed(ALICE), code_hash));
		assert!(!<CodeStorage<Test>>::contains_key(code_hash));

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![code_hash],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Unreserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeRemoved { code_hash }),
					topics: vec![code_hash],
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
			RuntimeOrigin::signed(ALICE),
			wasm,
			Some(codec::Compact(1_000)),
			Determinism::Deterministic,
		));

		assert_noop!(
			Contracts::remove_code(RuntimeOrigin::signed(BOB), code_hash),
			sp_runtime::traits::BadOrigin,
		);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![code_hash],
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
			RuntimeOrigin::signed(ALICE),
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
			Contracts::remove_code(RuntimeOrigin::signed(ALICE), code_hash),
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
			Contracts::remove_code(RuntimeOrigin::signed(ALICE), code_hash),
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
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		get_contract(&addr);

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
					event: RuntimeEvent::System(frame_system::Event::NewAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![code_hash],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
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
			RuntimeOrigin::signed(ALICE),
			50,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated.
		get_contract(&addr);

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
					event: RuntimeEvent::System(frame_system::Event::NewAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: min_balance,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: 50,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: ALICE,
						amount: 241,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::CodeStored { code_hash }),
					topics: vec![code_hash],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Instantiated {
						deployer: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
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
			RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			42,
			GAS_LIMIT,
			None,
			(1_000u32, 5_000u32).encode(),
		));
		// 4 is for creating 2 storage items
		let charged0 = 4 + 1_000 + 5_000;
		deposit += charged0;
		assert_eq!(get_contract(&addr).total_deposit(), deposit);

		// Add more storage (but also remove some)
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			(2_000u32, 4_900u32).encode(),
		));
		let charged1 = 1_000 - 100;
		deposit += charged1;
		assert_eq!(get_contract(&addr).total_deposit(), deposit);

		// Remove more storage (but also add some)
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			(2_100u32, 900u32).encode(),
		));
		// -1 for numeric instability
		let refunded0 = 4_000 - 100 - 1;
		deposit -= refunded0;
		assert_eq!(get_contract(&addr).total_deposit(), deposit);

		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: 42,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: charged0,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: charged0,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: charged1,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Reserved {
						who: addr.clone(),
						amount: charged1,
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::ReserveRepatriated {
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
fn set_code_extrinsic() {
	let (wasm, code_hash) = compile_module::<Test>("dummy").unwrap();
	let (new_wasm, new_code_hash) = compile_module::<Test>("crypto_hashes").unwrap();

	assert_ne!(code_hash, new_code_hash);

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			new_wasm,
			None,
			Determinism::Deterministic
		));

		// Drop previous events
		initialize_block(2);

		assert_eq!(get_contract(&addr).code_hash, code_hash);
		assert_refcount!(&code_hash, 1);
		assert_refcount!(&new_code_hash, 0);

		// only root can execute this extrinsic
		assert_noop!(
			Contracts::set_code(RuntimeOrigin::signed(ALICE), addr.clone(), new_code_hash),
			sp_runtime::traits::BadOrigin,
		);
		assert_eq!(get_contract(&addr).code_hash, code_hash);
		assert_refcount!(&code_hash, 1);
		assert_refcount!(&new_code_hash, 0);
		assert_eq!(System::events(), vec![],);

		// contract must exist
		assert_noop!(
			Contracts::set_code(RuntimeOrigin::root(), BOB, new_code_hash),
			<Error<Test>>::ContractNotFound,
		);
		assert_eq!(get_contract(&addr).code_hash, code_hash);
		assert_refcount!(&code_hash, 1);
		assert_refcount!(&new_code_hash, 0);
		assert_eq!(System::events(), vec![],);

		// new code hash must exist
		assert_noop!(
			Contracts::set_code(RuntimeOrigin::root(), addr.clone(), Default::default()),
			<Error<Test>>::CodeNotFound,
		);
		assert_eq!(get_contract(&addr).code_hash, code_hash);
		assert_refcount!(&code_hash, 1);
		assert_refcount!(&new_code_hash, 0);
		assert_eq!(System::events(), vec![],);

		// successful call
		assert_ok!(Contracts::set_code(RuntimeOrigin::root(), addr.clone(), new_code_hash));
		assert_eq!(get_contract(&addr).code_hash, new_code_hash);
		assert_refcount!(&code_hash, 0);
		assert_refcount!(&new_code_hash, 1);
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: RuntimeEvent::Contracts(pallet_contracts::Event::ContractCodeUpdated {
					contract: addr.clone(),
					new_code_hash,
					old_code_hash: code_hash,
				}),
				topics: vec![hash(&addr), new_code_hash, code_hash],
			},]
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
			RuntimeOrigin::signed(ALICE),
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
		// It is a corner case and we accept the destruction of the account.
		let _ = <Test as Config>::Currency::slash(
			&addr,
			<Test as Config>::Currency::total_balance(&addr),
		);

		// Sending below the minimum balance will fail the call because it needs to create the
		// account in order to send balance there.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
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
			RuntimeOrigin::signed(ALICE),
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![],
		));

		// Sending minimum balance should work
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
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
					event: RuntimeEvent::System(frame_system::Event::KilledAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Slashed {
						who: addr.clone(),
						amount: min_balance + 700
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::System(frame_system::Event::NewAccount {
						account: addr.clone()
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Endowed {
						account: addr.clone(),
						free_balance: min_balance
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Balances(pallet_balances::Event::Transfer {
						from: ALICE,
						to: addr.clone(),
						amount: min_balance
					}),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&addr)],
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
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm.clone(),
			None,
			Determinism::Deterministic
		));

		// Calling extrinsic: revert leads to an error
		assert_err_ignore_postinfo!(
			Contracts::instantiate(
				RuntimeOrigin::signed(ALICE),
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
				RuntimeOrigin::signed(ALICE),
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
		assert_eq!(result.result.data, buffer);
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
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				input.clone()
			),
			<Error<Test>>::ContractReverted,
		);

		// Calling directly: revert leads to success but the flags indicate the error
		let result = Contracts::bare_call(
			ALICE,
			addr.clone(),
			0,
			GAS_LIMIT,
			None,
			input,
			false,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_eq!(result.flags, flags);
		assert_eq!(result.data, buffer);
	});
}

#[test]
fn code_rejected_error_works() {
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		let (wasm, _) = compile_module::<Test>("invalid_module").unwrap();
		assert_noop!(
			Contracts::upload_code(
				RuntimeOrigin::signed(ALICE),
				wasm.clone(),
				None,
				Determinism::Deterministic
			),
			<Error<Test>>::CodeRejected,
		);
		let result = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(wasm),
			vec![],
			vec![],
			true,
		);
		assert_err!(result.result, <Error<Test>>::CodeRejected);
		assert_eq!(
			std::str::from_utf8(&result.debug_message).unwrap(),
			"validation of new code failed"
		);

		let (wasm, _) = compile_module::<Test>("invalid_contract").unwrap();
		assert_noop!(
			Contracts::upload_code(
				RuntimeOrigin::signed(ALICE),
				wasm.clone(),
				None,
				Determinism::Deterministic
			),
			<Error<Test>>::CodeRejected,
		);

		let result = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(wasm),
			vec![],
			vec![],
			true,
		);
		assert_err!(result.result, <Error<Test>>::CodeRejected);
		assert_eq!(
			std::str::from_utf8(&result.debug_message).unwrap(),
			"call function isn't exported"
		);
	});
}

#[test]
fn set_code_hash() {
	let (wasm, code_hash) = compile_module::<Test>("set_code_hash").unwrap();
	let (new_wasm, new_code_hash) = compile_module::<Test>("new_set_code_hash_contract").unwrap();

	let contract_addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Instantiate the 'caller'
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		// upload new code
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			new_wasm.clone(),
			None,
			Determinism::Deterministic
		));

		System::reset_events();

		// First call sets new code_hash and returns 1
		let result = Contracts::bare_call(
			ALICE,
			contract_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			new_code_hash.as_ref().to_vec(),
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_return_code!(result, 1);

		// Second calls new contract code that returns 2
		let result = Contracts::bare_call(
			ALICE,
			contract_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			vec![],
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
		assert_return_code!(result, 2);

		// Checking for the last event only
		assert_eq!(
			&System::events(),
			&[
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::ContractCodeUpdated {
						contract: contract_addr.clone(),
						new_code_hash,
						old_code_hash: code_hash,
					}),
					topics: vec![hash(&contract_addr), new_code_hash, code_hash],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: contract_addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&contract_addr)],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::Contracts(crate::Event::Called {
						caller: ALICE,
						contract: contract_addr.clone(),
					}),
					topics: vec![hash(&ALICE), hash(&contract_addr)],
				},
			],
		);
	});
}

#[test]
fn storage_deposit_limit_is_enforced() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the BOB contract has been instantiated and has the minimum balance
		assert_eq!(get_contract(&addr).total_deposit(), min_balance);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// Create 100 bytes of storage with a price of per byte
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(1)),
				100u32.to_le_bytes().to_vec()
			),
			<Error<Test>>::StorageDepositLimitExhausted,
		);
	});
}

#[test]
fn storage_deposit_limit_is_enforced_late() {
	let (wasm_caller, code_hash_caller) =
		compile_module::<Test>("create_storage_and_call").unwrap();
	let (wasm_callee, code_hash_callee) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Create both contracts: Constructors do nothing.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm_caller,
			vec![],
			vec![],
		));
		let addr_caller = Contracts::contract_address(&ALICE, &code_hash_caller, &[]);
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm_callee,
			vec![],
			vec![],
		));
		let addr_callee = Contracts::contract_address(&ALICE, &code_hash_callee, &[]);

		// Create 100 bytes of storage with a price of per byte
		// This is 100 Balance + 2 Balance for the item
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr_callee.clone(),
			0,
			GAS_LIMIT,
			Some(codec::Compact(102)),
			100u32.to_le_bytes().to_vec()
		));

		// We do not remove any storage but require 14 bytes of storage for the new
		// storage created in the immediate contract.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr_caller.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(5)),
				100u32
					.to_le_bytes()
					.as_ref()
					.iter()
					.chain(<_ as AsRef<[u8]>>::as_ref(&addr_callee))
					.cloned()
					.collect(),
			),
			<Error<Test>>::StorageDepositLimitExhausted,
		);

		// Allow for the additional 14 bytes but demand an additional byte in the callee contract.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr_caller.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(14)),
				101u32
					.to_le_bytes()
					.as_ref()
					.iter()
					.chain(<_ as AsRef<[u8]>>::as_ref(&addr_callee))
					.cloned()
					.collect(),
			),
			<Error<Test>>::StorageDepositLimitExhausted,
		);

		// Refund in the callee contract but not enough to cover the 14 balance required by the
		// caller.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr_caller.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(0)),
				87u32
					.to_le_bytes()
					.as_ref()
					.iter()
					.chain(<_ as AsRef<[u8]>>::as_ref(&addr_callee))
					.cloned()
					.collect(),
			),
			<Error<Test>>::StorageDepositLimitExhausted,
		);

		let _ = Balances::make_free_balance_be(&ALICE, 1_000);

		// Send more than the sender has balance.
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(ALICE),
				addr_caller.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(50)),
				1_200u32
					.to_le_bytes()
					.as_ref()
					.iter()
					.chain(<_ as AsRef<[u8]>>::as_ref(&addr_callee))
					.cloned()
					.collect(),
			),
			<Error<Test>>::StorageDepositLimitExhausted,
		);

		// Same as above but allow for the additional balance.
		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr_caller.clone(),
			0,
			GAS_LIMIT,
			Some(codec::Compact(1)),
			87u32
				.to_le_bytes()
				.as_ref()
				.iter()
				.chain(<_ as AsRef<[u8]>>::as_ref(&addr_callee))
				.cloned()
				.collect(),
		));
	});
}

#[test]
fn deposit_limit_honors_liquidity_restrictions() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let _ = Balances::deposit_creating(&BOB, 1_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the contract has been instantiated and has the minimum balance
		assert_eq!(get_contract(&addr).total_deposit(), min_balance);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// check that the lock ins honored
		Balances::set_lock([0; 8], &BOB, 1_000, WithdrawReasons::TRANSFER);
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(BOB),
				addr.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(200)),
				100u32.to_le_bytes().to_vec()
			),
			<Error<Test>>::StorageDepositNotEnoughFunds,
		);
		assert_eq!(Balances::free_balance(&BOB), 1_000);
	});
}

#[test]
fn deposit_limit_honors_existential_deposit() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let _ = Balances::deposit_creating(&BOB, 1_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the contract has been instantiated and has the minimum balance
		assert_eq!(get_contract(&addr).total_deposit(), min_balance);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// check that the deposit can't bring the account below the existential deposit
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(BOB),
				addr.clone(),
				0,
				GAS_LIMIT,
				Some(codec::Compact(900)),
				100u32.to_le_bytes().to_vec()
			),
			<Error<Test>>::StorageDepositNotEnoughFunds,
		);
		assert_eq!(Balances::free_balance(&BOB), 1_000);
	});
}

#[test]
fn deposit_limit_honors_min_leftover() {
	let (wasm, code_hash) = compile_module::<Test>("store").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);
		let _ = Balances::deposit_creating(&BOB, 1_000);
		let min_balance = <Test as Config>::Currency::minimum_balance();

		// Instantiate the BOB contract.
		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			0,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));
		let addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

		// Check that the contract has been instantiated and has the minimum balance
		assert_eq!(get_contract(&addr).total_deposit(), min_balance);
		assert_eq!(<Test as Config>::Currency::total_balance(&addr), min_balance);

		// check that the minumum leftover (value send) is considered
		assert_err_ignore_postinfo!(
			Contracts::call(
				RuntimeOrigin::signed(BOB),
				addr.clone(),
				400,
				GAS_LIMIT,
				Some(codec::Compact(500)),
				100u32.to_le_bytes().to_vec()
			),
			<Error<Test>>::StorageDepositNotEnoughFunds,
		);
		assert_eq!(Balances::free_balance(&BOB), 1_000);
	});
}

#[test]
fn cannot_instantiate_indeterministic_code() {
	let (wasm, code_hash) = compile_module::<Test>("float_instruction").unwrap();
	let (caller_wasm, _) = compile_module::<Test>("instantiate_return_code").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Try to instantiate directly from code
		assert_err_ignore_postinfo!(
			Contracts::instantiate_with_code(
				RuntimeOrigin::signed(ALICE),
				0,
				GAS_LIMIT,
				None,
				wasm.clone(),
				vec![],
				vec![],
			),
			<Error<Test>>::CodeRejected,
		);
		assert_err!(
			Contracts::bare_instantiate(
				ALICE,
				0,
				GAS_LIMIT,
				None,
				Code::Upload(wasm.clone()),
				vec![],
				vec![],
				false,
			)
			.result,
			<Error<Test>>::CodeRejected,
		);

		// Try to upload a non deterministic code as deterministic
		assert_err!(
			Contracts::upload_code(
				RuntimeOrigin::signed(ALICE),
				wasm.clone(),
				None,
				Determinism::Deterministic
			),
			<Error<Test>>::CodeRejected,
		);

		// Try to instantiate from already stored indeterministic code hash
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm,
			None,
			Determinism::AllowIndeterminism,
		));
		assert_err_ignore_postinfo!(
			Contracts::instantiate(
				RuntimeOrigin::signed(ALICE),
				0,
				GAS_LIMIT,
				None,
				code_hash,
				vec![],
				vec![],
			),
			<Error<Test>>::Indeterministic,
		);
		assert_err!(
			Contracts::bare_instantiate(
				ALICE,
				0,
				GAS_LIMIT,
				None,
				Code::Existing(code_hash),
				vec![],
				vec![],
				false,
			)
			.result,
			<Error<Test>>::Indeterministic,
		);

		// Deploy contract which instantiates another contract
		let addr = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(caller_wasm),
			vec![],
			vec![],
			false,
		)
		.result
		.unwrap()
		.account_id;

		// Try to instantiate `code_hash` from another contract in deterministic mode
		assert_err!(
			<Pallet<Test>>::bare_call(
				ALICE,
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				code_hash.encode(),
				false,
				Determinism::Deterministic,
			)
			.result,
			<Error<Test>>::Indeterministic,
		);

		// Instantiations are not allowed even in non determinism mode
		assert_err!(
			<Pallet<Test>>::bare_call(
				ALICE,
				addr.clone(),
				0,
				GAS_LIMIT,
				None,
				code_hash.encode(),
				false,
				Determinism::AllowIndeterminism,
			)
			.result,
			<Error<Test>>::Indeterministic,
		);
	});
}

#[test]
fn cannot_set_code_indeterministic_code() {
	let (wasm, code_hash) = compile_module::<Test>("float_instruction").unwrap();
	let (caller_wasm, _) = compile_module::<Test>("set_code_hash").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Put the non deterministic contract on-chain
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm,
			None,
			Determinism::AllowIndeterminism,
		));

		// Create the contract that will call `seal_set_code_hash`
		let caller_addr = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(caller_wasm),
			vec![],
			vec![],
			false,
		)
		.result
		.unwrap()
		.account_id;

		// We do not allow to set the code hash to a non determinstic wasm
		assert_err!(
			<Pallet<Test>>::bare_call(
				ALICE,
				caller_addr.clone(),
				0,
				GAS_LIMIT,
				None,
				code_hash.encode(),
				false,
				Determinism::AllowIndeterminism,
			)
			.result,
			<Error<Test>>::Indeterministic,
		);
	});
}

#[test]
fn delegate_call_indeterministic_code() {
	let (wasm, code_hash) = compile_module::<Test>("float_instruction").unwrap();
	let (caller_wasm, _) = compile_module::<Test>("delegate_call_simple").unwrap();
	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		// Put the non deterministic contract on-chain
		assert_ok!(Contracts::upload_code(
			RuntimeOrigin::signed(ALICE),
			wasm,
			None,
			Determinism::AllowIndeterminism,
		));

		// Create the contract that will call `seal_delegate_call`
		let caller_addr = Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(caller_wasm),
			vec![],
			vec![],
			false,
		)
		.result
		.unwrap()
		.account_id;

		// The delegate call will fail in deterministic mode
		assert_err!(
			<Pallet<Test>>::bare_call(
				ALICE,
				caller_addr.clone(),
				0,
				GAS_LIMIT,
				None,
				code_hash.encode(),
				false,
				Determinism::Deterministic,
			)
			.result,
			<Error<Test>>::Indeterministic,
		);

		// The delegate call will work on non deterministic mode
		assert_ok!(
			<Pallet<Test>>::bare_call(
				ALICE,
				caller_addr.clone(),
				0,
				GAS_LIMIT,
				None,
				code_hash.encode(),
				false,
				Determinism::AllowIndeterminism,
			)
			.result
		);
	});
}

#[test]
fn reentrance_count_works_with_call() {
	let (wasm, code_hash) = compile_module::<Test>("reentrance_count_call").unwrap();
	let contract_addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));

		// passing reentrant count to the input
		let input = 0.encode();

		Contracts::bare_call(
			ALICE,
			contract_addr,
			0,
			GAS_LIMIT,
			None,
			input,
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
	});
}

#[test]
fn reentrance_count_works_with_delegated_call() {
	let (wasm, code_hash) = compile_module::<Test>("reentrance_count_delegated_call").unwrap();
	let contract_addr = Contracts::contract_address(&ALICE, &code_hash, &[]);

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));

		// adding a callstack height to the input
		let input = (code_hash, 1).encode();

		Contracts::bare_call(
			ALICE,
			contract_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			input,
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();
	});
}

#[test]
fn account_reentrance_count_works() {
	let (wasm, code_hash) = compile_module::<Test>("account_reentrance_count_call").unwrap();
	let (wasm_reentrance_count, code_hash_reentrance_count) =
		compile_module::<Test>("reentrance_count_call").unwrap();

	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			wasm,
			vec![],
			vec![],
		));

		assert_ok!(Contracts::instantiate_with_code(
			RuntimeOrigin::signed(ALICE),
			300_000,
			GAS_LIMIT,
			None,
			wasm_reentrance_count,
			vec![],
			vec![]
		));

		let contract_addr = Contracts::contract_address(&ALICE, &code_hash, &[]);
		let another_contract_addr =
			Contracts::contract_address(&ALICE, &code_hash_reentrance_count, &[]);

		let result1 = Contracts::bare_call(
			ALICE,
			contract_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			contract_addr.encode(),
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();

		let result2 = Contracts::bare_call(
			ALICE,
			contract_addr.clone(),
			0,
			GAS_LIMIT,
			None,
			another_contract_addr.encode(),
			true,
			Determinism::Deterministic,
		)
		.result
		.unwrap();

		assert_eq!(result1.data, 1.encode());
		assert_eq!(result2.data, 0.encode());
	});
}
