// Copyright 2019 Parity Technologies (UK) Ltd.
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

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput, black_box};

use pallet_contracts::{
	self as contracts,
	ComputeDispatchFee, ContractAddressFor, TrieId, Schedule, TrieIdGenerator, AccountCounter,
	GenesisConfig,
};
use sr_primitives::{
	Perbill,
	traits::{BlakeTwo256, IdentityLookup},
	testing::{Header, H256},
};
use support::{
	assert_ok, impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
	StorageValue, traits::{Currency, Get},
};
use std::cell::RefCell;
use system;

impl_outer_event! {
	pub enum MetaEvent for Test {
		balances<T>, contracts<T>,
	}
}
impl_outer_origin! {
	pub enum Origin for Test { }
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
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl system::Trait for Test {
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
}
impl balances::Trait for Test {
	type Balance = u64;
	type OnFreeBalanceZero = Contract;
	type OnNewAccount = ();
	type Event = MetaEvent;
	type DustRemoval = ();
	type TransferPayment = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
}
parameter_types! {
	pub const MinimumPeriod: u64 = 1;
}
impl timestamp::Trait for Test {
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
impl contracts::Trait for Test {
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
	type TransferFee = TransferFee;
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

type Balances = balances::Module<Test>;
type Timestamp = timestamp::Module<Test>;
type Contract = contracts::Module<Test>;
type Randomness = randomness_collective_flip::Module<Test>;

pub struct DummyContractAddressFor;
impl ContractAddressFor<H256, u64> for DummyContractAddressFor {
	fn contract_address_for(_code_hash: &H256, _data: &[u8], origin: &u64) -> u64 {
		*origin + 1
	}
}

pub struct DummyTrieIdGenerator;
impl TrieIdGenerator<u64> for DummyTrieIdGenerator {
	fn trie_id(account_id: &u64) -> TrieId {
		use primitives::storage::well_known_keys;

		let new_seed = AccountCounter::mutate(|v| {
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
	fn compute_dispatch_fee(_: &Call) -> u64 {
		69
	}
}

const ALICE: u64 = 1;
const GAS_PRICE: u64 = 2;

fn test_externalities() -> runtime_io::TestExternalities {
	EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = 0);
	TRANSFER_FEE.with(|v| *v.borrow_mut() = 0);
	INSTANTIATION_FEE.with(|v| *v.borrow_mut() = 0);
	BLOCK_GAS_LIMIT.with(|v| *v.borrow_mut() = GAS_PRICE);

	let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	balances::GenesisConfig::<Test> {
		balances: vec![],
		vesting: vec![],
	}.assimilate_storage(&mut t).unwrap();
	GenesisConfig::<Test> {
		current_schedule: Schedule {
			enable_println: true,
			..Default::default()
		},
		gas_price: GAS_PRICE,
	}.assimilate_storage(&mut t).unwrap();
	runtime_io::TestExternalities::new(t)
}

const WASMS: &[(&str, &[u8])] = &[
	("flipper.wasm",			include_bytes!("wasms/flipper.wasm")),
	("erc20.wasm",				include_bytes!("wasms/erc20.wasm")),
	("erc721.wasm",				include_bytes!("wasms/erc721.wasm")),
	("events.wasm",				include_bytes!("wasms/events.wasm")),
	("delegator.wasm",			include_bytes!("wasms/delegator.wasm")),
	("incrementer.wasm",		include_bytes!("wasms/incrementer.wasm")),
	("runtime_storage.wasm",	include_bytes!("wasms/runtime_storage.wasm")),
	("shared_vec.wasm",			include_bytes!("wasms/shared_vec.wasm")),
];

fn test_flipper(c: &mut Criterion) {
	let mut group = c.benchmark_group("wasms");

	test_externalities().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000_000_000);

		for (name, bytes) in WASMS {
			group.throughput(Throughput::Bytes(bytes.len() as u64));

			group.bench_function(BenchmarkId::from_parameter(name), |b| {
				b.iter(|| {
					assert_ok!(Contract::put_code(
						Origin::signed(ALICE),
						100_000,
						black_box(bytes.to_vec())
					));
				})
			});
		}
	});
}

criterion_group!{
    name = benches;
    config = Criterion::default();
    targets = test_flipper
}

criterion_main!(benches);
