// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Scheduler test environment.

use super::*;

use crate as scheduler;
use frame_support::{
	ord_parameter_types, parameter_types,
	traits::{
		ConstU32, ConstU64, Contains, EnsureOneOf, EqualPrivilegeOnly, OnFinalize, OnInitialize,
	},
	weights::constants::RocksDbWeight,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	Perbill,
};

// Logger module to track execution.
#[frame_support::pallet]
pub mod logger {
	use super::{OriginCaller, OriginTrait};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use std::cell::RefCell;

	thread_local! {
		static LOG: RefCell<Vec<(OriginCaller, u32)>> = RefCell::new(Vec::new());
	}
	pub fn log() -> Vec<(OriginCaller, u32)> {
		LOG.with(|log| log.borrow().clone())
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Logged(u32, Weight),
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		<T as frame_system::Config>::Origin: OriginTrait<PalletsOrigin = OriginCaller>,
	{
		#[pallet::weight(*weight)]
		pub fn log(origin: OriginFor<T>, i: u32, weight: Weight) -> DispatchResult {
			Self::deposit_event(Event::Logged(i, weight));
			LOG.with(|log| {
				log.borrow_mut().push((origin.caller().clone(), i));
			});
			Ok(())
		}

		#[pallet::weight(*weight)]
		pub fn log_without_filter(origin: OriginFor<T>, i: u32, weight: Weight) -> DispatchResult {
			Self::deposit_event(Event::Logged(i, weight));
			LOG.with(|log| {
				log.borrow_mut().push((origin.caller().clone(), i));
			});
			Ok(())
		}
	}
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Logger: logger::{Pallet, Call, Event<T>},
		Scheduler: scheduler::{Pallet, Call, Storage, Event<T>},
		Preimage: pallet_preimage::{Pallet, Call, Storage, Event<T>},
	}
);

// Scheduler must dispatch with root and no filter, this tests base filter is indeed not used.
pub struct BaseFilter;
impl Contains<Call> for BaseFilter {
	fn contains(call: &Call) -> bool {
		!matches!(call, Call::Logger(LoggerCall::log { .. }))
	}
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(2_000_000_000_000);
}
impl system::Config for Test {
	type BaseCallFilter = BaseFilter;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = RocksDbWeight;
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}
impl logger::Config for Test {
	type Event = Event;
}
parameter_types! {
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) * BlockWeights::get().max_block;
	pub const NoPreimagePostponement: Option<u64> = Some(2);
}
ord_parameter_types! {
	pub const One: u64 = 1;
}

impl pallet_preimage::Config for Test {
	type Event = Event;
	type WeightInfo = ();
	type Currency = ();
	type ManagerOrigin = EnsureRoot<u64>;
	type MaxSize = ConstU32<1024>;
	type BaseDeposit = ();
	type ByteDeposit = ();
}

impl Config for Test {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = EnsureOneOf<EnsureRoot<u64>, EnsureSignedBy<One, u64>>;
	type MaxScheduledPerBlock = ConstU32<10>;
	type WeightInfo = ();
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
	type PreimageProvider = Preimage;
	type NoPreimagePostponement = NoPreimagePostponement;
}

pub type LoggerCall = logger::Call<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	t.into()
}

pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		Scheduler::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		Scheduler::on_initialize(System::block_number());
	}
}

pub fn root() -> OriginCaller {
	system::RawOrigin::Root.into()
}
