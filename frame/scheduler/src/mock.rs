// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
		ConstU32, ConstU64, Contains, EitherOfDiverse, EqualPrivilegeOnly, OnFinalize, OnInitialize,
	},
	weights::constants::RocksDbWeight,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage, Perbill,
};

// Logger module to track execution.
#[frame_support::pallet]
pub mod logger {
	use super::{OriginCaller, OriginTrait};
	use frame_support::{pallet_prelude::*, parameter_types};
	use frame_system::pallet_prelude::*;

	parameter_types! {
		static Log: Vec<(OriginCaller, u32)> = Vec::new();
	}
	pub fn log() -> Vec<(OriginCaller, u32)> {
		Log::get().clone()
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Logged(u32, Weight),
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		<T as frame_system::Config>::RuntimeOrigin: OriginTrait<PalletsOrigin = OriginCaller>,
	{
		#[pallet::call_index(0)]
		#[pallet::weight(*weight)]
		pub fn log(origin: OriginFor<T>, i: u32, weight: Weight) -> DispatchResult {
			Self::deposit_event(Event::Logged(i, weight));
			Log::mutate(|log| {
				log.push((origin.caller().clone(), i));
			});
			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(*weight)]
		pub fn log_without_filter(origin: OriginFor<T>, i: u32, weight: Weight) -> DispatchResult {
			Self::deposit_event(Event::Logged(i, weight));
			Log::mutate(|log| {
				log.push((origin.caller().clone(), i));
			});
			Ok(())
		}
	}
}

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Logger: logger::{Pallet, Call, Event<T>},
		Scheduler: scheduler::{Pallet, Call, Storage, Event<T>},
		Preimage: pallet_preimage::{Pallet, Call, Storage, Event<T>},
	}
);

// Scheduler must dispatch with root and no filter, this tests base filter is indeed not used.
pub struct BaseFilter;
impl Contains<RuntimeCall> for BaseFilter {
	fn contains(call: &RuntimeCall) -> bool {
		!matches!(call, RuntimeCall::Logger(LoggerCall::log { .. }))
	}
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(
			Weight::from_parts(2_000_000_000_000, u64::MAX),
		);
}
impl system::Config for Test {
	type BaseCallFilter = BaseFilter;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = RocksDbWeight;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Nonce = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
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
	type RuntimeEvent = RuntimeEvent;
}
ord_parameter_types! {
	pub const One: u64 = 1;
}

impl pallet_preimage::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type Currency = ();
	type ManagerOrigin = EnsureRoot<u64>;
	type BaseDeposit = ();
	type ByteDeposit = ();
}

pub struct TestWeightInfo;
impl WeightInfo for TestWeightInfo {
	fn service_agendas_base() -> Weight {
		Weight::from_parts(0b0000_0001, 0)
	}
	fn service_agenda_base(i: u32) -> Weight {
		Weight::from_parts((i << 8) as u64 + 0b0000_0010, 0)
	}
	fn service_task_base() -> Weight {
		Weight::from_parts(0b0000_0100, 0)
	}
	fn service_task_periodic() -> Weight {
		Weight::from_parts(0b0000_1100, 0)
	}
	fn service_task_named() -> Weight {
		Weight::from_parts(0b0001_0100, 0)
	}
	fn service_task_fetched(s: u32) -> Weight {
		Weight::from_parts((s << 8) as u64 + 0b0010_0100, 0)
	}
	fn execute_dispatch_signed() -> Weight {
		Weight::from_parts(0b0100_0000, 0)
	}
	fn execute_dispatch_unsigned() -> Weight {
		Weight::from_parts(0b1000_0000, 0)
	}
	fn schedule(_s: u32) -> Weight {
		Weight::from_parts(50, 0)
	}
	fn cancel(_s: u32) -> Weight {
		Weight::from_parts(50, 0)
	}
	fn schedule_named(_s: u32) -> Weight {
		Weight::from_parts(50, 0)
	}
	fn cancel_named(_s: u32) -> Weight {
		Weight::from_parts(50, 0)
	}
}
parameter_types! {
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) *
		BlockWeights::get().max_block;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
	type PalletsOrigin = OriginCaller;
	type RuntimeCall = RuntimeCall;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = EitherOfDiverse<EnsureRoot<u64>, EnsureSignedBy<One, u64>>;
	type MaxScheduledPerBlock = ConstU32<10>;
	type WeightInfo = TestWeightInfo;
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
	type Preimages = Preimage;
}

pub type LoggerCall = logger::Call<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
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
