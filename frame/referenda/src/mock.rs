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

//! The crate's tests.

use super::*;
use crate as pallet_referenda;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	assert_ok, ord_parameter_types, parameter_types,
	traits::{
		ConstU32, ConstU64, Contains, EqualPrivilegeOnly, OnInitialize, OriginTrait, Polling,
		PreimageRecipient, SortedMembers,
	},
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, Hash, IdentityLookup},
	DispatchResult, Perbill,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		Preimage: pallet_preimage,
		Scheduler: pallet_scheduler,
		Referenda: pallet_referenda,
	}
);

// Test that a fitlered call can be dispatched.
pub struct BaseFilter;
impl Contains<Call> for BaseFilter {
	fn contains(call: &Call) -> bool {
		!matches!(call, &Call::Balances(pallet_balances::Call::set_balance { .. }))
	}
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1_000_000);
}
impl frame_system::Config for Test {
	type BaseCallFilter = BaseFilter;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
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
	type MaxConsumers = ConstU32<16>;
}
impl pallet_preimage::Config for Test {
	type Event = Event;
	type WeightInfo = ();
	type Currency = Balances;
	type ManagerOrigin = EnsureRoot<u64>;
	type MaxSize = ConstU32<4096>;
	type BaseDeposit = ();
	type ByteDeposit = ();
}
impl pallet_scheduler::Config for Test {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = ConstU64<2_000_000_000_000>;
	type ScheduleOrigin = EnsureRoot<u64>;
	type MaxScheduledPerBlock = ConstU32<100>;
	type WeightInfo = ();
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
	type PreimageProvider = Preimage;
	type NoPreimagePostponement = ConstU64<10>;
}
impl pallet_balances::Config for Test {
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type MaxLocks = ConstU32<10>;
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub static AlarmInterval: u64 = 1;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
	pub const Three: u64 = 3;
	pub const Four: u64 = 4;
	pub const Five: u64 = 5;
	pub const Six: u64 = 6;
}
pub struct OneToFive;
impl SortedMembers<u64> for OneToFive {
	fn sorted_members() -> Vec<u64> {
		vec![1, 2, 3, 4, 5]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}

pub struct TestTracksInfo;
impl TracksInfo<u64, u64> for TestTracksInfo {
	type Id = u8;
	type Origin = <Origin as OriginTrait>::PalletsOrigin;
	fn tracks() -> &'static [(Self::Id, TrackInfo<u64, u64>)] {
		static DATA: [(u8, TrackInfo<u64, u64>); 2] = [
			(
				0u8,
				TrackInfo {
					name: "root",
					max_deciding: 1,
					decision_deposit: 10,
					prepare_period: 4,
					decision_period: 4,
					confirm_period: 2,
					min_enactment_period: 4,
					min_approval: Curve::LinearDecreasing {
						begin: Perbill::from_percent(100),
						delta: Perbill::from_percent(50),
					},
					min_turnout: Curve::LinearDecreasing {
						begin: Perbill::from_percent(100),
						delta: Perbill::from_percent(100),
					},
				},
			),
			(
				1u8,
				TrackInfo {
					name: "none",
					max_deciding: 3,
					decision_deposit: 1,
					prepare_period: 2,
					decision_period: 2,
					confirm_period: 1,
					min_enactment_period: 2,
					min_approval: Curve::LinearDecreasing {
						begin: Perbill::from_percent(55),
						delta: Perbill::from_percent(5),
					},
					min_turnout: Curve::LinearDecreasing {
						begin: Perbill::from_percent(10),
						delta: Perbill::from_percent(10),
					},
				},
			),
		];
		&DATA[..]
	}
	fn track_for(id: &Self::Origin) -> Result<Self::Id, ()> {
		if let Ok(system_origin) = frame_system::RawOrigin::try_from(id.clone()) {
			match system_origin {
				frame_system::RawOrigin::Root => Ok(0),
				frame_system::RawOrigin::None => Ok(1),
				_ => Err(()),
			}
		} else {
			Err(())
		}
	}
}

impl Config for Test {
	type WeightInfo = ();
	type Call = Call;
	type Event = Event;
	type Scheduler = Scheduler;
	type Currency = pallet_balances::Pallet<Self>;
	type CancelOrigin = EnsureSignedBy<Four, u64>;
	type KillOrigin = EnsureRoot<u64>;
	type Slash = ();
	type Votes = u32;
	type Tally = Tally;
	type SubmissionDeposit = ConstU64<2>;
	type MaxQueued = ConstU32<3>;
	type UndecidingTimeout = ConstU64<20>;
	type AlarmInterval = AlarmInterval;
	type Tracks = TestTracksInfo;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let balances = vec![(1, 100), (2, 100), (3, 100), (4, 100), (5, 100), (6, 100)];
	pallet_balances::GenesisConfig::<Test> { balances }
		.assimilate_storage(&mut t)
		.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

/// Execute the function two times, with `true` and with `false`.
#[allow(dead_code)]
pub fn new_test_ext_execute_with_cond(execute: impl FnOnce(bool) -> () + Clone) {
	new_test_ext().execute_with(|| (execute.clone())(false));
	new_test_ext().execute_with(|| execute(true));
}

#[derive(Encode, Debug, Decode, TypeInfo, Eq, PartialEq, Clone, Default, MaxEncodedLen)]
pub struct Tally {
	pub ayes: u32,
	pub nays: u32,
}

impl VoteTally<u32> for Tally {
	fn ayes(&self) -> u32 {
		self.ayes
	}

	fn turnout(&self) -> Perbill {
		Perbill::from_percent(self.ayes + self.nays)
	}

	fn approval(&self) -> Perbill {
		Perbill::from_rational(self.ayes, self.ayes + self.nays)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn unanimity() -> Self {
		Self { ayes: 100, nays: 0 }
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn from_requirements(turnout: Perbill, approval: Perbill) -> Self {
		let turnout = turnout.mul_ceil(100u32);
		let ayes = approval.mul_ceil(turnout);
		Self { ayes, nays: turnout - ayes }
	}
}

pub fn set_balance_proposal(value: u64) -> Vec<u8> {
	Call::Balances(pallet_balances::Call::set_balance { who: 42, new_free: value, new_reserved: 0 })
		.encode()
}

pub fn set_balance_proposal_hash(value: u64) -> H256 {
	let c = Call::Balances(pallet_balances::Call::set_balance {
		who: 42,
		new_free: value,
		new_reserved: 0,
	});
	<Preimage as PreimageRecipient<_>>::note_preimage(c.encode().try_into().unwrap());
	BlakeTwo256::hash_of(&c)
}

#[allow(dead_code)]
pub fn propose_set_balance(who: u64, value: u64, delay: u64) -> DispatchResult {
	Referenda::submit(
		Origin::signed(who),
		frame_system::RawOrigin::Root.into(),
		set_balance_proposal_hash(value),
		DispatchTime::After(delay),
	)
}

pub fn next_block() {
	System::set_block_number(System::block_number() + 1);
	Scheduler::on_initialize(System::block_number());
}

pub fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

#[allow(dead_code)]
pub fn begin_referendum() -> ReferendumIndex {
	System::set_block_number(0);
	assert_ok!(propose_set_balance(1, 2, 1));
	run_to(2);
	0
}

#[allow(dead_code)]
pub fn tally(r: ReferendumIndex) -> Tally {
	Referenda::ensure_ongoing(r).unwrap().tally
}

pub fn set_tally(index: ReferendumIndex, ayes: u32, nays: u32) {
	<Referenda as Polling<Tally>>::access_poll(index, |status| {
		let tally = status.ensure_ongoing().unwrap().0;
		tally.ayes = ayes;
		tally.nays = nays;
	});
}

pub fn waiting_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Ongoing(ReferendumStatus { submitted, deciding: None, .. }) => submitted,
		_ => panic!("Not waiting"),
	}
}

pub fn deciding_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Ongoing(ReferendumStatus {
			deciding: Some(DecidingStatus { since, .. }),
			..
		}) => since,
		_ => panic!("Not deciding"),
	}
}

pub fn deciding_and_failing_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Ongoing(ReferendumStatus {
			deciding: Some(DecidingStatus { since, confirming: None, .. }),
			..
		}) => since,
		_ => panic!("Not deciding"),
	}
}

pub fn confirming_until(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Ongoing(ReferendumStatus {
			deciding: Some(DecidingStatus { confirming: Some(until), .. }),
			..
		}) => until,
		_ => panic!("Not confirming"),
	}
}

pub fn approved_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Approved(since, ..) => since,
		_ => panic!("Not approved"),
	}
}

pub fn rejected_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Rejected(since, ..) => since,
		_ => panic!("Not rejected"),
	}
}

pub fn cancelled_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Cancelled(since, ..) => since,
		_ => panic!("Not cancelled"),
	}
}

pub fn killed_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::Killed(since, ..) => since,
		_ => panic!("Not killed"),
	}
}

pub fn timed_out_since(i: ReferendumIndex) -> u64 {
	match ReferendumInfoFor::<Test>::get(i).unwrap() {
		ReferendumInfo::TimedOut(since, ..) => since,
		_ => panic!("Not timed out"),
	}
}

fn is_deciding(i: ReferendumIndex) -> bool {
	matches!(
		ReferendumInfoFor::<Test>::get(i),
		Some(ReferendumInfo::Ongoing(ReferendumStatus { deciding: Some(_), .. }))
	)
}

#[derive(Clone, Copy)]
pub enum RefState {
	Failing,
	Passing,
	Confirming { immediate: bool },
}

impl RefState {
	pub fn create(self) -> ReferendumIndex {
		assert_ok!(Referenda::submit(
			Origin::signed(1),
			frame_support::dispatch::RawOrigin::Root.into(),
			set_balance_proposal_hash(1),
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::place_decision_deposit(Origin::signed(2), 0));
		if matches!(self, RefState::Confirming { immediate: true }) {
			set_tally(0, 100, 0);
		}
		let index = ReferendumCount::<Test>::get() - 1;
		while !is_deciding(index) {
			run_to(System::block_number() + 1);
		}
		if matches!(self, RefState::Confirming { immediate: false }) {
			set_tally(0, 100, 0);
			run_to(System::block_number() + 1);
		}
		if matches!(self, RefState::Confirming { .. }) {
			assert_eq!(confirming_until(index), System::block_number() + 2);
		}
		if matches!(self, RefState::Passing) {
			set_tally(0, 100, 99);
			run_to(System::block_number() + 1);
		}
		index
	}
}
