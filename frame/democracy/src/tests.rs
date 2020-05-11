// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! The crate's tests.

use super::*;
use std::cell::RefCell;
use codec::Encode;
use frame_support::{
	impl_outer_origin, impl_outer_dispatch, assert_noop, assert_ok, parameter_types,
	impl_outer_event, ord_parameter_types, traits::{Contains, OnInitialize}, weights::Weight,
};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup, BadOrigin},
	testing::Header, Perbill,
};
use pallet_balances::{BalanceLock, Error as BalancesError};
use frame_system::EnsureSignedBy;

mod cancellation;
mod delegation;
mod external_proposing;
mod fast_tracking;
mod lock_voting;
mod preimage;
mod proxying;
mod public_proposals;
mod scheduling;
mod voting;

const AYE: Vote = Vote { aye: true, conviction: Conviction::None };
const NAY: Vote = Vote { aye: false, conviction: Conviction::None };
const BIG_AYE: Vote = Vote { aye: true, conviction: Conviction::Locked1x };
const BIG_NAY: Vote = Vote { aye: false, conviction: Conviction::Locked1x };

impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		frame_system::System,
		pallet_balances::Balances,
		democracy::Democracy,
	}
}

mod democracy {
	pub use crate::Event;
}

impl_outer_event! {
	pub enum Event for Test {
		system<T>,
		pallet_balances<T>,
		pallet_scheduler<T>,
		democracy<T>,
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1_000_000;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
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
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
parameter_types! {
	pub const MaximumSchedulerWeight: Weight = Perbill::from_percent(80) * MaximumBlockWeight::get();
}
impl pallet_scheduler::Trait for Test {
	type Event = Event;
	type Origin = Origin;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}
parameter_types! {
	pub const LaunchPeriod: u64 = 2;
	pub const VotingPeriod: u64 = 2;
	pub const FastTrackVotingPeriod: u64 = 2;
	pub const MinimumDeposit: u64 = 1;
	pub const EnactmentPeriod: u64 = 2;
	pub const CooloffPeriod: u64 = 2;
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
impl Contains<u64> for OneToFive {
	fn sorted_members() -> Vec<u64> {
		vec![1, 2, 3, 4, 5]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}
thread_local! {
	static PREIMAGE_BYTE_DEPOSIT: RefCell<u64> = RefCell::new(0);
	static INSTANT_ALLOWED: RefCell<bool> = RefCell::new(false);
}
pub struct PreimageByteDeposit;
impl Get<u64> for PreimageByteDeposit {
	fn get() -> u64 { PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow()) }
}
pub struct InstantAllowed;
impl Get<bool> for InstantAllowed {
	fn get() -> bool { INSTANT_ALLOWED.with(|v| *v.borrow()) }
}
impl super::Trait for Test {
	type Proposal = Call;
	type Event = Event;
	type Currency = pallet_balances::Module<Self>;
	type EnactmentPeriod = EnactmentPeriod;
	type LaunchPeriod = LaunchPeriod;
	type VotingPeriod = VotingPeriod;
	type FastTrackVotingPeriod = FastTrackVotingPeriod;
	type MinimumDeposit = MinimumDeposit;
	type ExternalOrigin = EnsureSignedBy<Two, u64>;
	type ExternalMajorityOrigin = EnsureSignedBy<Three, u64>;
	type ExternalDefaultOrigin = EnsureSignedBy<One, u64>;
	type FastTrackOrigin = EnsureSignedBy<Five, u64>;
	type CancellationOrigin = EnsureSignedBy<Four, u64>;
	type VetoOrigin = EnsureSignedBy<OneToFive, u64>;
	type CooloffPeriod = CooloffPeriod;
	type PreimageByteDeposit = PreimageByteDeposit;
	type Slash = ();
	type InstantOrigin = EnsureSignedBy<Six, u64>;
	type InstantAllowed = InstantAllowed;
	type Scheduler = Scheduler;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
	}.assimilate_storage(&mut t).unwrap();
	GenesisConfig::default().assimilate_storage(&mut t).unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Scheduler = pallet_scheduler::Module<Test>;
type Democracy = Module<Test>;

#[test]
fn params_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Democracy::referendum_count(), 0);
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);
	});
}

fn set_balance_proposal(value: u64) -> Vec<u8> {
	Call::Balances(pallet_balances::Call::set_balance(42, value, 0)).encode()
}

fn set_balance_proposal_hash(value: u64) -> H256 {
	BlakeTwo256::hash(&set_balance_proposal(value)[..])
}

fn set_balance_proposal_hash_and_note(value: u64) -> H256 {
	let p = set_balance_proposal(value);
	let h = BlakeTwo256::hash(&p[..]);
	match Democracy::note_preimage(Origin::signed(6), p) {
		Ok(_) => (),
		Err(x) if x == Error::<Test>::DuplicatePreimage.into() => (),
		Err(x) => panic!(x),
	}
	h
}

fn propose_set_balance(who: u64, value: u64, delay: u64) -> DispatchResult {
	Democracy::propose(
		Origin::signed(who),
		set_balance_proposal_hash(value),
		delay
	)
}

fn propose_set_balance_and_note(who: u64, value: u64, delay: u64) -> DispatchResult {
	Democracy::propose(
		Origin::signed(who),
		set_balance_proposal_hash_and_note(value),
		delay
	)
}

fn next_block() {
	System::set_block_number(System::block_number() + 1);
	Scheduler::on_initialize(System::block_number());
	assert_eq!(Democracy::begin_block(System::block_number()), Ok(()));
}

fn fast_forward_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

fn begin_referendum() -> ReferendumIndex {
	System::set_block_number(0);
	assert_ok!(propose_set_balance_and_note(1, 2, 1));
	fast_forward_to(2);
	0
}

fn aye(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: AYE, balance: Balances::free_balance(&who) }
}

fn nay(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: NAY, balance: Balances::free_balance(&who) }
}

fn big_aye(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: BIG_AYE, balance: Balances::free_balance(&who) }
}

fn big_nay(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: BIG_NAY, balance: Balances::free_balance(&who) }
}

fn tally(r: ReferendumIndex) -> Tally<u64> {
	Democracy::referendum_status(r).unwrap().tally
}
