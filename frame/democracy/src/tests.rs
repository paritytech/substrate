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
	ord_parameter_types, traits::Contains, weights::Weight,
};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup, Bounded, BadOrigin},
	testing::Header, Perbill,
};
use pallet_balances::{BalanceLock, Error as BalancesError};
use frame_system::EnsureSignedBy;

const AYE: Vote = Vote{ aye: true, conviction: Conviction::None };
const NAY: Vote = Vote{ aye: false, conviction: Conviction::None };
const BIG_AYE: Vote = Vote{ aye: true, conviction: Conviction::Locked1x };
const BIG_NAY: Vote = Vote{ aye: false, conviction: Conviction::Locked1x };

impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		pallet_balances::Balances,
		democracy::Democracy,
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}
parameter_types! {
	pub const LaunchPeriod: u64 = 2;
	pub const VotingPeriod: u64 = 2;
	pub const FastTrackVotingPeriod: u64 = 1;
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
}
pub struct OneToFive;
impl Contains<u64> for OneToFive {
	fn sorted_members() -> Vec<u64> {
		vec![1, 2, 3, 4, 5]
	}
}
thread_local! {
	static PREIMAGE_BYTE_DEPOSIT: RefCell<u64> = RefCell::new(0);
}
pub struct PreimageByteDeposit;
impl Get<u64> for PreimageByteDeposit {
	fn get() -> u64 { PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow()) }
}
impl super::Trait for Test {
	type Proposal = Call;
	type Event = ();
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
}

fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
	}.assimilate_storage(&mut t).unwrap();
	GenesisConfig::default().assimilate_storage(&mut t).unwrap();
	sp_io::TestExternalities::new(t)
}

type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
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
	assert_eq!(Democracy::begin_block(System::block_number()), Ok(()));
}

fn fast_forward_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

#[test]
fn missing_preimage_should_fail() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn preimage_deposit_should_be_required_and_returned() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		// fee of 100 is too much.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 100);
		assert_noop!(
			Democracy::note_preimage(Origin::signed(6), vec![0; 500]),
			BalancesError::<Test, _>::InsufficientBalance,
		);
		// fee of 1 is reasonable.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		next_block();

		assert_eq!(Balances::reserved_balance(6), 0);
		assert_eq!(Balances::free_balance(6), 60);
		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn preimage_deposit_should_be_reapable_earlier_by_owner() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));

		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)),
			Error::<Test>::Early
		);
		next_block();
		assert_ok!(Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)));

		assert_eq!(Balances::free_balance(6), 60);
		assert_eq!(Balances::reserved_balance(6), 0);
	});
}

#[test]
fn preimage_deposit_should_be_reapable() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
			Error::<Test>::PreimageMissing
		);

		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));
		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		next_block();
		next_block();
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
			Error::<Test>::Early
		);

		next_block();
		assert_ok!(Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)));
		assert_eq!(Balances::reserved_balance(6), 0);
		assert_eq!(Balances::free_balance(6), 48);
		assert_eq!(Balances::free_balance(5), 62);
	});
}

#[test]
fn noting_imminent_preimage_for_free_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			1
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		assert_noop!(
			Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)),
			Error::<Test>::NotImminent
		);

		next_block();

		// Now we're in the dispatch queue it's all good.
		assert_ok!(Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)));

		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn reaping_imminent_preimage_should_fail() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let h = set_balance_proposal_hash_and_note(2);
		let r = Democracy::inject_referendum(3, h, VoteThreshold::SuperMajorityApprove, 1);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		next_block();
		next_block();
		// now imminent.
		assert_noop!(Democracy::reap_preimage(Origin::signed(6), h), Error::<Test>::Imminent);
	});
}

#[test]
fn external_and_public_interleaving_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(1),
		));
		assert_ok!(propose_set_balance_and_note(6, 2, 2));

		fast_forward_to(2);

		// both waiting: external goes first.
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(1),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		// replenish external
		assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(3),
			));

		fast_forward_to(4);

		// both waiting: public goes next.
		assert_eq!(
			Democracy::referendum_info(1),
			Some(ReferendumInfo {
				end: 6,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		// don't replenish public

		fast_forward_to(6);

		// it's external "turn" again, though since public is empty that doesn't really matter
		assert_eq!(
			Democracy::referendum_info(2),
			Some(ReferendumInfo {
				end: 8,
				proposal_hash: set_balance_proposal_hash_and_note(3),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		// replenish external
		assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(5),
			));

		fast_forward_to(8);

		// external goes again because there's no public waiting.
		assert_eq!(
			Democracy::referendum_info(3),
			Some(ReferendumInfo {
				end: 10,
				proposal_hash: set_balance_proposal_hash_and_note(5),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		// replenish both
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(7),
		));
		assert_ok!(propose_set_balance_and_note(6, 4, 2));

		fast_forward_to(10);

		// public goes now since external went last time.
		assert_eq!(
			Democracy::referendum_info(4),
			Some(ReferendumInfo {
				end: 12,
				proposal_hash: set_balance_proposal_hash_and_note(4),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		// replenish public again
		assert_ok!(propose_set_balance_and_note(6, 6, 2));
		// cancel external
		let h = set_balance_proposal_hash_and_note(7);
		assert_ok!(Democracy::veto_external(Origin::signed(3), h));

		fast_forward_to(12);

		// public goes again now since there's no external waiting.
		assert_eq!(
			Democracy::referendum_info(5),
			Some(ReferendumInfo {
				end: 14,
				proposal_hash: set_balance_proposal_hash_and_note(6),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
	});
}


#[test]
fn emergency_cancel_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			2
		);
		assert!(Democracy::referendum_info(r).is_some());

		assert_noop!(Democracy::emergency_cancel(Origin::signed(3), r), BadOrigin);
		assert_ok!(Democracy::emergency_cancel(Origin::signed(4), r));
		assert!(Democracy::referendum_info(r).is_none());

		// some time later...

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			2
		);
		assert!(Democracy::referendum_info(r).is_some());
		assert_noop!(Democracy::emergency_cancel(Origin::signed(4), r), Error::<Test>::AlreadyCanceled);
	});
}

#[test]
fn veto_external_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(2),
		));
		assert!(<NextExternal<Test>>::exists());

		let h = set_balance_proposal_hash_and_note(2);
		assert_ok!(Democracy::veto_external(Origin::signed(3), h.clone()));
		// cancelled.
		assert!(!<NextExternal<Test>>::exists());
		// fails - same proposal can't be resubmitted.
		assert_noop!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash(2),
		), Error::<Test>::ProposalBlacklisted);

		fast_forward_to(1);
		// fails as we're still in cooloff period.
		assert_noop!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash(2),
		), Error::<Test>::ProposalBlacklisted);

		fast_forward_to(2);
		// works; as we're out of the cooloff period.
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(2),
		));
		assert!(<NextExternal<Test>>::exists());

		// 3 can't veto the same thing twice.
		assert_noop!(
			Democracy::veto_external(Origin::signed(3), h.clone()),
			Error::<Test>::AlreadyVetoed
		);

		// 4 vetoes.
		assert_ok!(Democracy::veto_external(Origin::signed(4), h.clone()));
		// cancelled again.
		assert!(!<NextExternal<Test>>::exists());

		fast_forward_to(3);
		// same proposal fails as we're still in cooloff
		assert_noop!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash(2),
		), Error::<Test>::ProposalBlacklisted);
		// different proposal works fine.
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(3),
		));
	});
}

#[test]
fn external_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_noop!(
			Democracy::external_propose(
				Origin::signed(1),
				set_balance_proposal_hash(2),
			),
			BadOrigin,
		);
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(2),
		));
		assert_noop!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash(1),
		), Error::<Test>::DuplicateProposal);
		fast_forward_to(2);
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 4,
				proposal_hash: set_balance_proposal_hash(2),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
	});
}

#[test]
fn external_majority_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_noop!(
			Democracy::external_propose_majority(
				Origin::signed(1),
				set_balance_proposal_hash(2)
			),
			BadOrigin,
		);
		assert_ok!(Democracy::external_propose_majority(
			Origin::signed(3),
			set_balance_proposal_hash_and_note(2)
		));
		fast_forward_to(2);
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 4,
				proposal_hash: set_balance_proposal_hash(2),
				threshold: VoteThreshold::SimpleMajority,
				delay: 2,
			})
		);
	});
}

#[test]
fn external_default_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_noop!(
			Democracy::external_propose_default(
				Origin::signed(3),
				set_balance_proposal_hash(2)
			),
			BadOrigin,
		);
		assert_ok!(Democracy::external_propose_default(
			Origin::signed(1),
			set_balance_proposal_hash_and_note(2)
		));
		fast_forward_to(2);
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 4,
				proposal_hash: set_balance_proposal_hash(2),
				threshold: VoteThreshold::SuperMajorityAgainst,
				delay: 2,
			})
		);
	});
}

#[test]
fn fast_track_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let h = set_balance_proposal_hash_and_note(2);
		assert_noop!(Democracy::fast_track(Origin::signed(5), h, 3, 2), Error::<Test>::ProposalMissing);
		assert_ok!(Democracy::external_propose_majority(
			Origin::signed(3),
			set_balance_proposal_hash_and_note(2)
		));
		assert_noop!(Democracy::fast_track(Origin::signed(1), h, 3, 2), BadOrigin);
		assert_ok!(Democracy::fast_track(Origin::signed(5), h, 0, 0));
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 1,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SimpleMajority,
				delay: 0,
			})
		);
	});
}

#[test]
fn fast_track_referendum_fails_when_no_simple_majority() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let h = set_balance_proposal_hash_and_note(2);
		assert_ok!(Democracy::external_propose(
			Origin::signed(2),
			set_balance_proposal_hash_and_note(2)
		));
		assert_noop!(
			Democracy::fast_track(Origin::signed(5), h, 3, 2),
			Error::<Test>::NotSimpleMajority
		);
	});
}

#[test]
fn locked_for_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));
		assert_ok!(propose_set_balance_and_note(1, 3, 3));
		assert_eq!(Democracy::locked_for(0), Some(2));
		assert_eq!(Democracy::locked_for(1), Some(4));
		assert_eq!(Democracy::locked_for(2), Some(3));
	});
}

#[test]
fn single_proposal_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));
		assert!(Democracy::referendum_info(0).is_none());

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);

		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		assert_eq!(Democracy::referendum_count(), 1);
		assert_eq!(
			Democracy::referendum_info(0),
			Some(ReferendumInfo {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2
			})
		);
		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);
		assert_eq!(Democracy::tally(r), (1, 0, 1));

		fast_forward_to(3);

		// referendum still running
		assert!(Democracy::referendum_info(0).is_some());

		// referendum runs during 2 and 3, ends @ start of 4.
		fast_forward_to(4);

		assert!(Democracy::referendum_info(0).is_none());
		assert_eq!(Democracy::dispatch_queue(), vec![
			(6, set_balance_proposal_hash_and_note(2), 0)
		]);

		// referendum passes and wait another two blocks for enactment.
		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn cancel_queued_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);

		assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));

		fast_forward_to(4);

		assert_eq!(Democracy::dispatch_queue(), vec![
			(6, set_balance_proposal_hash_and_note(2), 0)
		]);

		assert_noop!(Democracy::cancel_queued(Origin::ROOT, 1), Error::<Test>::ProposalMissing);
		assert_ok!(Democracy::cancel_queued(Origin::ROOT, 0));
		assert_eq!(Democracy::dispatch_queue(), vec![]);
	});
}

#[test]
fn proxy_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Democracy::proxy(10), None);
		assert!(System::allow_death(&10));

		assert_noop!(Democracy::activate_proxy(Origin::signed(1), 10), Error::<Test>::NotOpen);

		assert_ok!(Democracy::open_proxy(Origin::signed(10), 1));
		assert!(!System::allow_death(&10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Open(1)));

		assert_noop!(Democracy::activate_proxy(Origin::signed(2), 10), Error::<Test>::WrongOpen);
		assert_ok!(Democracy::activate_proxy(Origin::signed(1), 10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Active(1)));

		// Can't set when already set.
		assert_noop!(Democracy::activate_proxy(Origin::signed(2), 10), Error::<Test>::AlreadyProxy);

		// But this works because 11 isn't proxying.
		assert_ok!(Democracy::open_proxy(Origin::signed(11), 2));
		assert_ok!(Democracy::activate_proxy(Origin::signed(2), 11));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Active(1)));
		assert_eq!(Democracy::proxy(11), Some(ProxyState::Active(2)));

		// 2 cannot fire 1's proxy:
		assert_noop!(Democracy::deactivate_proxy(Origin::signed(2), 10), Error::<Test>::WrongProxy);

		// 1 deactivates their proxy:
		assert_ok!(Democracy::deactivate_proxy(Origin::signed(1), 10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Open(1)));
		// but the proxy account cannot be killed until the proxy is closed.
		assert!(!System::allow_death(&10));

		// and then 10 closes it completely:
		assert_ok!(Democracy::close_proxy(Origin::signed(10)));
		assert_eq!(Democracy::proxy(10), None);
		assert!(System::allow_death(&10));

		// 11 just closes without 2's "permission".
		assert_ok!(Democracy::close_proxy(Origin::signed(11)));
		assert_eq!(Democracy::proxy(11), None);
		assert!(System::allow_death(&11));
	});
}

#[test]
fn single_proposal_should_work_with_proxy() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);
		let r = 0;
		assert_ok!(Democracy::open_proxy(Origin::signed(10), 1));
		assert_ok!(Democracy::activate_proxy(Origin::signed(1), 10));
		assert_ok!(Democracy::proxy_vote(Origin::signed(10), r, AYE));

		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);
		assert_eq!(Democracy::tally(r), (1, 0, 1));

		fast_forward_to(6);
		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn single_proposal_should_work_with_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		// Delegate vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);
		// Delegated vote is counted.
		assert_eq!(Democracy::tally(r), (3, 0, 3));

		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn single_proposal_should_work_with_cyclic_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		// Check behavior with cycle.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
		assert_ok!(Democracy::delegate(Origin::signed(3), 2, Conviction::max_value()));
		assert_ok!(Democracy::delegate(Origin::signed(1), 3, Conviction::max_value()));
		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		assert_eq!(Democracy::voters_for(r), vec![1]);

		// Delegated vote is counted.
		assert_eq!(Democracy::tally(r), (6, 0, 6));

		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
/// If transactor already voted, delegated vote is overwritten.
fn single_proposal_should_work_with_vote_and_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		// Vote.
		assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
		// Delegate vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
		assert_eq!(Democracy::voters_for(r), vec![1, 2]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);
		// Delegated vote is not counted.
		assert_eq!(Democracy::tally(r), (3, 0, 3));

		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn single_proposal_should_work_with_undelegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		// Delegate and undelegate vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
		assert_ok!(Democracy::undelegate(Origin::signed(2)));

		fast_forward_to(2);
		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		assert_eq!(Democracy::referendum_count(), 1);
		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);

		// Delegated vote is not counted.
		assert_eq!(Democracy::tally(r), (1, 0, 1));

		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
/// If transactor voted, delegated vote is overwritten.
fn single_proposal_should_work_with_delegation_and_vote() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);
		let r = 0;

		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		// Delegate vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

		// Vote.
		assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));

		assert_eq!(Democracy::referendum_count(), 1);
		assert_eq!(Democracy::voters_for(r), vec![1, 2]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);

		// Delegated vote is not counted.
		assert_eq!(Democracy::tally(r), (3, 0, 3));

		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn deposit_for_proposals_should_be_taken() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(propose_set_balance_and_note(1, 2, 5));
		assert_ok!(Democracy::second(Origin::signed(2), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::free_balance(2), 15);
		assert_eq!(Balances::free_balance(5), 35);
	});
}

#[test]
fn deposit_for_proposals_should_be_returned() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(propose_set_balance_and_note(1, 2, 5));
		assert_ok!(Democracy::second(Origin::signed(2), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		assert_ok!(Democracy::second(Origin::signed(5), 0));
		fast_forward_to(3);
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 20);
		assert_eq!(Balances::free_balance(5), 50);
	});
}

#[test]
fn proposal_with_deposit_below_minimum_should_not_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_noop!(propose_set_balance(1, 2, 0), Error::<Test>::ValueLow);
	});
}

#[test]
fn poor_proposer_should_not_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_noop!(propose_set_balance(1, 2, 11), BalancesError::<Test, _>::InsufficientBalance);
	});
}

#[test]
fn poor_seconder_should_not_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(propose_set_balance_and_note(2, 2, 11));
		assert_noop!(Democracy::second(Origin::signed(1), 0), BalancesError::<Test, _>::InsufficientBalance);
	});
}

#[test]
fn runners_up_should_come_after() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));
		assert_ok!(propose_set_balance_and_note(1, 3, 3));
		fast_forward_to(2);
		assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));
		fast_forward_to(4);
		assert_ok!(Democracy::vote(Origin::signed(1), 1, AYE));
		fast_forward_to(6);
		assert_ok!(Democracy::vote(Origin::signed(1), 2, AYE));
	});
}

#[test]
fn ooo_inject_referendums_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r1 = Democracy::inject_referendum(
			3,
			set_balance_proposal_hash_and_note(3),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		let r2 = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);

		assert_ok!(Democracy::vote(Origin::signed(1), r2, AYE));
		assert_eq!(Democracy::voters_for(r2), vec![1]);
		assert_eq!(Democracy::vote_of((r2, 1)), AYE);
		assert_eq!(Democracy::tally(r2), (1, 0, 1));

		next_block();
		assert_eq!(Balances::free_balance(42), 2);

		assert_ok!(Democracy::vote(Origin::signed(1), r1, AYE));
		assert_eq!(Democracy::voters_for(r1), vec![1]);
		assert_eq!(Democracy::vote_of((r1, 1)), AYE);
		assert_eq!(Democracy::tally(r1), (1, 0, 1));

		next_block();
		assert_eq!(Balances::free_balance(42), 3);
	});
}

#[test]
fn simple_passing_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), AYE);
		assert_eq!(Democracy::tally(r), (1, 0, 1));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn cancel_referendum_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		assert_ok!(Democracy::cancel_referendum(Origin::ROOT, r.into()));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn simple_failing_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, NAY));

		assert_eq!(Democracy::voters_for(r), vec![1]);
		assert_eq!(Democracy::vote_of((r, 1)), NAY);
		assert_eq!(Democracy::tally(r), (0, 1, 1));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn controversial_voting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);

		assert_ok!(Democracy::vote(Origin::signed(1), r, BIG_AYE));
		assert_ok!(Democracy::vote(Origin::signed(2), r, BIG_NAY));
		assert_ok!(Democracy::vote(Origin::signed(3), r, BIG_NAY));
		assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
		assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
		assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

		assert_eq!(Democracy::tally(r), (110, 100, 210));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn delayed_enactment_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			1
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
		assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
		assert_ok!(Democracy::vote(Origin::signed(3), r, AYE));
		assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
		assert_ok!(Democracy::vote(Origin::signed(5), r, AYE));
		assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

		assert_eq!(Democracy::tally(r), (21, 0, 21));

		next_block();
		assert_eq!(Balances::free_balance(42), 0);

		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn controversial_low_turnout_voting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
		assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

		assert_eq!(Democracy::tally(r), (60, 50, 110));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn passing_low_turnout_voting_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);

		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
		assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
		assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

		assert_eq!(Democracy::tally(r), (100, 50, 150));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn lock_voting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, Vote {
			aye: false,
			conviction: Conviction::Locked5x
		}));
		assert_ok!(Democracy::vote(Origin::signed(2), r, Vote {
			aye: true,
			conviction: Conviction::Locked4x
		}));
		assert_ok!(Democracy::vote(Origin::signed(3), r, Vote {
			aye: true,
			conviction: Conviction::Locked3x
		}));
		assert_ok!(Democracy::vote(Origin::signed(4), r, Vote {
			aye: true,
			conviction: Conviction::Locked2x
		}));
		assert_ok!(Democracy::vote(Origin::signed(5), r, Vote {
			aye: false,
			conviction: Conviction::Locked1x
		}));

		assert_eq!(Democracy::tally(r), (250, 100, 150));

		fast_forward_to(2);

		assert_eq!(Balances::locks(1), vec![]);
		assert_eq!(Balances::locks(2), vec![BalanceLock {
			id: DEMOCRACY_ID,
			amount: u64::max_value(),
			reasons: pallet_balances::Reasons::Misc,
		}]);
		assert_eq!(Democracy::locks(2), Some(18));
		assert_eq!(Balances::locks(3), vec![BalanceLock {
			id: DEMOCRACY_ID,
			amount: u64::max_value(),
			reasons: pallet_balances::Reasons::Misc,
		}]);
		assert_eq!(Democracy::locks(3), Some(10));
		assert_eq!(Balances::locks(4), vec![BalanceLock {
			id: DEMOCRACY_ID,
			amount: u64::max_value(),
			reasons: pallet_balances::Reasons::Misc,
		}]);
		assert_eq!(Democracy::locks(4), Some(6));
		assert_eq!(Balances::locks(5), vec![]);

		assert_eq!(Balances::free_balance(42), 2);

		assert_noop!(Democracy::unlock(Origin::signed(1), 1), Error::<Test>::NotLocked);

		fast_forward_to(5);
		assert_noop!(Democracy::unlock(Origin::signed(1), 4), Error::<Test>::NotExpired);
		fast_forward_to(6);
		assert_ok!(Democracy::unlock(Origin::signed(1), 4));
		assert_noop!(Democracy::unlock(Origin::signed(1), 4), Error::<Test>::NotLocked);

		fast_forward_to(9);
		assert_noop!(Democracy::unlock(Origin::signed(1), 3), Error::<Test>::NotExpired);
		fast_forward_to(10);
		assert_ok!(Democracy::unlock(Origin::signed(1), 3));
		assert_noop!(Democracy::unlock(Origin::signed(1), 3), Error::<Test>::NotLocked);

		fast_forward_to(17);
		assert_noop!(Democracy::unlock(Origin::signed(1), 2), Error::<Test>::NotExpired);
		fast_forward_to(18);
		assert_ok!(Democracy::unlock(Origin::signed(1), 2));
		assert_noop!(Democracy::unlock(Origin::signed(1), 2), Error::<Test>::NotLocked);
	});
}

#[test]
fn no_locks_without_conviction_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, Vote {
			aye: true,
			conviction: Conviction::None,
		}));

		fast_forward_to(2);

		assert_eq!(Balances::free_balance(42), 2);
		assert_eq!(Balances::locks(1), vec![]);
	});
}

#[test]
fn lock_voting_should_work_with_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, Vote {
			aye: false,
			conviction: Conviction::Locked5x
		}));
		assert_ok!(Democracy::vote(Origin::signed(2), r, Vote {
			aye: true,
			conviction: Conviction::Locked4x
		}));
		assert_ok!(Democracy::vote(Origin::signed(3), r, Vote {
			aye: true,
			conviction: Conviction::Locked3x
		}));
		assert_ok!(Democracy::delegate(Origin::signed(4), 2, Conviction::Locked2x));
		assert_ok!(Democracy::vote(Origin::signed(5), r, Vote {
			aye: false,
			conviction: Conviction::Locked1x
		}));

		assert_eq!(Democracy::tally(r), (250, 100, 150));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}
