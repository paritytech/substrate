// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Mock file for election module.

#![cfg(test)]

use frame_support::{
	StorageValue, StorageMap, parameter_types, assert_ok,
	traits::{ChangeMembers, Currency, LockIdentifier},
};
use sp_core::H256;
use sp_runtime::{
	BuildStorage, testing::Header, traits::{BlakeTwo256, IdentityLookup},
};
use crate as elections;


parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
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

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub const CandidacyBond: u64 = 3;
	pub const CarryCount: u32 = 2;
	pub const InactiveGracePeriod: u32 = 1;
	pub const VotingPeriod: u64 = 4;
	pub const MinimumVotingLock: u64 = 5;
	pub static VotingBond: u64 = 0;
	pub static VotingFee: u64 = 0;
	pub static PresentSlashPerVoter: u64 = 0;
	pub static DecayRatio: u32 = 0;
	pub static Members: Vec<u64> = vec![];
}

pub struct TestChangeMembers;
impl ChangeMembers<u64> for TestChangeMembers {
	fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
		let mut old_plus_incoming = MEMBERS.with(|m| m.borrow().to_vec());
		old_plus_incoming.extend_from_slice(incoming);
		old_plus_incoming.sort();
		let mut new_plus_outgoing = new.to_vec();
		new_plus_outgoing.extend_from_slice(outgoing);
		new_plus_outgoing.sort();
		assert_eq!(old_plus_incoming, new_plus_outgoing);

		MEMBERS.with(|m| *m.borrow_mut() = new.to_vec());
	}
}

parameter_types!{
	pub const ElectionPalletId: LockIdentifier = *b"py/elect";
}

impl elections::Config for Test {
	type Event = Event;
	type Currency = Balances;
	type BadPresentation = ();
	type BadReaper = ();
	type BadVoterIndex = ();
	type LoserCandidate = ();
	type ChangeMembers = TestChangeMembers;
	type CandidacyBond = CandidacyBond;
	type VotingBond = VotingBond;
	type VotingFee = VotingFee;
	type MinimumVotingLock = MinimumVotingLock;
	type PresentSlashPerVoter = PresentSlashPerVoter;
	type CarryCount = CarryCount;
	type InactiveGracePeriod = InactiveGracePeriod;
	type VotingPeriod = VotingPeriod;
	type DecayRatio = DecayRatio;
	type PalletId = ElectionPalletId;
}

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

use frame_system as system;
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Call, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Event<T>, Config<T>},
		Elections: elections::{Pallet, Call, Event<T>, Config<T>},
	}
);

pub struct ExtBuilder {
	balance_factor: u64,
	decay_ratio: u32,
	desired_seats: u32,
	voting_fee: u64,
	voting_bond: u64,
	bad_presentation_punishment: u64,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			balance_factor: 1,
			decay_ratio: 24,
			desired_seats: 2,
			voting_fee: 0,
			voting_bond: 0,
			bad_presentation_punishment: 1,
		}
	}
}

impl ExtBuilder {
	pub fn balance_factor(mut self, factor: u64) -> Self {
		self.balance_factor = factor;
		self
	}
	pub fn decay_ratio(mut self, ratio: u32) -> Self {
		self.decay_ratio = ratio;
		self
	}
	pub fn voting_fee(mut self, fee: u64) -> Self {
		self.voting_fee = fee;
		self
	}
	pub fn bad_presentation_punishment(mut self, fee: u64) -> Self {
		self.bad_presentation_punishment = fee;
		self
	}
	pub fn voting_bond(mut self, fee: u64) -> Self {
		self.voting_bond = fee;
		self
	}
	pub fn desired_seats(mut self, seats: u32) -> Self {
		self.desired_seats = seats;
		self
	}
	pub fn build(self) -> sp_io::TestExternalities {
		VOTING_BOND.with(|v| *v.borrow_mut() = self.voting_bond);
		VOTING_FEE.with(|v| *v.borrow_mut() = self.voting_fee);
		PRESENT_SLASH_PER_VOTER.with(|v| *v.borrow_mut() = self.bad_presentation_punishment);
		DECAY_RATIO.with(|v| *v.borrow_mut() = self.decay_ratio);
		let mut ext: sp_io::TestExternalities = GenesisConfig {
			pallet_balances: pallet_balances::GenesisConfig::<Test>{
				balances: vec![
					(1, 10 * self.balance_factor),
					(2, 20 * self.balance_factor),
					(3, 30 * self.balance_factor),
					(4, 40 * self.balance_factor),
					(5, 50 * self.balance_factor),
					(6, 60 * self.balance_factor)
				],
			},
			elections: elections::GenesisConfig::<Test>{
				members: vec![],
				desired_seats: self.desired_seats,
				presentation_duration: 2,
				term_duration: 5,
			},
		}.build_storage().unwrap().into();
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

pub(crate) fn voter_ids() -> Vec<u64> {
	Elections::all_voters().iter().map(|v| v.unwrap_or(0) ).collect::<Vec<u64>>()
}

pub(crate) fn vote(i: u64, l: usize) {
	let _ = Balances::make_free_balance_be(&i, 20);
	assert_ok!(
		Elections::set_approvals(
			Origin::signed(i),
			(0..l).map(|_| true).collect::<Vec<bool>>(),
			0,
			0,
			20,
		)
	);
}

pub(crate) fn vote_at(i: u64, l: usize, index: elections::VoteIndex) {
	let _ = Balances::make_free_balance_be(&i, 20);
	assert_ok!(
		Elections::set_approvals(
			Origin::signed(i),
			(0..l).map(|_| true).collect::<Vec<bool>>(),
			0,
			index,
			20,
		)
	);
}

pub(crate) fn create_candidate(i: u64, index: u32) {
	let _ = Balances::make_free_balance_be(&i, 20);
	assert_ok!(Elections::submit_candidacy(Origin::signed(i), index));
}

pub(crate) fn balances(who: &u64) -> (u64, u64) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}

pub(crate) fn locks(who: &u64) -> Vec<u64> {
	Balances::locks(who).iter().map(|l| l.amount).collect::<Vec<u64>>()
}

pub(crate) fn new_test_ext_with_candidate_holes() -> sp_io::TestExternalities {
	let mut t = ExtBuilder::default().build();
	t.execute_with(|| {
		<elections::Candidates<Test>>::put(vec![0, 0, 1]);
		elections::CandidateCount::put(1);
		<elections::RegisterInfoOf<Test>>::insert(1, (0, 2));
	});
	t
}
