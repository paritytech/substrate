// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Democratic system: Handles administration of general stakeholder voting.

use rstd::prelude::*;
use integer_sqrt::IntegerSquareRoot;
use codec::{KeyedVec, Slicable, Input, NonTrivialSlicable};
use runtime_support::storage;
use demo_primitives::{Proposal, AccountId, Hash, BlockNumber};
use runtime::{staking, system, session};
use runtime::staking::Balance;

pub type PropIndex = u32;
pub type ReferendumIndex = u32;

pub enum VoteThreshold {
	SuperMajorityApprove,
	SuperMajorityAgainst,
	SimpleMajority,
}

impl Slicable for VoteThreshold {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		u8::decode(input).and_then(|v| match v {
			0 => Some(VoteThreshold::SuperMajorityApprove),
			1 => Some(VoteThreshold::SuperMajorityAgainst),
			2 => Some(VoteThreshold::SimpleMajority),
			_ => None,
		})
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		match *self {
			VoteThreshold::SuperMajorityApprove => 0u8,
			VoteThreshold::SuperMajorityAgainst => 1u8,
			VoteThreshold::SimpleMajority => 2u8,
		}.using_encoded(f)
	}
}
impl NonTrivialSlicable for VoteThreshold {}

impl VoteThreshold {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favour of approval.
	pub fn approved(&self, approve: Balance, against: Balance, electorate: Balance) -> bool {
		let voters = approve + against;
		match *self {
			VoteThreshold::SuperMajorityApprove =>
				voters.integer_sqrt() * approve / electorate.integer_sqrt() > against,
			VoteThreshold::SuperMajorityAgainst =>
				approve > voters.integer_sqrt() * against / electorate.integer_sqrt(),
			VoteThreshold::SimpleMajority => approve > against,
		}
	}
}

// public proposals
pub const PUBLIC_PROP_COUNT: &[u8] = b"dem:ppc";	// PropIndex
pub const PUBLIC_PROPS: &[u8] = b"dem:pub";			// Vec<(PropIndex, Proposal)>
pub const DEPOSIT_OF: &[u8] = b"dem:dep:";			// PropIndex -> (Balance, Vec<AccountId>)
pub const LAUNCH_PERIOD: &[u8] = b"dem:lau";		// BlockNumber
pub const MINIMUM_DEPOSIT: &[u8] = b"dem:min";		// Balance

// referenda
pub const VOTING_PERIOD: &[u8] = b"dem:per";		// BlockNumber
pub const REFERENDUM_COUNT: &[u8] = b"dem:rco";		// ReferendumIndex
pub const NEXT_TALLY: &[u8] = b"dem:nxt";			// ReferendumIndex
pub const REFERENDUM_INFO_OF: &[u8] = b"dem:pro:";	// ReferendumIndex -> (BlockNumber, Proposal, VoteThreshold)
pub const VOTERS_FOR: &[u8] = b"dem:vtr:";			// ReferendumIndex -> Vec<AccountId>
pub const VOTE_OF: &[u8] = b"dem:vot:";				// (ReferendumIndex, AccountId) -> bool

/// The minimum amount to be used as a deposit for a public referendum proposal.
pub fn minimum_deposit() -> Balance {
	storage::get(MINIMUM_DEPOSIT)
		.expect("all core parameters of council module must be in place")
}

/// How often (in blocks) to check for new votes.
pub fn voting_period() -> BlockNumber {
	storage::get(VOTING_PERIOD)
		.expect("all core parameters of council module must be in place")
}

/// How often (in blocks) new public referenda are launched.
pub fn launch_period() -> BlockNumber {
	storage::get(LAUNCH_PERIOD)
		.expect("all core parameters of council module must be in place")
}

/// The public proposals. Unsorted.
pub fn public_props() -> Vec<(PropIndex, Proposal, AccountId)> {
	storage::get_or_default(PUBLIC_PROPS)
}

/// Those who have locked a deposit.
pub fn deposit_lockers(proposal: PropIndex) -> Option<(Balance, Vec<AccountId>)> {
	storage::get(&proposal.to_keyed_vec(DEPOSIT_OF))
}

/// Get the amount locked in support of `proposal`; false if proposal isn't a valid proposal
/// index.
pub fn locked_for(proposal: PropIndex) -> Option<Balance> {
	deposit_lockers(proposal).map(|(d, l)| d * (l.len() as Balance))
}

/// Return true if `ref_index` is an on-going referendum.
pub fn is_active_referendum(ref_index: ReferendumIndex) -> bool {
	storage::exists(&ref_index.to_keyed_vec(REFERENDUM_INFO_OF))
}

/// Get the voters for the current proposal.
pub fn voters_for(ref_index: ReferendumIndex) -> Vec<AccountId> {
	storage::get_or_default(&ref_index.to_keyed_vec(VOTERS_FOR))
}

/// Get the vote, if Some, of `who`.
pub fn vote_of(who: &AccountId, ref_index: ReferendumIndex) -> Option<bool> {
	storage::get(&(*who, ref_index).to_keyed_vec(VOTE_OF))
}

/// Get the info concerning the next referendum.
pub fn referendum_info(ref_index: ReferendumIndex) -> Option<(BlockNumber, Proposal, VoteThreshold)> {
	storage::get(&ref_index.to_keyed_vec(REFERENDUM_INFO_OF))
}

/// Get all referendums ready for tally at block `n`.
pub fn maturing_referendums_at(n: BlockNumber) -> Vec<(ReferendumIndex, BlockNumber, Proposal, VoteThreshold)> {
	let next: ReferendumIndex = storage::get_or_default(NEXT_TALLY);
	let last: ReferendumIndex = storage::get_or_default(REFERENDUM_COUNT);
	(next..last).into_iter()
		.filter_map(|i| referendum_info(i).map(|(n, p, t)| (i, n, p, t)))
		.take_while(|&(_, block_number, _, _)| block_number == n)
		.collect()
}

/// Get the voters for the current proposal.
pub fn tally(ref_index: ReferendumIndex) -> (staking::Balance, staking::Balance) {
	voters_for(ref_index).iter()
		.map(|a| (staking::balance(a), vote_of(a, ref_index).expect("all items come from `voters`; for an item to be in `voters` there must be a vote registered; qed")))
		.map(|(bal, vote)| if vote { (bal, 0) } else { (0, bal) })
		.fold((0, 0), |(a, b), (c, d)| (a + c, b + d))
}

/// Get the next free referendum index, aka the number of referendums started so far.
pub fn next_free_ref_index() -> ReferendumIndex {
	storage::get_or_default(REFERENDUM_COUNT)
}

pub mod public {
	use super::*;

	/// Propose a sensitive action to be taken.
	pub fn propose(signed: &AccountId, proposal: &Proposal, value: Balance) {
		assert!(value >= minimum_deposit());
		let b = staking::balance(signed);
		assert!(b >= value);

		staking::internal::set_balance(signed, b - value);

		let index: PropIndex = storage::get_or_default(PUBLIC_PROP_COUNT);
		storage::put(PUBLIC_PROP_COUNT, &(index + 1));
		storage::put(&index.to_keyed_vec(DEPOSIT_OF), &(value, vec![*signed]));

		let mut props = public_props();
		props.push((index, proposal.clone(), *signed));
		storage::put(PUBLIC_PROPS, &props);
	}

	/// Propose a sensitive action to be taken.
	pub fn second(signed: &AccountId, proposal: PropIndex) {
		let b = staking::balance(signed);
		let key = proposal.to_keyed_vec(DEPOSIT_OF);
		let mut deposit: (Balance, Vec<AccountId>) =
			storage::get(&key).expect("can only second an existing proposal");
		assert!(b >= deposit.0);
		deposit.1.push(*signed);

		staking::internal::set_balance(signed, b - deposit.0);
		storage::put(&key, &deposit);
	}

	/// Vote in a referendum. If `approve_proposal` is true, the vote is to enact the proposal;
	/// false would be a vote to keep the status quo..
	pub fn vote(signed: &AccountId, ref_index: ReferendumIndex, approve_proposal: bool) {
		if !is_active_referendum(ref_index) {
			panic!("vote given for invalid referendum.")
		}
		if staking::balance(signed) == 0 {
			panic!("transactor must have balance to signal approval.");
		}
		let key = (*signed, ref_index).to_keyed_vec(VOTE_OF);
		if !storage::exists(&key) {
			let mut voters = voters_for(ref_index);
			voters.push(signed.clone());
			storage::put(&ref_index.to_keyed_vec(VOTERS_FOR), &voters);
		}
		storage::put(&key, &approve_proposal);
	}
}

pub mod privileged {
	use super::*;

	/// Can be called directly by the council.
	pub fn start_referendum(proposal: Proposal, vote_threshold: VoteThreshold) {
		inject_referendum(system::block_number() + voting_period(), proposal, vote_threshold);
	}

	/// Remove a referendum.
	pub fn clear_referendum(ref_index: ReferendumIndex) {
		for v in voters_for(ref_index) {
			storage::kill(&(v, ref_index).to_keyed_vec(VOTE_OF));
		}
		storage::kill(&ref_index.to_keyed_vec(VOTERS_FOR));
	}
}

pub mod internal {
	use super::*;
	use demo_primitives::Proposal;
	use dispatch::enact_proposal;

	/// Current era is ending; we should finish up any proposals.
	pub fn end_block() {
		let now = system::block_number();

		// pick out another public referendum if it's time.
		if now % launch_period() == 0 {
			let mut public_props = public_props();
			if let Some((winner_index, _)) = public_props.iter()
				.enumerate()
				.max_by_key(|x| locked_for((x.1).0).expect("All current public proposals have an amount locked"))
			{
				let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
				let (deposit, depositors): (Balance, Vec<AccountId>) =
					storage::take(&prop_index.to_keyed_vec(DEPOSIT_OF))
						.expect("depositors always exist for current proposals");
				// refund depositors
				for d in &depositors {
					staking::internal::set_balance(d, staking::balance(d) + deposit);
				}
				storage::put(PUBLIC_PROPS, &public_props);
				inject_referendum(now + voting_period(), proposal, VoteThreshold::SuperMajorityApprove);
			}
		}

		// tally up votes for any expiring referenda.
		for (index, _, proposal, vote_threshold) in maturing_referendums_at(now) {
			let (approve, against) = tally(index);
			let total_stake = staking::total_stake();
			privileged::clear_referendum(index);
			if vote_threshold.approved(approve, against, total_stake) {
				enact_proposal(proposal);
			}
			storage::put(NEXT_TALLY, &(index + 1));
		}
	}
}

/// Start a referendum
fn inject_referendum(
	end: BlockNumber,
	proposal: Proposal,
	vote_threshold: VoteThreshold
) -> ReferendumIndex {
	let ref_index = next_free_ref_index();
	if ref_index > 0 && referendum_info(ref_index - 1).map(|i| i.0 > end).unwrap_or(false) {
		panic!("Cannot inject a referendum that ends earlier than preceeding referendum");
	}

	storage::put(REFERENDUM_COUNT, &(ref_index + 1));
	storage::put(&ref_index.to_keyed_vec(REFERENDUM_INFO_OF), &(end, proposal, vote_threshold));
	ref_index
}

#[cfg(test)]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use codec::Joiner;
	use keyring::Keyring;
	use runtime::{session, staking};

	pub fn externalities() -> TestExternalities {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let one = Keyring::One.to_raw_public();

		map![
			twox_128(session::SESSION_LENGTH).to_vec() => vec![].and(&1u64),
			twox_128(session::VALIDATOR_COUNT).to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(session::VALIDATOR_AT)).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(session::VALIDATOR_AT)).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(session::VALIDATOR_AT)).to_vec() => charlie.to_vec(),
			twox_128(staking::INTENTION_COUNT).to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(staking::INTENTION_AT)).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(staking::INTENTION_AT)).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(staking::INTENTION_AT)).to_vec() => charlie.to_vec(),
			twox_128(&alice.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&10u64),
			twox_128(&bob.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&20u64),
			twox_128(&charlie.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&30u64),
			twox_128(&dave.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&40u64),
			twox_128(&eve.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&50u64),
			twox_128(&ferdie.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&60u64),
			twox_128(&one.to_keyed_vec(staking::BALANCE_OF)).to_vec() => vec![].and(&1u64),
			twox_128(staking::TOTAL_STAKE).to_vec() => vec![].and(&210u64),
			twox_128(staking::SESSIONS_PER_ERA).to_vec() => vec![].and(&1u64),
			twox_128(staking::VALIDATOR_COUNT).to_vec() => vec![].and(&3u64),
			twox_128(staking::CURRENT_ERA).to_vec() => vec![].and(&1u64),

			twox_128(LAUNCH_PERIOD).to_vec() => vec![].and(&1u64),
			twox_128(VOTING_PERIOD).to_vec() => vec![].and(&1u64),
			twox_128(MINIMUM_DEPOSIT).to_vec() => vec![].and(&1u64)
		]
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use environment::with_env;
	use demo_primitives::{AccountId, Proposal};
	use runtime::{staking, session, democracy};

	fn new_test_ext() -> TestExternalities {
		testing::externalities()
	}

	#[test]
	fn params_should_work() {
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(launch_period(), 1u64);
			assert_eq!(voting_period(), 1u64);
			assert_eq!(minimum_deposit(), 1u64);
			assert_eq!(next_free_ref_index(), 0u32);
			assert_eq!(staking::sessions_per_era(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);
		});
	}

	// TODO: test VoteThreshold

	#[test]
	fn locked_for_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 2u64);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(4), 4u64);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(3), 3u64);
			assert_eq!(locked_for(0), Some(2));
			assert_eq!(locked_for(1), Some(4));
			assert_eq!(locked_for(2), Some(3));
		});
	}

	#[test]
	fn single_proposal_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 1u64);
			democracy::internal::end_block();

			with_env(|e| e.block_number = 2);
			let r = 0;
			public::vote(&alice, r, true);

			assert_eq!(next_free_ref_index(), 1);
			assert_eq!(voters_for(r), vec![alice.clone()]);
			assert_eq!(vote_of(&alice, r), Some(true));
			assert_eq!(tally(r), (10, 0));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_taken() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 5u64);
			public::second(&bob, 0);
			public::second(&eve, 0);
			public::second(&eve, 0);
			public::second(&eve, 0);
			assert_eq!(staking::balance(&alice), 5u64);
			assert_eq!(staking::balance(&bob), 15u64);
			assert_eq!(staking::balance(&eve), 35u64);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_returned() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 5u64);
			public::second(&bob, 0);
			public::second(&eve, 0);
			public::second(&eve, 0);
			public::second(&eve, 0);
			democracy::internal::end_block();
			assert_eq!(staking::balance(&alice), 10u64);
			assert_eq!(staking::balance(&bob), 20u64);
			assert_eq!(staking::balance(&eve), 50u64);
		});
	}

	#[test]
	#[should_panic]
	fn proposal_with_deposit_below_minimum_should_panic() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 0u64);
		});
	}

	#[test]
	#[should_panic]
	fn poor_proposer_should_panic() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2), 11u64);
		});
	}

	#[test]
	#[should_panic]
	fn poor_seconder_should_panic() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			public::propose(&bob, &Proposal::StakingSetSessionsPerEra(2), 11u64);
			public::second(&alice, 0);
		});
	}

	#[test]
	fn runners_up_should_come_after() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 0);
			public::propose(&alice, &Proposal::StakingSetBondingDuration(2), 2u64);
			public::propose(&alice, &Proposal::StakingSetBondingDuration(4), 4u64);
			public::propose(&alice, &Proposal::StakingSetBondingDuration(3), 3u64);
			democracy::internal::end_block();

			with_env(|e| e.block_number = 1);
			public::vote(&alice, 0, true);
			democracy::internal::end_block();
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 4u64);

			with_env(|e| e.block_number = 2);
			public::vote(&alice, 1, true);
			democracy::internal::end_block();
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 3u64);

			with_env(|e| e.block_number = 3);
			public::vote(&alice, 2, true);
			democracy::internal::end_block();
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 2u64);
		});
	}

	#[test]
	fn simple_passing_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, Proposal::StakingSetSessionsPerEra(2), VoteThreshold::SuperMajorityApprove);
			public::vote(&alice, r, true);

			assert_eq!(voters_for(r), vec![alice.clone()]);
			assert_eq!(vote_of(&alice, r), Some(true));
			assert_eq!(tally(r), (10, 0));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, Proposal::StakingSetSessionsPerEra(2), VoteThreshold::SuperMajorityApprove);
			public::vote(&alice, r, false);

			assert_eq!(voters_for(r), vec![alice.clone()]);
			assert_eq!(vote_of(&alice, r), Some(false));
			assert_eq!(tally(r), (0, 10));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 1u64);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let one = Keyring::One.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, Proposal::StakingSetSessionsPerEra(2), VoteThreshold::SuperMajorityApprove);
			public::vote(&alice, r, true);
			public::vote(&bob, r, false);
			public::vote(&charlie, r, false);
			public::vote(&dave, r, true);
			public::vote(&eve, r, false);
			public::vote(&ferdie, r, true);

			assert_eq!(tally(r), (110, 100));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let one = Keyring::One.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, Proposal::StakingSetSessionsPerEra(2), VoteThreshold::SuperMajorityApprove);
			public::vote(&eve, r, false);
			public::vote(&ferdie, r, true);

			assert_eq!(tally(r), (60, 50));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 1u64);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let one = Keyring::One.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);

			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, Proposal::StakingSetSessionsPerEra(2), VoteThreshold::SuperMajorityApprove);
			public::vote(&dave, r, true);
			public::vote(&eve, r, false);
			public::vote(&ferdie, r, true);

			assert_eq!(tally(r), (100, 50));

			democracy::internal::end_block();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}
}
