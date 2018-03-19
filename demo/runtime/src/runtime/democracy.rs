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
use runtime_support::{StorageValue, StorageMap};
use demo_primitives::{AccountId, Hash, BlockNumber};
use dispatch::PrivCall as Proposal;
use runtime::{staking, system, session};
use runtime::staking::{PublicPass, Balance};

/// A token for privileged dispatch. Can only be created in this module.
pub struct PrivPass((),);

impl PrivPass {
	fn new() -> PrivPass { PrivPass((),) }

	#[cfg(test)]
	pub fn test() -> PrivPass { PrivPass((),) }
}

/// A proposal index.
pub type PropIndex = u32;
/// A referendum index.
pub type ReferendumIndex = u32;

/// A means of determining if a vote is past pass threshold.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub enum VoteThreshold {
	/// A supermajority of approvals is needed to pass this vote.
	SuperMajorityApprove,
	/// A supermajority of rejects is needed to fail this vote.
	SuperMajorityAgainst,
	/// A simple majority of approvals is needed to pass this vote.
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

trait Approved {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favour of approval.
	fn approved(&self, approve: Balance, against: Balance, electorate: Balance) -> bool;
}

impl Approved for VoteThreshold {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favour of approval.
	fn approved(&self, approve: Balance, against: Balance, electorate: Balance) -> bool {
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

storage_items! {
	// The number of (public) proposals that have been made so far.
	pub PublicPropCount get(public_prop_count): b"dem:ppc" => default PropIndex;
	// The public proposals. Unsorted.
	pub PublicProps get(public_props): b"dem:pub" => default Vec<(PropIndex, Proposal, AccountId)>;
	// Those who have locked a deposit.
	pub DepositOf get(deposit_lockers): b"dem:dep:" => map [ PropIndex => (Balance, Vec<AccountId>) ];
	// How often (in blocks) new public referenda are launched.
	pub LaunchPeriod get(launch_period): b"dem:lau" => required BlockNumber;
	// The minimum amount to be used as a deposit for a public referendum proposal.
	pub MinimumDeposit get(minimum_deposit): b"dem:min" => required Balance;

	// How often (in blocks) to check for new votes.
	pub VotingPeriod get(voting_period): b"dem:per" => required BlockNumber;

	// The next free referendum index, aka the number of referendums started so far.
	pub ReferendumCount get(next_free_ref_index): b"dem:rco" => default ReferendumIndex;
	// The next referendum index that should be tallied.
	pub NextTally get(next_tally): b"dem:nxt" => default ReferendumIndex;
	// Information concerning any given referendum.
	pub ReferendumInfoOf get(referendum_info): b"dem:pro:" => map [ ReferendumIndex => (BlockNumber, Proposal, VoteThreshold) ];

	// Get the voters for the current proposal.
	pub VotersFor get(voters_for): b"dem:vtr:" => default map [ ReferendumIndex => Vec<AccountId> ];

	// Get the vote, if Some, of `who`.
	pub VoteOf get(vote_of): b"dem:vot:" => map [ (ReferendumIndex, AccountId) => bool ];
}

// public proposals

/// Get the amount locked in support of `proposal`; false if proposal isn't a valid proposal
/// index.
pub fn locked_for(proposal: PropIndex) -> Option<Balance> {
	deposit_lockers(proposal).map(|(d, l)| d * (l.len() as Balance))
}

/// Return true if `ref_index` is an on-going referendum.
pub fn is_active_referendum(ref_index: ReferendumIndex) -> bool {
	ReferendumInfoOf::exists(ref_index)
}

/// Get all referendums currently active.
pub fn active_referendums() -> Vec<(ReferendumIndex, BlockNumber, Proposal, VoteThreshold)> {
	let next = NextTally::get();
	let last = ReferendumCount::get();
	(next..last).into_iter()
		.filter_map(|i| referendum_info(i).map(|(n, p, t)| (i, n, p, t)))
		.collect()
}

/// Get all referendums ready for tally at block `n`.
pub fn maturing_referendums_at(n: BlockNumber) -> Vec<(ReferendumIndex, BlockNumber, Proposal, VoteThreshold)> {
	let next = NextTally::get();
	let last = ReferendumCount::get();
	(next..last).into_iter()
		.filter_map(|i| referendum_info(i).map(|(n, p, t)| (i, n, p, t)))
		.take_while(|&(_, block_number, _, _)| block_number == n)
		.collect()
}

/// Get the voters for the current proposal.
pub fn tally(ref_index: ReferendumIndex) -> (staking::Balance, staking::Balance) {
	voters_for(ref_index).iter()
		.map(|a| (staking::balance(a), vote_of((ref_index, *a)).expect("all items come from `voters`; for an item to be in `voters` there must be a vote registered; qed")))
		.map(|(bal, vote)| if vote { (bal, 0) } else { (0, bal) })
		.fold((0, 0), |(a, b), (c, d)| (a + c, b + d))
}

impl_dispatch! {
	pub mod public;
	fn propose(proposal: Box<Proposal>, value: Balance) = 0;
	fn second(proposal: PropIndex) = 1;
	fn vote(ref_index: ReferendumIndex, approve_proposal: bool) = 2;
}

impl<'a> public::Dispatch for PublicPass<'a> {
	/// Propose a sensitive action to be taken.
	fn propose(self, proposal: Box<Proposal>, value: Balance) {
		assert!(value >= minimum_deposit());
		assert!(staking::internal::deduct_unbonded(&self, value));

		let index = PublicPropCount::get();
		PublicPropCount::put(index + 1);
		DepositOf::insert(index, (value, vec![*self]));

		let mut props = public_props();
		props.push((index, (*proposal).clone(), *self));
		PublicProps::put(props);
	}

	/// Propose a sensitive action to be taken.
	fn second(self, proposal: PropIndex) {
		let mut deposit = DepositOf::get(proposal).expect("can only second an existing proposal");
		assert!(staking::internal::deduct_unbonded(&self, deposit.0));

		deposit.1.push(*self);
		DepositOf::insert(proposal, deposit);
	}

	/// Vote in a referendum. If `approve_proposal` is true, the vote is to enact the proposal;
	/// false would be a vote to keep the status quo..
	fn vote(self, ref_index: ReferendumIndex, approve_proposal: bool) {
		if !is_active_referendum(ref_index) {
			panic!("vote given for invalid referendum.")
		}
		if staking::balance(&self) == 0 {
			panic!("transactor must have balance to signal approval.");
		}
		if !VoteOf::exists(&(ref_index, *self)) {
			let mut voters = voters_for(ref_index);
			voters.push(self.clone());
			VotersFor::insert(ref_index, voters);
		}
		VoteOf::insert(&(ref_index, *self), approve_proposal);
	}
}

impl_dispatch! {
	pub mod privileged;
	fn start_referendum(proposal: Box<Proposal>, vote_threshold: VoteThreshold) = 0;
	fn cancel_referendum(ref_index: ReferendumIndex) = 1;
}

impl privileged::Dispatch for PrivPass {
	/// Start a referendum.
	fn start_referendum(self, proposal: Box<Proposal>, vote_threshold: VoteThreshold) {
		inject_referendum(system::block_number() + voting_period(), *proposal, vote_threshold);
	}

	/// Remove a referendum.
	fn cancel_referendum(self, ref_index: ReferendumIndex) {
		clear_referendum(ref_index);
	}
}

pub mod internal {
	use super::*;
	use dispatch;

	/// Can be called directly by the council.
	pub fn start_referendum(proposal: Proposal, vote_threshold: VoteThreshold) {
		inject_referendum(system::block_number() + voting_period(), proposal, vote_threshold);
	}

	/// Remove a referendum.
	pub fn cancel_referendum(ref_index: ReferendumIndex) {
		clear_referendum(ref_index);
	}

	/// Current era is ending; we should finish up any proposals.
	pub fn end_block(now: BlockNumber) {
		// pick out another public referendum if it's time.
		if now % launch_period() == 0 {
			let mut public_props = public_props();
			if let Some((winner_index, _)) = public_props.iter()
				.enumerate()
				.max_by_key(|x| locked_for((x.1).0).expect("All current public proposals have an amount locked"))
			{
				let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
				let (deposit, depositors): (Balance, Vec<AccountId>) =
					DepositOf::take(prop_index).expect("depositors always exist for current proposals");
				// refund depositors
				for d in &depositors {
					staking::internal::refund(d, deposit);
				}
				PublicProps::put(public_props);
				inject_referendum(now + voting_period(), proposal, VoteThreshold::SuperMajorityApprove);
			}
		}

		// tally up votes for any expiring referenda.
		for (index, _, proposal, vote_threshold) in maturing_referendums_at(now) {
			let (approve, against) = tally(index);
			let total_stake = staking::total_stake();
			clear_referendum(index);
			if vote_threshold.approved(approve, against, total_stake) {
				proposal.dispatch(PrivPass::new());
			}
			NextTally::put(index + 1);
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

	ReferendumCount::put(ref_index + 1);
	ReferendumInfoOf::insert(ref_index, (end, proposal, vote_threshold));
	ref_index
}

/// Remove all info on a referendum.
fn clear_referendum(ref_index: ReferendumIndex) {
	ReferendumInfoOf::remove(ref_index);
	VotersFor::remove(ref_index);
	for v in voters_for(ref_index) {
		VoteOf::remove((ref_index, v));
	}
}

#[cfg(test)]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use runtime_support::{StorageList, StorageValue, StorageMap};
	use codec::Joiner;
	use keyring::Keyring::*;
	use runtime::{session, staking};

	pub fn externalities() -> TestExternalities {
		map![
			twox_128(session::SessionLength::key()).to_vec() => vec![].and(&1u64),
			twox_128(session::Validators::key()).to_vec() => vec![].and(&vec![Alice.to_raw_public(), Bob.into(), Charlie.into()]),
			twox_128(&staking::Intention::len_key()).to_vec() => vec![].and(&3u32),
			twox_128(&staking::Intention::key_for(0)).to_vec() => Alice.to_raw_public_vec(),
			twox_128(&staking::Intention::key_for(1)).to_vec() => Bob.to_raw_public_vec(),
			twox_128(&staking::Intention::key_for(2)).to_vec() => Charlie.to_raw_public_vec(),
			twox_128(&staking::FreeBalanceOf::key_for(*Alice)).to_vec() => vec![].and(&10u64),
			twox_128(&staking::FreeBalanceOf::key_for(*Bob)).to_vec() => vec![].and(&20u64),
			twox_128(&staking::FreeBalanceOf::key_for(*Charlie)).to_vec() => vec![].and(&30u64),
			twox_128(&staking::FreeBalanceOf::key_for(*Dave)).to_vec() => vec![].and(&40u64),
			twox_128(&staking::FreeBalanceOf::key_for(*Eve)).to_vec() => vec![].and(&50u64),
			twox_128(&staking::FreeBalanceOf::key_for(*Ferdie)).to_vec() => vec![].and(&60u64),
			twox_128(&staking::FreeBalanceOf::key_for(*One)).to_vec() => vec![].and(&1u64),
			twox_128(staking::TotalStake::key()).to_vec() => vec![].and(&210u64),
			twox_128(staking::SessionsPerEra::key()).to_vec() => vec![].and(&1u64),
			twox_128(staking::ValidatorCount::key()).to_vec() => vec![].and(&3u64),
			twox_128(staking::CurrentEra::key()).to_vec() => vec![].and(&1u64),
			twox_128(staking::TransactionFee::key()).to_vec() => vec![].and(&1u64),
			twox_128(staking::BondingDuration::key()).to_vec() => vec![].and(&0u64),

			twox_128(LaunchPeriod::key()).to_vec() => vec![].and(&1u64),
			twox_128(VotingPeriod::key()).to_vec() => vec![].and(&1u64),
			twox_128(MinimumDeposit::key()).to_vec() => vec![].and(&1u64)
		]
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring::*;
	use environment::with_env;
	use demo_primitives::AccountId;
	use dispatch::PrivCall as Proposal;
	use runtime::staking::PublicPass;
	use super::public::Dispatch;
	use super::privileged::Dispatch as PrivDispatch;
	use runtime::{staking, session, democracy};

	fn new_test_ext() -> TestExternalities {
		testing::externalities()
	}

	#[test]
	fn params_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(launch_period(), 1u64);
			assert_eq!(voting_period(), 1u64);
			assert_eq!(minimum_deposit(), 1u64);
			assert_eq!(next_free_ref_index(), 0u32);
			assert_eq!(staking::sessions_per_era(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);
		});
	}

	// TODO: test VoteThreshold

	fn propose_sessions_per_era(who: &AccountId, value: u64, locked: Balance) {
		PublicPass::test(who).
			propose(Box::new(Proposal::Staking(staking::privileged::Call::set_sessions_per_era(value))), locked);
	}

	#[test]
	fn locked_for_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 2u64);
			propose_sessions_per_era(&Alice, 4, 4u64);
			propose_sessions_per_era(&Alice, 3, 3u64);
			assert_eq!(locked_for(0), Some(2));
			assert_eq!(locked_for(1), Some(4));
			assert_eq!(locked_for(2), Some(3));
		});
	}

	#[test]
	fn single_proposal_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 1u64);
			democracy::internal::end_block(system::block_number());

			with_env(|e| e.block_number = 2);
			let r = 0;
			PublicPass::test(&Alice).vote(r, true);

			assert_eq!(next_free_ref_index(), 1);
			assert_eq!(voters_for(r), vec![Alice.to_raw_public()]);
			assert_eq!(vote_of((r, *Alice)), Some(true));
			assert_eq!(tally(r), (10, 0));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_taken() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 5u64);
			PublicPass::test(&Bob).second(0);
			PublicPass::test(&Eve).second(0);
			PublicPass::test(&Eve).second(0);
			PublicPass::test(&Eve).second(0);
			assert_eq!(staking::balance(&Alice), 5u64);
			assert_eq!(staking::balance(&Bob), 15u64);
			assert_eq!(staking::balance(&Eve), 35u64);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_returned() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 5u64);
			PublicPass::test(&Bob).second(0);
			PublicPass::test(&Eve).second(0);
			PublicPass::test(&Eve).second(0);
			PublicPass::test(&Eve).second(0);
			democracy::internal::end_block(system::block_number());
			assert_eq!(staking::balance(&Alice), 10u64);
			assert_eq!(staking::balance(&Bob), 20u64);
			assert_eq!(staking::balance(&Eve), 50u64);
		});
	}

	#[test]
	#[should_panic]
	fn proposal_with_deposit_below_minimum_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 0u64);
		});
	}

	#[test]
	#[should_panic]
	fn poor_proposer_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Alice, 2, 11u64);
		});
	}

	#[test]
	#[should_panic]
	fn poor_seconder_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			propose_sessions_per_era(&Bob, 2, 11u64);
			PublicPass::test(&Alice).second(0);
		});
	}

	fn propose_bonding_duration(who: &AccountId, value: u64, locked: Balance) {
		PublicPass::test(who).
			propose(Box::new(Proposal::Staking(staking::privileged::Call::set_bonding_duration(value))), locked);
	}

	#[test]
	fn runners_up_should_come_after() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 0);
			propose_bonding_duration(&Alice, 2, 2u64);
			propose_bonding_duration(&Alice, 4, 4u64);
			propose_bonding_duration(&Alice, 3, 3u64);
			democracy::internal::end_block(system::block_number());

			with_env(|e| e.block_number = 1);
			PublicPass::test(&Alice).vote(0, true);
			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 4u64);

			with_env(|e| e.block_number = 2);
			PublicPass::test(&Alice).vote(1, true);
			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 3u64);

			with_env(|e| e.block_number = 3);
			PublicPass::test(&Alice).vote(2, true);
			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();
			assert_eq!(staking::bonding_duration(), 2u64);
		});
	}

	fn sessions_per_era_propsal(value: u64) -> Proposal {
		Proposal::Staking(staking::privileged::Call::set_sessions_per_era(value))
	}

	#[test]
	fn simple_passing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Alice).vote(r, true);

			assert_eq!(voters_for(r), vec![Alice.to_raw_public()]);
			assert_eq!(vote_of((r, *Alice)), Some(true));
			assert_eq!(tally(r), (10, 0));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn cancel_referendum_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Alice).vote(r, true);
			PrivPass::new().cancel_referendum(r);

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 1u64);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Alice).vote(r, false);

			assert_eq!(voters_for(r), vec![Alice.to_raw_public()]);
			assert_eq!(vote_of((r, *Alice)), Some(false));
			assert_eq!(tally(r), (0, 10));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 1u64);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Alice).vote(r, true);
			PublicPass::test(&Bob).vote(r, false);
			PublicPass::test(&Charlie).vote(r, false);
			PublicPass::test(&Dave).vote(r, true);
			PublicPass::test(&Eve).vote(r, false);
			PublicPass::test(&Ferdie).vote(r, true);

			assert_eq!(tally(r), (110, 100));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Eve).vote(r, false);
			PublicPass::test(&Ferdie).vote(r, true);

			assert_eq!(tally(r), (60, 50));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 1u64);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);

			with_env(|e| e.block_number = 1);
			let r = inject_referendum(1, sessions_per_era_propsal(2), VoteThreshold::SuperMajorityApprove);
			PublicPass::test(&Dave).vote(r, true);
			PublicPass::test(&Eve).vote(r, false);
			PublicPass::test(&Ferdie).vote(r, true);

			assert_eq!(tally(r), (100, 50));

			democracy::internal::end_block(system::block_number());
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}
}
