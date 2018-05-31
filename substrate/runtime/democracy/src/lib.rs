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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(feature = "std")]
extern crate substrate_primitives;

#[macro_use]
extern crate substrate_runtime_std as rstd;

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
use primitives::traits::{Zero, Executable, RefInto, As};
use runtime_support::{StorageValue, StorageMap, Parameter, Dispatchable, IsSubType};

mod vote_threshold;
pub use vote_threshold::{Approved, VoteThreshold};

/// A proposal index.
pub type PropIndex = u32;
/// A referendum index.
pub type ReferendumIndex = u32;

pub trait Trait: staking::Trait + Sized {
	type Proposal: Parameter + Dispatchable + IsSubType<Module<Self>>;
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn propose(aux, proposal: Box<T::Proposal>, value: T::Balance) = 0;
		fn second(aux, proposal: PropIndex) = 1;
		fn vote(aux, ref_index: ReferendumIndex, approve_proposal: bool) = 2;
	}
	pub enum PrivCall {
		fn start_referendum(proposal: Box<T::Proposal>, vote_threshold: VoteThreshold) = 0;
		fn cancel_referendum(ref_index: ReferendumIndex) = 1;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// The number of (public) proposals that have been made so far.
	pub PublicPropCount get(public_prop_count): b"dem:ppc" => default PropIndex;
	// The public proposals. Unsorted.
	pub PublicProps get(public_props): b"dem:pub" => default Vec<(PropIndex, T::Proposal, T::AccountId)>;
	// Those who have locked a deposit.
	pub DepositOf get(deposit_of): b"dem:dep:" => map [ PropIndex => (T::Balance, Vec<T::AccountId>) ];
	// How often (in blocks) new public referenda are launched.
	pub LaunchPeriod get(launch_period): b"dem:lau" => required T::BlockNumber;
	// The minimum amount to be used as a deposit for a public referendum proposal.
	pub MinimumDeposit get(minimum_deposit): b"dem:min" => required T::Balance;

	// How often (in blocks) to check for new votes.
	pub VotingPeriod get(voting_period): b"dem:per" => required T::BlockNumber;

	// The next free referendum index, aka the number of referendums started so far.
	pub ReferendumCount get(referendum_count): b"dem:rco" => required ReferendumIndex;
	// The next referendum index that should be tallied.
	pub NextTally get(next_tally): b"dem:nxt" => required ReferendumIndex;
	// Information concerning any given referendum.
	pub ReferendumInfoOf get(referendum_info): b"dem:pro:" => map [ ReferendumIndex => (T::BlockNumber, T::Proposal, VoteThreshold) ];

	// Get the voters for the current proposal.
	pub VotersFor get(voters_for): b"dem:vtr:" => default map [ ReferendumIndex => Vec<T::AccountId> ];

	// Get the vote, if Some, of `who`.
	pub VoteOf get(vote_of): b"dem:vot:" => map [ (ReferendumIndex, T::AccountId) => bool ];
}

impl<T: Trait> Module<T> {

	// exposed immutables.

	/// Get the amount locked in support of `proposal`; `None` if proposal isn't a valid proposal
	/// index.
	pub fn locked_for(proposal: PropIndex) -> Option<T::Balance> {
		Self::deposit_of(proposal).map(|(d, l)| d * T::Balance::sa(l.len()))
	}

	/// Return true if `ref_index` is an on-going referendum.
	pub fn is_active_referendum(ref_index: ReferendumIndex) -> bool {
		<ReferendumInfoOf<T>>::exists(ref_index)
	}

	/// Get all referendums currently active.
	pub fn active_referendums() -> Vec<(ReferendumIndex, T::BlockNumber, T::Proposal, VoteThreshold)> {
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|(n, p, t)| (i, n, p, t)))
			.collect()
	}

	/// Get all referendums ready for tally at block `n`.
	pub fn maturing_referendums_at(n: T::BlockNumber) -> Vec<(ReferendumIndex, T::BlockNumber, T::Proposal, VoteThreshold)> {
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|(n, p, t)| (i, n, p, t)))
			.take_while(|&(_, block_number, _, _)| block_number == n)
			.collect()
	}

	/// Get the voters for the current proposal.
	pub fn tally(ref_index: ReferendumIndex) -> (T::Balance, T::Balance) {
		Self::voters_for(ref_index).iter()
			.map(|a| (<staking::Module<T>>::balance(a), Self::vote_of((ref_index, a.clone())).unwrap_or(false)/*defensive only: all items come from `voters`; for an item to be in `voters` there must be a vote registered; qed*/))
			.map(|(bal, vote)| if vote { (bal, Zero::zero()) } else { (Zero::zero(), bal) })
			.fold((Zero::zero(), Zero::zero()), |(a, b), (c, d)| (a + c, b + d))
	}

	// dispatching.

	/// Propose a sensitive action to be taken.
	fn propose(aux: &T::PublicAux, proposal: Box<T::Proposal>, value: T::Balance) {
		ensure!(value >= Self::minimum_deposit());
		ensure!(<staking::Module<T>>::deduct_unbonded(aux.ref_into(), value));

		let index = Self::public_prop_count();
		<PublicPropCount<T>>::put(index + 1);
		<DepositOf<T>>::insert(index, (value, vec![aux.ref_into().clone()]));

		let mut props = Self::public_props();
		props.push((index, (*proposal).clone(), aux.ref_into().clone()));
		<PublicProps<T>>::put(props);
	}

	/// Propose a sensitive action to be taken.
	fn second(aux: &T::PublicAux, proposal: PropIndex) {
		if let Some(mut deposit) = Self::deposit_of(proposal) {
			ensure!(<staking::Module<T>>::deduct_unbonded(aux.ref_into(), deposit.0));
			deposit.1.push(aux.ref_into().clone());
			<DepositOf<T>>::insert(proposal, deposit);
		} else {
			fail!("can only second an existing proposal");
		}
	}

	/// Vote in a referendum. If `approve_proposal` is true, the vote is to enact the proposal;
	/// false would be a vote to keep the status quo..
	fn vote(aux: &T::PublicAux, ref_index: ReferendumIndex, approve_proposal: bool) {
		if !Self::is_active_referendum(ref_index) {
			fail!("vote given for invalid referendum.")
		}
		if <staking::Module<T>>::balance(aux.ref_into()).is_zero() {
			fail!("transactor must have balance to signal approval.");
		}
		if !<VoteOf<T>>::exists(&(ref_index, aux.ref_into().clone())) {
			let mut voters = Self::voters_for(ref_index);
			voters.push(aux.ref_into().clone());
			<VotersFor<T>>::insert(ref_index, voters);
		}
		<VoteOf<T>>::insert(&(ref_index, aux.ref_into().clone()), approve_proposal);
	}

	/// Start a referendum.
	fn start_referendum(proposal: Box<T::Proposal>, vote_threshold: VoteThreshold) {
		let _ = Self::inject_referendum(<system::Module<T>>::block_number() + Self::voting_period(), *proposal, vote_threshold);
	}

	/// Remove a referendum.
	fn cancel_referendum(ref_index: ReferendumIndex) {
		Self::clear_referendum(ref_index);
	}

	// exposed mutables.

	/// Start a referendum. Can be called directly by the council.
	pub fn internal_start_referendum(proposal: T::Proposal, vote_threshold: VoteThreshold) {
		let _ = <Module<T>>::inject_referendum(<system::Module<T>>::block_number() + <Module<T>>::voting_period(), proposal, vote_threshold);
	}

	/// Remove a referendum. Can be called directly by the council.
	pub fn internal_cancel_referendum(ref_index: ReferendumIndex) {
		<Module<T>>::clear_referendum(ref_index);
	}

	// private.

	/// Start a referendum
	fn inject_referendum(
		end: T::BlockNumber,
		proposal: T::Proposal,
		vote_threshold: VoteThreshold
	) -> Result<ReferendumIndex, &'static str> {
		let ref_index = Self::referendum_count();
		if ref_index > 0 && Self::referendum_info(ref_index - 1).map(|i| i.0 > end).unwrap_or(false) {
			Err("Cannot inject a referendum that ends earlier than preceeding referendum")?
		}

		<ReferendumCount<T>>::put(ref_index + 1);
		<ReferendumInfoOf<T>>::insert(ref_index, (end, proposal, vote_threshold));
		Ok(ref_index)
	}

	/// Remove all info on a referendum.
	fn clear_referendum(ref_index: ReferendumIndex) {
		<ReferendumInfoOf<T>>::remove(ref_index);
		<VotersFor<T>>::remove(ref_index);
		for v in Self::voters_for(ref_index) {
			<VoteOf<T>>::remove((ref_index, v));
		}
	}

	/// Current era is ending; we should finish up any proposals.
	fn end_block(now: T::BlockNumber) -> Result<(), &'static str> {
		// pick out another public referendum if it's time.
		if (now % Self::launch_period()).is_zero() {
			let mut public_props = Self::public_props();
			if let Some((winner_index, _)) = public_props.iter()
				.enumerate()
				.max_by_key(|x| Self::locked_for((x.1).0).unwrap_or_else(Zero::zero)/*defensive only: All current public proposals have an amount locked*/)
			{
				let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
				if let Some((deposit, depositors)) = <DepositOf<T>>::take(prop_index) {//: (T::Balance, Vec<T::AccountId>) =
					// refund depositors
					for d in &depositors {
						<staking::Module<T>>::refund(d, deposit);
					}
					<PublicProps<T>>::put(public_props);
					Self::inject_referendum(now + Self::voting_period(), proposal, VoteThreshold::SuperMajorityApprove)?;
				} else {
					Err("depositors always exist for current proposals")?
				}
			}
		}

		// tally up votes for any expiring referenda.
		for (index, _, proposal, vote_threshold) in Self::maturing_referendums_at(now) {
			let (approve, against) = Self::tally(index);
			let total_stake = <staking::Module<T>>::total_stake();
			Self::clear_referendum(index);
			if vote_threshold.approved(approve, against, total_stake) {
				proposal.dispatch();
			}
			<NextTally<T>>::put(index + 1);
		}
		Ok(())
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
		if let Err(e) = Self::end_block(<system::Module<T>>::block_number()) {
			runtime_io::print(e);
		}
	}
}

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait> {
	pub launch_period: T::BlockNumber,
	pub voting_period: T::BlockNumber,
	pub minimum_deposit: T::Balance,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> GenesisConfig<T> {
	pub fn new() -> Self {
		GenesisConfig {
			launch_period: T::BlockNumber::sa(1),
			voting_period: T::BlockNumber::sa(1),
			minimum_deposit: T::Balance::sa(1),
		}
	}

	pub fn extended() -> Self {
		GenesisConfig {
			launch_period: T::BlockNumber::sa(1),
			voting_period: T::BlockNumber::sa(3),
			minimum_deposit: T::Balance::sa(1),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			launch_period: T::BlockNumber::sa(1000),
			voting_period: T::BlockNumber::sa(1000),
			minimum_deposit: T::Balance::sa(0),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildExternalities for GenesisConfig<T>
{
	fn build_externalities(self) -> runtime_io::TestExternalities {
		use codec::Slicable;
		use runtime_io::twox_128;

		map![
			twox_128(<LaunchPeriod<T>>::key()).to_vec() => self.launch_period.encode(),
			twox_128(<VotingPeriod<T>>::key()).to_vec() => self.voting_period.encode(),
			twox_128(<MinimumDeposit<T>>::key()).to_vec() => self.minimum_deposit.encode(),
			twox_128(<ReferendumCount<T>>::key()).to_vec() => (0 as ReferendumIndex).encode(),
			twox_128(<NextTally<T>>::key()).to_vec() => (0 as ReferendumIndex).encode(),
			twox_128(<PublicPropCount<T>>::key()).to_vec() => (0 as PropIndex).encode()
		]
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use primitives::BuildExternalities;
	use primitives::traits::{HasPublicAux, Identity};
	use primitives::testing::{Digest, Header};

	impl_outer_dispatch! {
		pub enum Proposal {
			Session = 0,
			Staking = 1,
			Democracy = 2,
		}
	}

	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl consensus::Trait for Test {
		type PublicAux = <Self as HasPublicAux>::PublicAux;
		type SessionKey = u64;
	}
	impl system::Trait for Test {
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = runtime_io::BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
	}
	impl session::Trait for Test {
		type ConvertAccountIdToSessionKey = Identity;
	}
	impl staking::Trait for Test {
		type Balance = u64;
		type DetermineContractAddress = staking::DummyContractAddressFor;
	}
	impl Trait for Test {
		type Proposal = Proposal;
	}

	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::<Test>::default().build_externalities();
		t.extend(consensus::GenesisConfig::<Test>{
			code: vec![],
			authorities: vec![],
		}.build_externalities());
		t.extend(session::GenesisConfig::<Test>{
			session_length: 1,		//??? or 2?
			validators: vec![10, 20],
		}.build_externalities());
		t.extend(staking::GenesisConfig::<Test>{
			sessions_per_era: 1,
			current_era: 0,
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
			intentions: vec![],
			validator_count: 2,
			bonding_duration: 3,
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
		}.build_externalities());
		t.extend(GenesisConfig::<Test>{
			launch_period: 1,
			voting_period: 1,
			minimum_deposit: 1,
		}.build_externalities());
		t
	}

	type System = system::Module<Test>;
	type Session = session::Module<Test>;
	type Staking = staking::Module<Test>;
	type Democracy = Module<Test>;

	#[test]
	fn params_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Democracy::launch_period(), 1);
			assert_eq!(Democracy::voting_period(), 1);
			assert_eq!(Democracy::minimum_deposit(), 1);
			assert_eq!(Democracy::referendum_count(), 0);
			assert_eq!(Staking::sessions_per_era(), 1);
			assert_eq!(Staking::total_stake(), 210);
		});
	}

	fn propose_sessions_per_era(who: u64, value: u64, locked: u64) {
		Democracy::propose(&who, Box::new(Proposal::Staking(staking::PrivCall::set_sessions_per_era(value))), locked);
	}

	#[test]
	fn locked_for_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 2);
			propose_sessions_per_era(1, 4, 4);
			propose_sessions_per_era(1, 3, 3);
			assert_eq!(Democracy::locked_for(0), Some(2));
			assert_eq!(Democracy::locked_for(1), Some(4));
			assert_eq!(Democracy::locked_for(2), Some(3));
		});
	}

	#[test]
	fn single_proposal_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 1);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(2);
			let r = 0;
			Democracy::vote(&1, r, true);

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), Some(true));
			assert_eq!(Democracy::tally(r), (10, 0));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 2);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_taken() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 5);
			Democracy::second(&2, 0);
			Democracy::second(&5, 0);
			Democracy::second(&5, 0);
			Democracy::second(&5, 0);
			assert_eq!(Staking::balance(&1), 5);
			assert_eq!(Staking::balance(&2), 15);
			assert_eq!(Staking::balance(&5), 35);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_returned() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 5);
			Democracy::second(&2, 0);
			Democracy::second(&5, 0);
			Democracy::second(&5, 0);
			Democracy::second(&5, 0);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Staking::balance(&1), 10);
			assert_eq!(Staking::balance(&2), 20);
			assert_eq!(Staking::balance(&5), 50);
		});
	}

	#[test]
	fn proposal_with_deposit_below_minimum_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 0);
			assert_eq!(Democracy::locked_for(0), None);
		});
	}

	#[test]
	fn poor_proposer_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(1, 2, 11);
			assert_eq!(Democracy::locked_for(0), None);
		});
	}

	#[test]
	fn poor_seconder_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			propose_sessions_per_era(2, 2, 11);
			Democracy::second(&1, 0);
			assert_eq!(Democracy::locked_for(0), Some(11));
		});
	}

	fn propose_bonding_duration(who: u64, value: u64, locked: u64) {
		Democracy::propose(&who, Box::new(Proposal::Staking(staking::PrivCall::set_bonding_duration(value))), locked);
	}

	#[test]
	fn runners_up_should_come_after() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(0);
			propose_bonding_duration(1, 2, 2);
			propose_bonding_duration(1, 4, 4);
			propose_bonding_duration(1, 3, 3);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(1);
			Democracy::vote(&1, 0, true);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();
			assert_eq!(Staking::bonding_duration(), 4);

			System::set_block_number(2);
			Democracy::vote(&1, 1, true);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();
			assert_eq!(Staking::bonding_duration(), 3);

			System::set_block_number(3);
			Democracy::vote(&1, 2, true);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();
			assert_eq!(Staking::bonding_duration(), 2);
		});
	}

	fn sessions_per_era_proposal(value: u64) -> Proposal {
		Proposal::Staking(staking::PrivCall::set_sessions_per_era(value))
	}

	#[test]
	fn simple_passing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&1, r, true);

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), Some(true));
			assert_eq!(Democracy::tally(r), (10, 0));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 2);
		});
	}

	#[test]
	fn cancel_referendum_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&1, r, true);
			Democracy::cancel_referendum(r);

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 1);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&1, r, false);

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), Some(false));
			assert_eq!(Democracy::tally(r), (0, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 1);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&1, r, true);
			Democracy::vote(&2, r, false);
			Democracy::vote(&3, r, false);
			Democracy::vote(&4, r, true);
			Democracy::vote(&5, r, false);
			Democracy::vote(&6, r, true);

			assert_eq!(Democracy::tally(r), (110, 100));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 2);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&5, r, false);
			Democracy::vote(&6, r, true);

			assert_eq!(Democracy::tally(r), (60, 50));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 1);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Staking::era_length(), 1);
			assert_eq!(Staking::total_stake(), 210);

			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, sessions_per_era_proposal(2), VoteThreshold::SuperMajorityApprove).unwrap();
			Democracy::vote(&4, r, true);
			Democracy::vote(&5, r, false);
			Democracy::vote(&6, r, true);

			assert_eq!(Democracy::tally(r), (100, 50));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			Staking::check_new_era();

			assert_eq!(Staking::era_length(), 2);
		});
	}
}
