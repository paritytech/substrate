// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Council voting system.

use rstd::prelude::*;
use rstd::borrow::Borrow;
use primitives::traits::{Hash, As, Zero};
use runtime_io::print;
use srml_support::dispatch::Result;
use srml_support::{StorageValue, StorageMap, IsSubType, decl_module, decl_storage, decl_event, ensure};
use {system, democracy};
use super::{Trait as CouncilTrait, Module as Council};
use system::ensure_signed;

pub trait Trait: CouncilTrait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn propose(origin, proposal: Box<T::Proposal>) {
			let who = ensure_signed(origin)?;

			let expiry = <system::Module<T>>::block_number() + Self::voting_period();
			ensure!(Self::will_still_be_councillor_at(&who, expiry), "proposer would not be on council");

			let proposal_hash = T::Hashing::hash_of(&proposal);

			ensure!(!<ProposalOf<T>>::exists(proposal_hash), "duplicate proposals not allowed");
			ensure!(!Self::is_vetoed(&proposal_hash), "proposal is vetoed");

			let mut proposals = Self::proposals();
			proposals.push((expiry, proposal_hash));
			proposals.sort_by_key(|&(expiry, _)| expiry);
			Self::set_proposals(&proposals);

			<ProposalOf<T>>::insert(proposal_hash, *proposal);
			<ProposalVoters<T>>::insert(proposal_hash, vec![who.clone()]);
			<CouncilVoteOf<T>>::insert((proposal_hash, who.clone()), true);
		}

		fn vote(origin, proposal: T::Hash, approve: bool) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_councillor(&who), "only councillors may vote on council proposals");

			if Self::vote_of((proposal, who.clone())).is_none() {
				<ProposalVoters<T>>::mutate(proposal, |voters| voters.push(who.clone()));
			}
			<CouncilVoteOf<T>>::insert((proposal, who), approve);
		}

		fn veto(origin, proposal_hash: T::Hash) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_councillor(&who), "only councillors may veto council proposals");
			ensure!(<ProposalVoters<T>>::exists(&proposal_hash), "proposal must exist to be vetoed");

			let mut existing_vetoers = Self::veto_of(&proposal_hash)
				.map(|pair| pair.1)
				.unwrap_or_else(Vec::new);
			let insert_position = existing_vetoers.binary_search(&who)
				.err().ok_or("a councillor may not veto a proposal twice")?;
			existing_vetoers.insert(insert_position, who);
			Self::set_veto_of(
				&proposal_hash,
				<system::Module<T>>::block_number() + Self::cooloff_period(),
				existing_vetoers
			);

			Self::set_proposals(
				&Self::proposals().into_iter().filter(|&(_, h)| h != proposal_hash
			).collect::<Vec<_>>());
			<ProposalVoters<T>>::remove(proposal_hash);
			<ProposalOf<T>>::remove(proposal_hash);
			for (c, _) in <Council<T>>::active_council() {
				<CouncilVoteOf<T>>::remove((proposal_hash, c));
			}
		}

		fn set_cooloff_period(#[compact] blocks: T::BlockNumber) {
			<CooloffPeriod<T>>::put(blocks);
		}

		fn set_voting_period(#[compact] blocks: T::BlockNumber) {
			<VotingPeriod<T>>::put(blocks);
		}

		fn on_finalize(n: T::BlockNumber) {
			if let Err(e) = Self::end_block(n) {
				print("Guru meditation");
				print(e);
			}
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as CouncilVoting {
		pub CooloffPeriod get(cooloff_period) config(): T::BlockNumber = T::BlockNumber::sa(1000);
		pub VotingPeriod get(voting_period) config(): T::BlockNumber = T::BlockNumber::sa(3);
		/// Number of blocks by which to delay enactment of successful, non-unanimous-council-instigated referendum proposals.
		pub EnactDelayPeriod get(enact_delay_period) config(): T::BlockNumber = T::BlockNumber::sa(0);
		pub Proposals get(proposals) build(|_| vec![]): Vec<(T::BlockNumber, T::Hash)>; // ordered by expiry.
		pub ProposalOf get(proposal_of): map T::Hash => Option<T::Proposal>;
		pub ProposalVoters get(proposal_voters): map T::Hash => Vec<T::AccountId>;
		pub CouncilVoteOf get(vote_of): map (T::Hash, T::AccountId) => Option<bool>;
		pub VetoedProposal get(veto_of): map T::Hash => Option<(T::BlockNumber, Vec<T::AccountId>)>;
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::Hash {
		/// A voting tally has happened for a referendum cancellation vote.
		/// Last three are yes, no, abstain counts.
		TallyCancelation(Hash, u32, u32, u32),
		/// A voting tally has happened for a referendum vote.
		/// Last three are yes, no, abstain counts.
		TallyReferendum(Hash, u32, u32, u32),
	}
);

impl<T: Trait> Module<T> {
	pub fn is_vetoed<B: Borrow<T::Hash>>(proposal: B) -> bool {
		Self::veto_of(proposal.borrow())
			.map(|(expiry, _): (T::BlockNumber, Vec<T::AccountId>)| <system::Module<T>>::block_number() < expiry)
			.unwrap_or(false)
	}

	pub fn will_still_be_councillor_at(who: &T::AccountId, n: T::BlockNumber) -> bool {
		<Council<T>>::active_council().iter()
			.find(|&&(ref a, _)| a == who)
			.map(|&(_, expires)| expires > n)
			.unwrap_or(false)
	}

	pub fn is_councillor(who: &T::AccountId) -> bool {
		<Council<T>>::active_council().iter()
			.any(|&(ref a, _)| a == who)
	}

	pub fn tally(proposal_hash: &T::Hash) -> (u32, u32, u32) {
		Self::generic_tally(proposal_hash, |w: &T::AccountId, p: &T::Hash| Self::vote_of((*p, w.clone())))
	}

	// Private
	fn set_veto_of(proposal: &T::Hash, expiry: T::BlockNumber, vetoers: Vec<T::AccountId>) {
		<VetoedProposal<T>>::insert(proposal, (expiry, vetoers));
	}

	fn kill_veto_of(proposal: &T::Hash) {
		<VetoedProposal<T>>::remove(proposal);
	}

	fn take_tally(proposal_hash: &T::Hash) -> (u32, u32, u32) {
		Self::generic_tally(proposal_hash, |w: &T::AccountId, p: &T::Hash| <CouncilVoteOf<T>>::take((*p, w.clone())))
	}

	fn generic_tally<F: Fn(&T::AccountId, &T::Hash) -> Option<bool>>(proposal_hash: &T::Hash, vote_of: F) -> (u32, u32, u32) {
		let c = <Council<T>>::active_council();
		let (approve, reject) = c.iter()
			.filter_map(|&(ref a, _)| vote_of(a, proposal_hash))
			.map(|approve| if approve { (1, 0) } else { (0, 1) })
			.fold((0, 0), |(a, b), (c, d)| (a + c, b + d));
		(approve, reject, c.len() as u32 - approve - reject)
	}

	fn set_proposals(p: &Vec<(T::BlockNumber, T::Hash)>) {
		<Proposals<T>>::put(p);
	}

	fn take_proposal_if_expiring_at(n: T::BlockNumber) -> Option<(T::Proposal, T::Hash)> {
		let proposals = Self::proposals();
		match proposals.first() {
			Some(&(expiry, hash)) if expiry == n => {
				// yes this is horrible, but fixing it will need substantial work in storage.
				Self::set_proposals(&proposals[1..].to_vec());
				<ProposalOf<T>>::take(hash).map(|p| (p, hash))	/* defensive only: all queued proposal hashes must have associated proposals*/
			}
			_ => None,
		}
	}

	fn end_block(now: T::BlockNumber) -> Result {
		while let Some((proposal, proposal_hash)) = Self::take_proposal_if_expiring_at(now) {
			let tally = Self::take_tally(&proposal_hash);
			if let Some(&democracy::Call::cancel_referendum(ref_index)) = IsSubType::<democracy::Module<T>>::is_aux_sub_type(&proposal) {
				Self::deposit_event(RawEvent::TallyCancelation(proposal_hash, tally.0, tally.1, tally.2));
				if let (_, 0, 0) = tally {
					<democracy::Module<T>>::internal_cancel_referendum(ref_index.into());
				}
			} else {
				Self::deposit_event(RawEvent::TallyReferendum(proposal_hash.clone(), tally.0, tally.1, tally.2));
				if tally.0 > tally.1 + tally.2 {
					Self::kill_veto_of(&proposal_hash);
					// If there were no nay-votes from the council, then it's weakly uncontroversial; we enact immediately.
					let period = match tally.1 {
						0 => Zero::zero(),
						_ => Self::enact_delay_period(),
					};
					// If all council members voted yes, then it's strongly uncontroversial; we require a negative
					// super-majority at referendum in order to defeat it.
					let threshold = match tally {
						(_, 0, 0) => democracy::VoteThreshold::SuperMajorityAgainst,
						_ => democracy::VoteThreshold::SimpleMajority,
					};
					<democracy::Module<T>>::internal_start_referendum(proposal, threshold, period).map(|_| ())?;
				}
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::*;
	use crate::tests::{Call, Origin};
	use srml_support::{Hashable, assert_ok, assert_noop};
	use democracy::{ReferendumInfo, VoteThreshold};

	#[test]
	fn basic_environment_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(CouncilVoting::cooloff_period(), 2);
			assert_eq!(CouncilVoting::voting_period(), 1);
			assert_eq!(CouncilVoting::will_still_be_councillor_at(&1, 1), true);
			assert_eq!(CouncilVoting::will_still_be_councillor_at(&1, 10), false);
			assert_eq!(CouncilVoting::will_still_be_councillor_at(&4, 10), false);
			assert_eq!(CouncilVoting::is_councillor(&1), true);
			assert_eq!(CouncilVoting::is_councillor(&4), false);
			assert_eq!(CouncilVoting::proposals(), Vec::<(u64, H256)>::new());
			assert_eq!(CouncilVoting::proposal_voters(H256::default()), Vec::<u64>::new());
			assert_eq!(CouncilVoting::is_vetoed(&H256::default()), false);
			assert_eq!(CouncilVoting::vote_of((H256::default(), 1)), None);
			assert_eq!(CouncilVoting::tally(&H256::default()), (0, 0, 3));
		});
	}

	fn set_balance_proposal(value: u64) -> Call {
		Call::Balances(balances::Call::set_balance(42, value.into(), 0))
	}

	fn cancel_referendum_proposal(id: u32) -> Call {
		Call::Democracy(democracy::Call::cancel_referendum(id.into()))
	}

	#[test]
	fn referendum_cancellation_should_work_when_unanimous() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(Democracy::internal_start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove, 0), 0);
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(4, proposal, VoteThreshold::SuperMajorityApprove, 0))]);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(cancellation)));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), hash, true));
			assert_ok!(CouncilVoting::vote(Origin::signed(3), hash, true));
			assert_eq!(CouncilVoting::proposals(), vec![(2, hash)]);
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(Democracy::active_referendums(), vec![]);
			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_not_unanimous() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(Democracy::internal_start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove, 0), 0);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(cancellation)));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), hash, true));
			assert_ok!(CouncilVoting::vote(Origin::signed(3), hash, false));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(4, proposal, VoteThreshold::SuperMajorityApprove, 0))]);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_abstentions() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(Democracy::internal_start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove, 0), 0);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(cancellation)));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), hash, true));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(4, proposal, VoteThreshold::SuperMajorityApprove, 0))]);
		});
	}

	#[test]
	fn veto_should_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(2), hash));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn double_veto_should_not_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(2), hash));

			System::set_block_number(3);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_noop!(CouncilVoting::veto(Origin::signed(2), hash), "a councillor may not veto a proposal twice");
		});
	}

	#[test]
	fn retry_in_cooloff_should_not_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(2), hash));

			System::set_block_number(2);
			assert_noop!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())), "proposal is vetoed");
		});
	}

	#[test]
	fn retry_after_cooloff_should_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(2), hash));

			System::set_block_number(3);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), hash, false));
			assert_ok!(CouncilVoting::vote(Origin::signed(3), hash, true));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(4);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(7, set_balance_proposal(42), VoteThreshold::SimpleMajority, 0))]);
		});
	}

	#[test]
	fn alternative_double_veto_should_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(2), hash));

			System::set_block_number(3);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::veto(Origin::signed(3), hash));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn simple_propose_should_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_eq!(CouncilVoting::proposals().len(), 1);
			assert_eq!(CouncilVoting::proposal_voters(&hash), vec![1]);
			assert_eq!(CouncilVoting::vote_of((hash, 1)), Some(true));
			assert_eq!(CouncilVoting::tally(&hash), (1, 0, 2));
		});
	}

	#[test]
	fn unvoted_proposal_should_expire_without_action() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_eq!(CouncilVoting::tally(&proposal.blake2_256().into()), (1, 0, 2));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn unanimous_proposal_should_expire_with_biased_referendum() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), proposal.blake2_256().into(), true));
			assert_ok!(CouncilVoting::vote(Origin::signed(3), proposal.blake2_256().into(), true));
			assert_eq!(CouncilVoting::tally(&proposal.blake2_256().into()), (3, 0, 0));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(5, proposal, VoteThreshold::SuperMajorityAgainst, 0))]);
		});
	}

	#[test]
	fn majority_proposal_should_expire_with_unbiased_referendum() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_ok!(CouncilVoting::vote(Origin::signed(2), proposal.blake2_256().into(), true));
			assert_ok!(CouncilVoting::vote(Origin::signed(3), proposal.blake2_256().into(), false));
			assert_eq!(CouncilVoting::tally(&proposal.blake2_256().into()), (2, 1, 0));
			assert_ok!(CouncilVoting::end_block(System::block_number()));

			System::set_block_number(2);
			assert_ok!(CouncilVoting::end_block(System::block_number()));
			assert_eq!(CouncilVoting::proposals().len(), 0);
			assert_eq!(Democracy::active_referendums(), vec![(0, ReferendumInfo::new(5, proposal, VoteThreshold::SimpleMajority, 0))]);
		});
	}

	#[test]
	fn propose_by_public_should_not_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_noop!(CouncilVoting::propose(Origin::signed(4), Box::new(proposal)), "proposer would not be on council");
		});
	}

	#[test]
	fn vote_by_public_should_not_work() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_ok!(CouncilVoting::propose(Origin::signed(1), Box::new(proposal.clone())));
			assert_noop!(CouncilVoting::vote(Origin::signed(4), proposal.blake2_256().into(), true), "only councillors may vote on council proposals");
		});
	}
}
