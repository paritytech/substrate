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

//! Council voting system.

use rstd::prelude::*;
use rstd::borrow::Borrow;
//use runtime_io::{twox_128, TestExternalities};
use primitives::{Zero, One, Bounded, SimpleArithmetic, Executable, RefInto, Hashing};
use runtime_support::{StorageValue, StorageMap, Parameter};
use super::{Trait, system, democracy, Module as Council};
use democracy::IsCancelReferendum;

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn propose(aux, proposal: Box<T::Proposal>) = 0;
		fn vote(aux, proposal: T::Hash, approve: bool) = 1;
		fn veto(aux, proposal_hash: T::Hash) = 2;
	}
	pub enum PrivCall {
		fn set_cooloff_period(blocks: T::BlockNumber) = 0;
		fn set_voting_period(blocks: T::BlockNumber) = 1;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	pub CooloffPeriod get(cooloff_period): b"cov:cooloff" => required T::BlockNumber;
	pub VotingPeriod get(voting_period): b"cov:period" => required T::BlockNumber;
	pub Proposals get(proposals): b"cov:prs" => default Vec<(T::BlockNumber, T::Hash)>; // ordered by expiry.
	pub ProposalOf get(proposal_of): b"cov:pro" => map [ T::Hash => T::Proposal ];
	pub ProposalVoters get(proposal_voters): b"cov:voters:" => default map [ T::Hash => Vec<T::AccountId> ];
	pub CouncilVoteOf get(vote_of): b"cov:vote:" => map [ (T::Hash, T::AccountId) => bool ];
	pub VetoedProposal get(veto_of): b"cov:veto:" => map [ T::Hash => (T::BlockNumber, Vec<T::AccountId>) ];
}

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

	// Dispatch
	fn propose(aux: &T::PublicAux, proposal: Box<T::Proposal>) {
		let expiry = <system::Module<T>>::block_number() + Self::voting_period();
		assert!(Self::will_still_be_councillor_at(aux.ref_into(), expiry));

		let proposal_hash = T::Hashing::hash_of(&proposal);

		assert!(!Self::is_vetoed(&proposal_hash));

		let mut proposals = Self::proposals();
		proposals.push((expiry, proposal_hash));
		proposals.sort_by_key(|&(expiry, _)| expiry);
		Self::set_proposals(&proposals);

		<ProposalOf<T>>::insert(proposal_hash, *proposal);
		<ProposalVoters<T>>::insert(proposal_hash, vec![aux.ref_into().clone()]);
		<CouncilVoteOf<T>>::insert((proposal_hash, aux.ref_into().clone()), true);
	}

	fn vote(aux: &T::PublicAux, proposal: T::Hash, approve: bool) {
		if Self::vote_of((proposal, aux.ref_into().clone())).is_none() {
			let mut voters = Self::proposal_voters(&proposal);
			voters.push(aux.ref_into().clone());
			<ProposalVoters<T>>::insert(proposal, voters);
		}
		<CouncilVoteOf<T>>::insert((proposal, aux.ref_into().clone()), approve);
	}

	fn veto(aux: &T::PublicAux, proposal_hash: T::Hash) {
		assert!(Self::is_councillor(aux.ref_into()), "only councillors may veto council proposals");
		assert!(<ProposalVoters<T>>::exists(&proposal_hash), "proposal must exist to be vetoed");

		let mut existing_vetoers = Self::veto_of(&proposal_hash)
			.map(|pair| pair.1)
			.unwrap_or_else(Vec::new);
		let insert_position = existing_vetoers.binary_search(aux.ref_into())
			.expect_err("a councillor may not veto a proposal twice");
		existing_vetoers.insert(insert_position, aux.ref_into().clone());
		Self::set_veto_of(&proposal_hash, <system::Module<T>>::block_number() + Self::cooloff_period(), existing_vetoers);

		Self::set_proposals(&Self::proposals().into_iter().filter(|&(_, h)| h != proposal_hash).collect::<Vec<_>>());
		<ProposalVoters<T>>::remove(proposal_hash);
		<ProposalOf<T>>::remove(proposal_hash);
		for (c, _) in <Council<T>>::active_council() {
			<CouncilVoteOf<T>>::remove((proposal_hash, c));
		}
	}

	fn set_cooloff_period(blocks: T::BlockNumber) {
		<CooloffPeriod<T>>::put(blocks);
	}

	fn set_voting_period(blocks: T::BlockNumber) {
		<VotingPeriod<T>>::put(blocks);
	}

	// private


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
		let mut proposals = Self::proposals();
		match proposals.first() {
			Some(&(expiry, hash)) if expiry == n => {
				// yes this is horrible, but fixing it will need substantial work in storage.
				Self::set_proposals(&proposals[1..].to_vec());
				let proposal = <ProposalOf<T>>::take(hash).expect("all queued proposal hashes must have associated proposals");
				Some((proposal, hash))
			}
			_ => None,
		}
	}

	fn end_block(now: T::BlockNumber) {
		while let Some((proposal, proposal_hash)) = Self::take_proposal_if_expiring_at(now) {
			let tally = Self::take_tally(&proposal_hash);
			if let Some(ref_index) = proposal.is_cancel_referendum() {
				if let (_, 0, 0) = tally {
					<democracy::Module<T>>::internal_cancel_referendum(ref_index);
				}
			} else {
				if tally.0 > tally.1 + tally.2 {
					Self::kill_veto_of(&proposal_hash);
					match tally {
						(_, 0, 0) => <democracy::Module<T>>::internal_start_referendum(proposal, democracy::VoteThreshold::SuperMajorityAgainst),
						_ => <democracy::Module<T>>::internal_start_referendum(proposal, democracy::VoteThreshold::SimpleMajority),
					};
				}
			}
		}
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
		Self::end_block(<system::Module<T>>::block_number());
	}
}

/*

#[cfg(test)]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use keyring::Keyring::{Alice, Bob, Charlie};
	use codec::Joiner;
	use runtime::{council, democracy};

	pub fn externalities() -> TestExternalities {
		let expiry: BlockNumber = 10;
		let extras: TestExternalities = map![
			twox_128(council::ActiveCouncil::key()).to_vec() => vec![].and(&vec![
				(Alice.to_raw_public(), expiry),
				(Bob.into(), expiry),
				(Charlie.into(), expiry)
			]),
			twox_128(CooloffPeriod::key()).to_vec() => vec![].and(&2u64),
			twox_128(VotingPeriod::key()).to_vec() => vec![].and(&1u64),
			twox_128(democracy::VotingPeriod::key()).to_vec() => vec![].and(&3u64)
		];
		council::testing::externalities()
			.into_iter().chain(extras.into_iter()).collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring::{Alice, Bob, Charlie, Dave};
	use demo_primitives::AccountId;
	use runtime::democracy::VoteThreshold;
	use runtime::{staking, council, democracy};
	use super::public::Dispatch;
	use super::privileged::Dispatch as PrivDispatch;

	fn new_test_ext() -> TestExternalities {
		testing::externalities()
	}

	#[test]
	fn basic_environment_works() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			assert_eq!(staking::bonding_duration(), 0);
			assert_eq!(cooloff_period(), 2);
			assert_eq!(voting_period(), 1);
			assert_eq!(will_still_be_councillor_at(&Alice, 1), true);
			assert_eq!(will_still_be_councillor_at(&Alice, 10), false);
			assert_eq!(will_still_be_councillor_at(&Dave, 10), false);
			assert_eq!(is_councillor(&Alice), true);
			assert_eq!(is_councillor(&Dave), false);
			assert_eq!(proposals(), Vec::<(BlockNumber, ProposalHash)>::new());
			assert_eq!(proposal_voters(ProposalHash::default()), Vec::<AccountId>::new());
			assert_eq!(is_vetoed(&ProposalHash::default()), false);
			assert_eq!(vote_of((*Alice, ProposalHash::default())), None);
			assert_eq!(tally(&ProposalHash::default()), (0, 0, 3));
		});
	}

	fn sessions_per_era_proposal(value: u64) -> Proposal {
		Proposal::Staking(staking::privileged::Call::set_sessions_per_era(value))
	}

	fn bonding_duration_proposal(value: u64) -> Proposal {
		Proposal::Staking(staking::privileged::Call::set_bonding_duration(value))
	}

	fn cancel_referendum_proposal(id: u32) -> Proposal {
		Proposal::Democracy(democracy::privileged::Call::cancel_referendum(id))
	}

	#[test]
	fn referendum_cancellation_should_work_when_unanimous() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			democracy::internal::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(cancellation));
			staking::public_pass_from_payment(&Bob).vote(hash, true);
			staking::public_pass_from_payment(&Charlie).vote(hash, true);
			assert_eq!(proposals(), vec![(2, hash)]);
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![]);
			assert_eq!(staking::bonding_duration(), 0);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_not_unanimous() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			democracy::internal::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(cancellation));
			staking::public_pass_from_payment(&Bob).vote(hash, true);
			staking::public_pass_from_payment(&Charlie).vote(hash, false);
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_abstentions() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			democracy::internal::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);

			let cancellation = cancel_referendum_proposal(0);
			let hash = cancellation.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(cancellation));
			staking::public_pass_from_payment(&Bob).vote(hash, true);
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);
		});
	}

	#[test]
	fn veto_should_work() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	#[should_panic]
	fn double_veto_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);

			system::testing::set_block_number(3);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);
		});
	}

	#[test]
	#[should_panic]
	fn retry_in_cooloff_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);

			system::testing::set_block_number(2);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
		});
	}

	#[test]
	fn retry_after_cooloff_should_work() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);

			system::testing::set_block_number(3);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).vote(hash, false);
			staking::public_pass_from_payment(&Charlie).vote(hash, true);
			internal::end_block(3);

			system::testing::set_block_number(4);
			internal::end_block(4);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 7, bonding_duration_proposal(42), VoteThreshold::SimpleMajority)]);
		});
	}

	#[test]
	fn alternative_double_veto_should_work() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).veto(hash);

			system::testing::set_block_number(3);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Charlie).veto(hash);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn simple_propose_should_work() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			let hash = proposal.blake2_256();
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			assert_eq!(proposals().len(), 1);
			assert_eq!(proposal_voters(&hash), vec![Alice.to_raw_public()]);
			assert_eq!(vote_of((hash, *Alice)), Some(true));
			assert_eq!(tally(&hash), (1, 0, 2));
		});
	}

	#[test]
	fn unvoted_proposal_should_expire_without_action() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			assert_eq!(tally(&proposal.blake2_256()), (1, 0, 2));
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn unanimous_proposal_should_expire_with_biased_referendum() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).vote(proposal.blake2_256(), true);
			staking::public_pass_from_payment(&Charlie).vote(proposal.blake2_256(), true);
			assert_eq!(tally(&proposal.blake2_256()), (3, 0, 0));
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 5, proposal, VoteThreshold::SuperMajorityAgainst)]);
		});
	}

	#[test]
	fn majority_proposal_should_expire_with_unbiased_referendum() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			staking::public_pass_from_payment(&Alice).propose(Box::new(proposal.clone()));
			staking::public_pass_from_payment(&Bob).vote(proposal.blake2_256(), true);
			staking::public_pass_from_payment(&Charlie).vote(proposal.blake2_256(), false);
			assert_eq!(tally(&proposal.blake2_256()), (2, 1, 0));
			internal::end_block(1);

			system::testing::set_block_number(2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 5, proposal, VoteThreshold::SimpleMajority)]);
		});
	}

	#[test]
	#[should_panic]
	fn propose_by_public_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			system::testing::set_block_number(1);
			let proposal = bonding_duration_proposal(42);
			staking::public_pass_from_payment(&Dave).propose(Box::new(proposal));
		});
	}
}
*/
