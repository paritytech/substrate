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
use codec::{KeyedVec, Slicable, Input, NonTrivialSlicable};
use runtime_support::Hashable;
use runtime_support::storage;
use demo_primitives::{Proposal, AccountId, Hash, BlockNumber};
use runtime::{system, democracy, council};
use runtime::staking::Balance;

type ProposalHash = [u8; 32];

pub const COOLOFF_PERIOD: &[u8] = b"cov:cooloff";		// BlockNumber
pub const VOTING_PERIOD: &[u8] = b"cov:period";			// BlockNumber

pub const PROPOSALS: &[u8] = b"cov:prs";				// Vec<(expiry: BlockNumber, ProposalHash)> ordered by expiry.
pub const PROPOSAL_OF: &[u8] = b"cov:pro";				// ProposalHash -> Proposal
pub const PROPOSAL_VOTERS: &[u8] = b"cov:voters:";		// ProposalHash -> Vec<AccountId>
pub const COUNCIL_VOTE_OF: &[u8] = b"cov:vote:";		// (ProposalHash, AccountId) -> bool
pub const VETOED_PROPOSAL: &[u8] = b"cov:veto:";		// ProposalHash -> (BlockNumber, sorted_vetoers: Vec<AccountId>)

pub fn cooloff_period() -> BlockNumber {
	storage::get(COOLOFF_PERIOD).expect("all parameters must be defined")
}

pub fn voting_period() -> BlockNumber {
	storage::get(VOTING_PERIOD).expect("all parameters must be defined")
}

pub fn proposals() -> Vec<(BlockNumber, ProposalHash)> {
	storage::get_or_default(PROPOSALS)
}

pub fn is_vetoed(proposal: &ProposalHash) -> bool {
	storage::get(&proposal.to_keyed_vec(VETOED_PROPOSAL))
		.map(|(expiry, _): (BlockNumber, Vec<AccountId>)| system::block_number() < expiry)
		.unwrap_or(false)
}

pub fn veto_of(proposal: &ProposalHash) -> Option<(BlockNumber, Vec<AccountId>)> {
	storage::get(&proposal.to_keyed_vec(VETOED_PROPOSAL))
}

fn set_veto_of(proposal: &ProposalHash, expiry: BlockNumber, vetoers: Vec<AccountId>) {
	storage::put(&proposal.to_keyed_vec(VETOED_PROPOSAL), &(expiry, vetoers))
}

fn kill_veto_of(proposal: &ProposalHash) {
	storage::kill(&proposal.to_keyed_vec(VETOED_PROPOSAL))
}

pub fn will_still_be_councillor_at(who: &AccountId, n: BlockNumber) -> bool {
	council::active_council().iter()
		.find(|&&(ref a, _)| a == who)
		.map(|&(_, expires)| expires > n)
		.unwrap_or(false)
}

pub fn is_councillor(who: &AccountId) -> bool {
	council::active_council().iter()
		.any(|&(ref a, _)| a == who)
}

pub fn vote_of(who: &AccountId, proposal: &ProposalHash) -> Option<bool> {
	storage::get(&(*proposal, *who).to_keyed_vec(COUNCIL_VOTE_OF))
}

pub fn proposal_voters(proposal: &ProposalHash) -> Vec<AccountId> {
	storage::get_or_default(&proposal.to_keyed_vec(PROPOSAL_VOTERS))
}

pub fn tally(proposal_hash: &ProposalHash) -> (u32, u32, u32) {
	generic_tally(proposal_hash, |w: &AccountId, p: &ProposalHash| storage::get(&(*p, *w).to_keyed_vec(COUNCIL_VOTE_OF)))
}

fn take_tally(proposal_hash: &ProposalHash) -> (u32, u32, u32) {
	generic_tally(proposal_hash, |w: &AccountId, p: &ProposalHash| storage::get(&(*p, *w).to_keyed_vec(COUNCIL_VOTE_OF)))
}

fn generic_tally<F: Fn(&AccountId, &ProposalHash) -> Option<bool>>(proposal_hash: &ProposalHash, vote_of: F) -> (u32, u32, u32) {
	let c = council::active_council();
	let (approve, reject) = c.iter()
		.filter_map(|&(ref a, _)| vote_of(a, proposal_hash))
		.map(|approve| if approve { (1, 0) } else { (0, 1) })
		.fold((0, 0), |(a, b), (c, d)| (a + c, b + d));
	(approve, reject, c.len() as u32 - approve - reject)
}

fn set_proposals(p: &Vec<(BlockNumber, ProposalHash)>) {
	storage::put(PROPOSALS, p)
}

fn take_proposal_if_expiring_at(n: BlockNumber) -> Option<(Proposal, ProposalHash)> {
	let mut proposals = proposals();
	match proposals.first() {
		Some(&(expiry, hash)) if expiry == n => {
			// yes this is horrible, but fixing it will need substantial work in storage.
			set_proposals(&proposals[1..].to_vec());
			let proposal = storage::take(&hash.to_keyed_vec(PROPOSAL_OF)).expect("all queued proposal hashes must have associated proposals");
			Some((proposal, hash))
		}
		_ => None,
	}
}

pub mod public {
	use super::*;

	pub fn propose(signed: &AccountId, proposal: &Proposal) {
		let expiry = system::block_number() + voting_period();
		assert!(will_still_be_councillor_at(signed, expiry));

		let proposal_hash = proposal.blake2_256();

		assert!(!is_vetoed(&proposal_hash));

		let mut proposals = proposals();
		proposals.push((expiry, proposal_hash));
		proposals.sort_by_key(|&(expiry, _)| expiry);
		set_proposals(&proposals);

		storage::put(&proposal_hash.to_keyed_vec(PROPOSAL_OF), proposal);
		storage::put(&proposal_hash.to_keyed_vec(PROPOSAL_VOTERS), &vec![*signed]);
		storage::put(&(proposal_hash, *signed).to_keyed_vec(COUNCIL_VOTE_OF), &true);
	}

	pub fn vote(signed: &AccountId, proposal: &ProposalHash, approve: bool) {
		if vote_of(signed, proposal).is_none() {
			let mut voters = proposal_voters(proposal);
			voters.push(*signed);
			storage::put(&proposal.to_keyed_vec(PROPOSAL_VOTERS), &voters);
		}
		storage::put(&(*proposal, *signed).to_keyed_vec(COUNCIL_VOTE_OF), &approve);
	}

	pub fn veto(signed: &AccountId, proposal_hash: &ProposalHash) {
		assert!(is_councillor(signed), "only councillors may veto council proposals");
		assert!(storage::exists(&proposal_hash.to_keyed_vec(PROPOSAL_VOTERS)), "proposal must exist to be vetoed");

		let mut existing_vetoers = veto_of(&proposal_hash)
			.map(|pair| pair.1)
			.unwrap_or_else(Vec::new);
		let insert_position = existing_vetoers.binary_search(signed)
			.expect_err("a councillor may not veto a proposal twice");
		existing_vetoers.insert(insert_position, *signed);
		set_veto_of(&proposal_hash, system::block_number() + cooloff_period(), existing_vetoers);

		set_proposals(&proposals().into_iter().filter(|&(_, h)| h != *proposal_hash).collect::<Vec<_>>());
		storage::kill(&proposal_hash.to_keyed_vec(PROPOSAL_VOTERS));
		storage::kill(&proposal_hash.to_keyed_vec(PROPOSAL_OF));
		for (c, _) in council::active_council() {
			storage::kill(&(*proposal_hash, c).to_keyed_vec(COUNCIL_VOTE_OF));
		}
	}
}

pub mod privileged {
	use super::*;

	pub fn set_cooloff_period(blocks: BlockNumber) {
		storage::put(COOLOFF_PERIOD, &blocks);
	}

	pub fn set_voting_period(blocks: BlockNumber) {
		storage::put(VOTING_PERIOD, &blocks);
	}
}

pub mod internal {
	use super::*;
	use runtime::democracy::VoteThreshold;
	use runtime::democracy::privileged::start_referendum;

	pub fn end_block(now: BlockNumber) {
		while let Some((proposal, proposal_hash)) = take_proposal_if_expiring_at(now) {
			let tally = take_tally(&proposal_hash);
			println!("Executing proposal {:?} {:?}", proposal, tally);
			if let &Proposal::DemocracyCancelReferendum(ref_index) = &proposal {
				if let (_, 0, 0) = tally {
					democracy::privileged::cancel_referendum(ref_index);
				}
			} else {
				if tally.0 > tally.1 + tally.2 {
					kill_veto_of(&proposal_hash);
					match tally {
						(_, 0, 0) => start_referendum(proposal, VoteThreshold::SuperMajorityAgainst),
						_ => start_referendum(proposal, VoteThreshold::SimpleMajority),
					};
				}
			}
		}
	}
}

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
			twox_128(council::ACTIVE_COUNCIL).to_vec() => vec![].and(&vec![
				(Alice.to_raw_public(), expiry),
				(Bob.into(), expiry),
				(Charlie.into(), expiry)
			]),
			twox_128(COOLOFF_PERIOD).to_vec() => vec![].and(&2u64),
			twox_128(VOTING_PERIOD).to_vec() => vec![].and(&1u64),
			twox_128(democracy::VOTING_PERIOD).to_vec() => vec![].and(&3u64)
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
	use environment::with_env;
	use demo_primitives::{AccountId, Proposal};
	use runtime::{staking, council, democracy};
	use runtime::democracy::VoteThreshold;

	fn new_test_ext() -> TestExternalities {
		testing::externalities()
	}

	#[test]
	fn basic_environment_works() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			assert_eq!(staking::bonding_duration(), 0);
			assert_eq!(cooloff_period(), 2);
			assert_eq!(voting_period(), 1);
			assert_eq!(will_still_be_councillor_at(&Alice, 1), true);
			assert_eq!(will_still_be_councillor_at(&Alice, 10), false);
			assert_eq!(will_still_be_councillor_at(&Dave, 10), false);
			assert_eq!(is_councillor(&Alice), true);
			assert_eq!(is_councillor(&Dave), false);
			assert_eq!(proposals(), Vec::<(BlockNumber, ProposalHash)>::new());
			assert_eq!(proposal_voters(&ProposalHash::default()), Vec::<AccountId>::new());
			assert_eq!(is_vetoed(&ProposalHash::default()), false);
			assert_eq!(vote_of(&Alice, &ProposalHash::default()), None);
			assert_eq!(tally(&ProposalHash::default()), (0, 0, 3));
		});
	}

	#[test]
	fn referendum_cancellation_should_work_when_unanimous() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			democracy::privileged::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);

			let cancellation = Proposal::DemocracyCancelReferendum(0);
			let hash = cancellation.blake2_256();
			public::propose(&Alice, &cancellation);
			public::vote(&Bob, &hash, true);
			public::vote(&Charlie, &hash, true);
			assert_eq!(proposals(), vec![(2, hash)]);
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![]);
			assert_eq!(staking::bonding_duration(), 0);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_not_unanimous() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			democracy::privileged::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);

			let cancellation = Proposal::DemocracyCancelReferendum(0);
			let hash = cancellation.blake2_256();
			public::propose(&Alice, &cancellation);
			public::vote(&Bob, &hash, true);
			public::vote(&Charlie, &hash, false);
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);
		});
	}

	#[test]
	fn referendum_cancellation_should_fail_when_abstentions() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			democracy::privileged::start_referendum(proposal.clone(), VoteThreshold::SuperMajorityApprove);

			let cancellation = Proposal::DemocracyCancelReferendum(0);
			let hash = cancellation.blake2_256();
			public::propose(&Alice, &cancellation);
			public::vote(&Bob, &hash, true);
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(democracy::active_referendums(), vec![(0, 4, proposal, VoteThreshold::SuperMajorityApprove)]);
		});
	}

	#[test]
	fn veto_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	#[should_panic]
	fn double_veto_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);

			with_env(|e| e.block_number = 3);
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);
		});
	}

	#[test]
	#[should_panic]
	fn retry_in_cooloff_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);

			with_env(|e| e.block_number = 2);
			public::propose(&Alice, &proposal);
		});
	}

	#[test]
	fn retry_after_cooloff_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);

			with_env(|e| e.block_number = 3);
			public::propose(&Alice, &proposal);
			public::vote(&Bob, &hash, false);
			public::vote(&Charlie, &hash, true);
			internal::end_block(3);

			with_env(|e| e.block_number = 4);
			internal::end_block(4);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 7, Proposal::StakingSetBondingDuration(42), VoteThreshold::SimpleMajority)]);
		});
	}

	#[test]
	fn alternative_double_veto_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			public::veto(&Bob, &hash);

			with_env(|e| e.block_number = 3);
			public::propose(&Alice, &proposal);
			public::veto(&Charlie, &hash);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn simple_propose_should_work() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			let proposal = Proposal::StakingSetBondingDuration(42);
			let hash = proposal.blake2_256();
			public::propose(&Alice, &proposal);
			assert_eq!(proposals().len(), 1);
			assert_eq!(proposal_voters(&hash), vec![Alice.to_raw_public()]);
			assert_eq!(vote_of(&Alice, &hash), Some(true));
			assert_eq!(tally(&hash), (1, 0, 2));
		});
	}

	#[test]
	fn unvoted_proposal_should_expire_without_action() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			public::propose(&Alice, &Proposal::StakingSetBondingDuration(42));
			assert_eq!(tally(&Proposal::StakingSetBondingDuration(42).blake2_256()), (1, 0, 2));
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums().len(), 0);
		});
	}

	#[test]
	fn unanimous_proposal_should_expire_with_biased_referendum() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			public::propose(&Alice, &Proposal::StakingSetBondingDuration(42));
			public::vote(&Bob, &Proposal::StakingSetBondingDuration(42).blake2_256(), true);
			public::vote(&Charlie, &Proposal::StakingSetBondingDuration(42).blake2_256(), true);
			assert_eq!(tally(&Proposal::StakingSetBondingDuration(42).blake2_256()), (3, 0, 0));
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 5, Proposal::StakingSetBondingDuration(42), VoteThreshold::SuperMajorityAgainst)]);
		});
	}

	#[test]
	fn majority_proposal_should_expire_with_unbiased_referendum() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			public::propose(&Alice, &Proposal::StakingSetBondingDuration(42));
			public::vote(&Bob, &Proposal::StakingSetBondingDuration(42).blake2_256(), true);
			public::vote(&Charlie, &Proposal::StakingSetBondingDuration(42).blake2_256(), false);
			assert_eq!(tally(&Proposal::StakingSetBondingDuration(42).blake2_256()), (2, 1, 0));
			internal::end_block(1);

			with_env(|e| e.block_number = 2);
			internal::end_block(2);
			assert_eq!(proposals().len(), 0);
			assert_eq!(democracy::active_referendums(), vec![(0, 5, Proposal::StakingSetBondingDuration(42), VoteThreshold::SimpleMajority)]);
		});
	}

	#[test]
	#[should_panic]
	fn propose_by_public_should_panic() {
		with_externalities(&mut new_test_ext(), || {
			with_env(|e| e.block_number = 1);
			public::propose(&Dave, &Proposal::StakingSetBondingDuration(42));
		});
	}
}
