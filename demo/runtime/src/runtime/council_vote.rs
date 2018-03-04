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
pub const VETOED_PROPOSAL: &[u8] = b"cov:veto:";		// ProposalHash -> (BlockNumber, Vec<AccountId>)

pub fn cooloff_period() -> BlockNumber {
	storage::get(COOLOFF_PERIOD).expect("all parameters must be defined")
}

pub fn voting_period() -> BlockNumber {
	storage::get(VOTING_PERIOD).expect("all parameters must be defined")
}

pub fn proposals() -> Vec<(BlockNumber, ProposalHash)> {
	storage::get_or_default(PROPOSALS)
}

pub fn was_vetoed(proposal: &ProposalHash) -> bool {
	storage::exists(&proposal.to_keyed_vec(VETOED_PROPOSAL))
}

pub fn will_still_be_councillor_at(who: &AccountId, n: BlockNumber) -> bool {
	council::active_council().iter()
		.find(|&&(ref a, _)| a == who)
		.map(|&(_, expires)| expires > n)
		.unwrap_or(false)
}

pub fn vote_of(who: &AccountId, proposal: &ProposalHash) -> Option<bool> {
	storage::get(&(*who, *proposal).to_keyed_vec(COUNCIL_VOTE_OF))
}

pub fn take_vote_of(who: &AccountId, proposal: &ProposalHash) -> Option<bool> {
	storage::get(&(*who, *proposal).to_keyed_vec(COUNCIL_VOTE_OF))
}

pub fn tally(proposal_hash: &ProposalHash) -> (u32, u32, u32) {
	generic_tally(proposal_hash, vote_of)
}

fn take_tally(proposal_hash: &ProposalHash) -> (u32, u32, u32) {
	generic_tally(proposal_hash, take_vote_of)
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
		assert!(!was_vetoed(&proposal_hash));

		let mut proposals = proposals();
		proposals.push((expiry, proposal_hash));
		proposals.sort_by_key(|&(expiry, _)| expiry);
		set_proposals(&proposals);

		storage::put(&proposal_hash.to_keyed_vec(PROPOSAL_OF), proposal);
		storage::put(&proposal_hash.to_keyed_vec(PROPOSAL_VOTERS), &vec![*signed]);
		storage::put(&(proposal_hash, *signed).to_keyed_vec(COUNCIL_VOTE_OF), &true);
	}

	pub fn vote(signed: AccountId, proposal: &ProposalHash, approve: bool) {

	}

	pub fn veto(signed: AccountId, proposal: &ProposalHash) {

	}

	pub fn repropose(signed: AccountId, proposal: &Proposal) {

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
			let vote_threshold = match tally.0 {
				x if x == tally.2 => VoteThreshold::SuperMajorityAgainst,
				x if x > tally.2 / 2 => VoteThreshold::SimpleMajority,
				_ => VoteThreshold::SuperMajorityApprove,
			};
			start_referendum(proposal, vote_threshold);
		}
	}
}

#[cfg(test)]
mod tests {

}
