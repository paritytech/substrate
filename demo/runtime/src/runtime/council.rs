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

//! Council system: Handles the voting in and maintenance of council members.

use rstd::prelude::*;
use codec::KeyedVec;
use runtime_support::storage;
use demo_primitives::{Proposal, AccountId, Hash, BlockNumber};
use runtime::{staking, system, session};
use runtime::staking::Balance;

// no polynomial attack:
// all public operations should be constant time.
// all protected operations may be at most O(public operations)

// public operations:
// - express approval (ideally, express all approvals)
// - re-express approval (ideally, re-express all approvals)
// - clear all approvals
// - submit candidacy
// protected operations:
// - remove candidacy (remove all votes for a candidate)

// for an approval vote of C councilers:

// top K candidates are maintained between votes. all others are discarded.
// - candidate removed & bond returned when elected.
// - candidate removed & bond burned when discarded.

// at the point that the vote ends, all voters' balances are snapshotted.

// for B blocks following, there's a counting period whereby each of the candidates that believe
// they fall in the top K+C voted can present themselves. they get the total stake
// recorded (based on the snapshot); an ordered list is maintained. Noone may present themselves
// that, if elected, would result in being included twice on the council (important since existing
// councilers will will have their approval votes as it may be that they don't get removed), nor
// if existing presenters would mean they're not in the top K+C.

// following B blocks, the top C+K that presented themselves have their bond returned and the
// top C candidates are elected. the top C candidates have their bond returned.

// the top C candidates and all other candidates beyond the top C+K are cleared and the clearing
// mask is appended to mask list (ready to be applied to vote arrays).

// vote-clearing happens lazily, with previous write also storing the round and all subsequent
// rounds' operations applied at the next read/write time.

// vote buffer size increases as required.
// bond taken for initial approval, returned when clearing.

// vec<candidate> (list of addresses, each bonded, can contain "holes" of null addresses). Order important.
// vec<voter> (all voters. order unimportant - just need to be enumerable.)
// voter -> (last round, Vec<bool>)

const CURRENT_VOTE: &[u8] = b"cou:cur";
const APPROVALS_OF: &[u8] = b"cou:apr:";
const VOTERS: &[u8] = b"cou:vrs";
const CANDIDATES: &[u8] = b"cou:can";

const CANDIDACY_BOND: &[u8] = b"cou:cbo";
const VOTING_BOND: &[u8] = b"cou:vbo";

const CARRY_COUNT: &[u8] = b"cou:cco";
const PRESENTATION_DURATION: &[u8] = b"cou:pdu";

const WINNERS: &[u8] = b"cou:win";

/// How much should be locked up in order to submit one's candidacy.
pub fn candidacy_bond() -> Balance {
	unimplemented!();
}

/// How much should be locked up in order to be able to submit votes.
pub fn voting_bond() -> Balance {
	unimplemented!();
}

/// How long to give each top candidate to present themselves after the vote ends.
pub fn presentation_duration() -> BlockNumber {
	unimplemented!();
}

/// How many runners-up should have their approvals persist until the next vote.
pub fn carry_count() -> u32 {
	unimplemented!();
}

/// The current council. When there's a vote going on, this should still be used for executive
/// matters.
pub fn active_council() -> Vec<AccountId> {
	unimplemented!();
}

/// The information on the current vote:
/// - The block number where voting will end;
/// - The specific council members to be replaced.
pub fn current_vote() -> Option<(BlockNumber, Vec<AccountId>)> {
	unimplemented!();
}

/// The total number of votes that have happened or are in progress.
pub fn vote_index() -> VoteIndex {
	unimplemented!();
}

/// The queue of candidate indices that will be cleared.
pub fn candidate_clear_queue() -> {
	unimplemented!();
}

/// The last cleared vote index that this voter was last active at.
pub fn voter_last_active(voter: &AddressId) -> VoteIndex {
	unimplemented!();
}

pub mod public {
	use super::*;

	/// Remove a voter. For it not to panic, the combination of candidate_clear_queue from the
	/// when it was last active until the penultimate vote should result in no approvals.
	///
	/// May be called by anyone. Returns the voter deposit to `signed`.
	pub fn kill_inactive_voter(signed: &AccountId, who: &AddressId) {
		unimplemented!();
	}

	/// Remove a voter. All votes are cancelled and the voter deposit is returned.
	pub fn retract_voter(signed: AccountId) {
		unimplemented!();
	}

	/// Submit oneself for candidacy.
	///
	/// Account must have enough cash in it to pay the bond.
	pub fn submit_candidacy(signed: &AccountId) {
		unimplemented!();
	}

	/// Claim that `signed` is one of the top carry_count() + current_vote().1 candidates.
	/// Only works if the block number >= current_vote().0 and < current_vote().0 + presentation_duration()
	pub fn present(signed: &AccountId) {
		unimplemented!();
	}
}

pub mod privileged {
	use super::*;

	/// Set the desired member count; if lower than the current count, then seats will not be up
	/// election when they expire. If more, then a new vote will be started if one is not already
	/// in progress.
	pub fn set_desired_seats(count: u32) {
		unimplemented!();
	}

	/// Remove a particular member. A new vote will be started if one is not already in progress.
	/// This is effective immediately.
	pub fn remove_member(who: AddressId) {
		unimplemented!();
	}
}

pub mod internal {
	use super::*;
	use demo_primitives::Proposal;
	use dispatch::enact_proposal;

	/// Current era is ending; we should finish up any proposals.
	pub fn end_block() {
		if let Some((number, removals)) = current_vote() {
			if system::block_number() == number {
				close_voting(removals.len() as u32);
			}
			if system::block_number() == number + presentation_duration() {
				finalise_vote(removals);
			}
		}
	}
}

/// Close the voting, snapshot the staking and the number of seats that are actually up for grabs.
fn close_voting(removal_count: u32) {
	unimplemented!();
}

/// Finalise the vote, removing each of the `removals` and inserting `seats` of the most approved
/// candidates in their place. If the total council members is less than the desired membership
/// a new vote is started.
/// Clears all presented candidates, returning the bond of the elected ones.
fn finalise_vote(seats: u32, removals: Vec<AccountId>) {
	unimplemented!();
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
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let one = Keyring::One.to_raw_public();

		map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => charlie.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => charlie.to_vec(),
			twox_128(&alice.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&10u64),
			twox_128(&bob.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&20u64),
			twox_128(&charlie.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&30u64),
			twox_128(&dave.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&40u64),
			twox_128(&eve.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&50u64),
			twox_128(&ferdie.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&60u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&1u64),
			twox_128(b"sta:tot").to_vec() => vec![].and(&210u64),
			twox_128(b"sta:spe").to_vec() => vec![].and(&1u64),
			twox_128(b"sta:vac").to_vec() => vec![].and(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].and(&1u64)
		]
	}

	#[test]
	fn simple_passing_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);

			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2));
			public::vote(&alice, 1, true);

			assert_eq!(public::tally(), (10, 0));

			democracy::internal::end_of_an_era();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}
}
