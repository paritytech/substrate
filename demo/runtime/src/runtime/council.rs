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

type VoteIndex = u32;

// parameters
const CANDIDACY_BOND: &[u8] = b"cou:cbo";
const VOTING_BOND: &[u8] = b"cou:vbo";
const PRESENT_SLASH_PER_VOTER: &[u8] = b"cou:pss";
const CARRY_COUNT: &[u8] = b"cou:cco";
const PRESENTATION_DURATION: &[u8] = b"cou:pdu";
const TERM_DURATION: &[u8] = b"cou:trm";
const DESIRED_SEATS: &[u8] = b"cou:sts";

// permanent state (always relevant, changes only at the finalisation of voting)
const ACTIVE_COUNCIL: &[u8] = b"cou:act";
const VOTE_COUNT: &[u8] = b"cou:vco";

// persistent state (always relevant, changes constantly)
const APPROVALS_OF: &[u8] = b"cou:apr:";
const REGISTER_INDEX_OF: &[u8] = b"cou:reg:";	// Candidate -> VoteIndex
const LAST_ACTIVE_OF: &[u8] = b"cou:lac:";		// Voter -> VoteIndex
const VOTERS: &[u8] = b"cou:vrs";
const CANDIDATES: &[u8] = b"cou:can";

// temporary state (only relevant during finalisation/presentation)
const NEXT_FINALISE: &[u8] = b"cou:nxt";
const SNAPSHOTED_STAKE_OF: &[u8] = b"cou:sss:";		// AccountId -> Balance
const WINNERS: &[u8] = b"cou:win";					// Vec<(Balance, AccountId)> ORDERED low -> high

/// How much should be locked up in order to submit one's candidacy.
pub fn candidacy_bond() -> Balance {
	storage::get(CANDIDACY_BOND)
		.expect("all core parameters of council module must be in place")
}

/// How much should be locked up in order to be able to submit votes.
pub fn voting_bond() -> Balance {
	storage::get(VOTING_BOND)
		.expect("all core parameters of council module must be in place")
}

/// How long to give each top candidate to present themselves after the vote ends.
pub fn presentation_duration() -> BlockNumber {
	storage::get(PRESENTATION_DURATION)
		.expect("all core parameters of council module must be in place")
}

/// How long each position is active for.
pub fn term_duration() -> BlockNumber {
	storage::get(TERM_DURATION)
		.expect("all core parameters of council module must be in place")
}

/// The punishment, per voter, if you provide an invalid presentation.
pub fn present_slash_per_voter() -> Balance {
	storage::get(PRESENT_SLASH_PER_VOTER)
		.expect("all core parameters of council module must be in place")
}

/// Number of accounts that should be sitting on the council.
pub fn desired_seats() -> u32 {
	storage::get(DESIRED_SEATS)
		.expect("all core parameters of council module must be in place")
}

/// How many runners-up should have their approvals persist until the next vote.
pub fn carry_count() -> u32 {
	storage::get(CARRY_COUNT)
		.expect("all core parameters of council module must be in place")
}

/// The current council. When there's a vote going on, this should still be used for executive
/// matters.
pub fn active_council() -> Vec<(AccountId, BlockNumber)> {
	storage::get_or_default(ACTIVE_COUNCIL)
}

/// The block number on which the tally for the next election will happen. `None` only if the
/// desired seats of the council is zero.
pub fn next_tally() -> Option<BlockNumber> {
	let desired_seats = desired_seats();
	if desired_seats == 0 {
		None
	} else {
		let c = active_council();
		let (next_possible, count, coming) =
			if let Some((tally_end, comers, leavers)) = next_finalise() {
				// if there's a tally in progress, then next tally can begin immediately afterwards
				(tally_end, c.len() - leavers.len() + comers as usize, comers)
			} else {
				(system::block_number(), c.len(), 0)
			};
		if count < desired_seats as usize {
			Some(next_possible)
		} else {
			// next tally begins once enough council members expire to bring members below desired.
			if desired_seats <= coming {
				// the entire amount of desired seats is less than those new members - we'll have
				// to wait until they expire.
				Some(next_possible + term_duration())
			} else {
				Some(c[c.len() - (desired_seats - coming) as usize].1)
			}
		}
	}
}

/// The accounts holding the seats that will become free on the next tally.
pub fn next_finalise() -> Option<(BlockNumber, u32, Vec<AccountId>)> {
	storage::get(NEXT_FINALISE)
}

/// The total number of votes that have happened or are in progress.
pub fn vote_index() -> VoteIndex {
	storage::get_or_default(VOTE_COUNT)
}

/// The vote index that the candidate `who` was registered or `None` if they are not currently
/// registered.
pub fn candidate_reg_index(who: &AccountId) -> Option<VoteIndex> {
	storage::get(&who.to_keyed_vec(REGISTER_INDEX_OF))
}

/// The last cleared vote index that this voter was last active at.
pub fn voter_last_active(voter: &AccountId) -> Option<VoteIndex> {
	storage::get(LAST_ACTIVE_OF)
}

pub mod public {
	use super::*;

	/// Set candidate approvals. Approval slots stay valid as long as candidates in those slots
	/// are registered.
	pub fn set_approvals(who: &AccountId, votes: &Vec<bool>, index: VoteIndex) {
		assert_eq!(index, vote_index());
		storage::put(&who.to_keyed_vec(APPROVALS_OF), votes);
		storage::put(&who.to_keyed_vec(LAST_ACTIVE_OF), &index);
	}

	/// Remove a voter. For it not to be a bond-consuming no-op, all approved candidate indices
	/// must now be either unregistered or registered to a candidate that registered the slot after
	/// the voter gave their last approval set.
	///
	/// May be called by anyone. Returns the voter deposit to `signed`.
	pub fn kill_inactive_voter(signed: &AccountId, who: &AccountId) {
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
	/// `signed` should have at least
	pub fn present(signed: &AccountId, who: &AccountId, index: VoteIndex) {
		assert_eq!(index, vote_index());
		unimplemented!();
	}
}

pub mod privileged {
	use super::*;

	/// Set the desired member count; if lower than the current count, then seats will not be up
	/// election when they expire. If more, then a new vote will be started if one is not already
	/// in progress.
	pub fn set_desired_seats(count: u32) {
		storage::put(DESIRED_SEATS, &count);
	}

	/// Remove a particular member. A tally will happen instantly (if not already in a presentation
	/// period) to fill the seat if removal means that the desired members are not met.
	/// This is effective immediately.
	pub fn remove_member(who: &AccountId) {
		let new_council: Vec<(AccountId, BlockNumber)> = active_council()
			.into_iter()
			.filter(|i| i.0 != *who)
			.collect();
		storage::put(ACTIVE_COUNCIL, &new_council);
	}

	/// Set the presentation duration. If there is current a vote being presented for, will
	/// invoke `finalise_vote`.
	pub fn set_presentation_duration(count: BlockNumber) {
		storage::put(PRESENTATION_DURATION, &count);
	}

	/// Set the presentation duration. If there is current a vote being presented for, will
	/// invoke `finalise_vote`.
	pub fn set_term_duration(count: BlockNumber) {
		storage::put(TERM_DURATION, &count);
	}
}

pub mod internal {
	use super::*;
	use demo_primitives::Proposal;
	use dispatch::enact_proposal;

	/// Current era is ending; we should finish up any proposals.
	pub fn end_block() {
		if let Some(number) = next_tally() {
			if system::block_number() == number {
				start_tally();
			}
		}
		if let Some((number, _, _)) = next_finalise() {
			if system::block_number() == number {
				finalise_tally();
			}
		}
	}
}

/// Close the voting, snapshot the staking and the number of seats that are actually up for grabs.
fn start_tally() {
	let active_council = active_council();
	let desired_seats = desired_seats() as usize;
	let number = system::block_number();
	let expiring = active_council.iter().take_while(|i| i.1 == number).cloned().collect::<Vec<_>>();
	if active_council.len() - expiring.len() < desired_seats {
		let empty_seats = desired_seats - (active_council.len() - expiring.len());
		storage::put(NEXT_FINALISE, &(number + presentation_duration(), empty_seats as u32, expiring));
	}
}

/// Finalise the vote, removing each of the `removals` and inserting `seats` of the most approved
/// candidates in their place. If the total council members is less than the desired membership
/// a new vote is started.
/// Clears all presented candidates, returning the bond of the elected ones.
fn finalise_tally() {
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
		});
	}
}
