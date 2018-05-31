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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")] extern crate serde;

extern crate integer_sqrt;
extern crate substrate_codec as codec;
extern crate substrate_primitives;
#[cfg(any(feature = "std", test))] extern crate substrate_keyring as keyring;
#[macro_use] extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_democracy as democracy;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
use primitives::traits::{Zero, One, RefInto, As};
use runtime_support::{StorageValue, StorageMap};

pub mod voting;

// no polynomial attacks:
//
// all unbonded public operations should be constant time.
// all other public operations must be linear time in terms of prior public operations and:
// - those "valid" ones that cost nothing be limited to a constant number per single protected operation
// - the rest costing the same order as the computational complexity
// all protected operations must complete in at most O(public operations)
//
// we assume "beneficial" transactions will have the same access as attack transactions.
//
// any storage requirements should be bonded by the same order as the volume.

// public operations:
// - express approvals (you pay in a "voter" bond the first time you do this; O(1); one extra DB entry, one DB change)
// - remove active voter (you get your "voter" bond back; O(1); one fewer DB entry, one DB change)
// - remove inactive voter (either you or the target is removed; if the target, you get their "voter" bond back; O(1); one fewer DB entry, one DB change)
// - submit candidacy (you pay a "candidate" bond; O(1); one extra DB entry, two DB changes)
// - present winner/runner-up (you may pay a "presentation" bond of O(voters) if the presentation is invalid; O(voters) compute; )
// protected operations:
// - remove candidacy (remove all votes for a candidate) (one fewer DB entry, two DB changes)

// to avoid a potentially problematic case of not-enough approvals prior to voting causing a
// back-to-back votes that have no way of ending, then there's a forced grace period between votes.
// to keep the system as stateless as possible (making it a bit easier to reason about), we just
// restrict when votes can begin to blocks that lie on boundaries (`voting_period`).

// for an approval vote of C councilers:

// top K runners-up are maintained between votes. all others are discarded.
// - candidate removed & bond returned when elected.
// - candidate removed & bond burned when discarded.

// at the point that the vote ends (), all voters' balances are snapshotted.

// for B blocks following, there's a counting period whereby each of the candidates that believe
// they fall in the top K+C voted can present themselves. they get the total stake
// recorded (based on the snapshot); an ordered list is maintained (the leaderboard). Noone may
// present themselves that, if elected, would result in being included twice on the council
// (important since existing councilers will will have their approval votes as it may be that they
// don't get removed), nor if existing presenters would mean they're not in the top K+C.

// following B blocks, the top C candidates are elected and have their bond returned. the top C
// candidates and all other candidates beyond the top C+K are cleared.

// vote-clearing happens lazily; for an approval to count, the most recent vote at the time of the
// voter's most recent vote must be no later than the most recent vote at the time that the
// candidate in the approval position was registered there. as candidates are removed from the
// register and others join in their place, this prevent an approval meant for an earlier candidate
// being used to elect a new candidate.

// the candidate list increases as needed, but the contents (though not really the capacity) reduce
// after each vote as all but K entries are cleared. newly registering candidates must use cleared
// entries before they increase the capacity.

pub type VoteIndex = u32;

pub trait Trait: democracy::Trait {}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn set_approvals(aux, votes: Vec<bool>, index: VoteIndex) = 0;
		fn reap_inactive_voter(aux, signed_index: u32, who: T::AccountId, who_index: u32, assumed_vote_index: VoteIndex) = 1;
		fn retract_voter(aux, index: u32) = 2;
		fn submit_candidacy(aux, slot: u32) = 3;
		fn present_winner(aux, candidate: T::AccountId, total: T::Balance, index: VoteIndex) = 4;
	}
	pub enum PrivCall {
		fn set_desired_seats(count: u32) = 0;
		fn remove_member(who: T::AccountId) = 1;
		fn set_presentation_duration(count: T::BlockNumber) = 2;
		fn set_term_duration(count: T::BlockNumber) = 3;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// parameters
	// How much should be locked up in order to submit one's candidacy.
	pub CandidacyBond get(candidacy_bond): b"cou:cbo" => required T::Balance;
	// How much should be locked up in order to be able to submit votes.
	pub VotingBond get(voting_bond): b"cou:vbo" => required T::Balance;
	// The punishment, per voter, if you provide an invalid presentation.
	pub PresentSlashPerVoter get(present_slash_per_voter): b"cou:pss" => required T::Balance;
	// How many runners-up should have their approvals persist until the next vote.
	pub CarryCount get(carry_count): b"cou:cco" => required u32;
	// How long to give each top candidate to present themselves after the vote ends.
	pub PresentationDuration get(presentation_duration): b"cou:pdu" => required T::BlockNumber;
	// How many votes need to go by after a voter's last vote before they can be reaped if their
	// approvals are moot.
	pub InactiveGracePeriod get(inactivity_grace_period): b"cou:vgp" => required VoteIndex;
	// How often (in blocks) to check for new votes.
	pub VotingPeriod get(voting_period): b"cou:per" => required T::BlockNumber;
	// How long each position is active for.
	pub TermDuration get(term_duration): b"cou:trm" => required T::BlockNumber;
	// Number of accounts that should be sitting on the council.
	pub DesiredSeats get(desired_seats): b"cou:sts" => required u32;

	// permanent state (always relevant, changes only at the finalisation of voting)
	// The current council. When there's a vote going on, this should still be used for executive
	// matters.
	pub ActiveCouncil get(active_council): b"cou:act" => default Vec<(T::AccountId, T::BlockNumber)>;
	// The total number of votes that have happened or are in progress.
	pub VoteCount get(vote_index): b"cou:vco" => default VoteIndex;

	// persistent state (always relevant, changes constantly)
	// The last cleared vote index that this voter was last active at.
	pub ApprovalsOf get(approvals_of): b"cou:apr" => default map [ T::AccountId => Vec<bool> ];
	// The vote index and list slot that the candidate `who` was registered or `None` if they are not
	// currently registered.
	pub RegisterInfoOf get(candidate_reg_info): b"cou:reg" => map [ T::AccountId => (VoteIndex, u32) ];
	// The last cleared vote index that this voter was last active at.
	pub LastActiveOf get(voter_last_active): b"cou:lac" => map [ T::AccountId => VoteIndex ];
	// The present voter list.
	pub Voters get(voters): b"cou:vrs" => default Vec<T::AccountId>;
	// The present candidate list.
	pub Candidates get(candidates): b"cou:can" => default Vec<T::AccountId>; // has holes
	pub CandidateCount get(candidate_count): b"cou:cnc" => default u32;

	// temporary state (only relevant during finalisation/presentation)
	// The accounts holding the seats that will become free on the next tally.
	pub NextFinalise get(next_finalise): b"cou:nxt" => (T::BlockNumber, u32, Vec<T::AccountId>);
	// The stakes as they were at the point that the vote ended.
	pub SnapshotedStakes get(snapshoted_stakes): b"cou:sss" => required Vec<T::Balance>;
	// Get the leaderboard if we;re in the presentation phase.
	pub Leaderboard get(leaderboard): b"cou:win" => Vec<(T::Balance, T::AccountId)>; // ORDERED low -> high
}

impl<T: Trait> Module<T> {

	// exposed immutables.

	/// True if we're currently in a presentation period.
	pub fn presentation_active() -> bool {
		<NextFinalise<T>>::exists()
	}

	/// If `who` a candidate at the moment?
	pub fn is_a_candidate(who: &T::AccountId) -> bool {
		<RegisterInfoOf<T>>::exists(who)
	}

	/// Determine the block that a vote can happen on which is no less than `n`.
	pub fn next_vote_from(n: T::BlockNumber) -> T::BlockNumber {
		let voting_period = Self::voting_period();
		(n + voting_period - One::one()) / voting_period * voting_period
	}

	/// The block number on which the tally for the next election will happen. `None` only if the
	/// desired seats of the council is zero.
	pub fn next_tally() -> Option<T::BlockNumber> {
		let desired_seats = Self::desired_seats();
		if desired_seats == 0 {
			None
		} else {
			let c = Self::active_council();
			let (next_possible, count, coming) =
				if let Some((tally_end, comers, leavers)) = Self::next_finalise() {
					// if there's a tally in progress, then next tally can begin immediately afterwards
					(tally_end, c.len() - leavers.len() + comers as usize, comers)
				} else {
					(<system::Module<T>>::block_number(), c.len(), 0)
				};
			if count < desired_seats as usize {
				Some(next_possible)
			} else {
				// next tally begins once enough council members expire to bring members below desired.
				if desired_seats <= coming {
					// the entire amount of desired seats is less than those new members - we'll have
					// to wait until they expire.
					Some(next_possible + Self::term_duration())
				} else {
					Some(c[c.len() - (desired_seats - coming) as usize].1)
				}
			}.map(Self::next_vote_from)
		}
	}

	// dispatch

	/// Set candidate approvals. Approval slots stay valid as long as candidates in those slots
	/// are registered.
	fn set_approvals(aux: &T::PublicAux, votes: Vec<bool>, index: VoteIndex) {
		ensure!(!Self::presentation_active());
		ensure!(index == Self::vote_index());
		if !<LastActiveOf<T>>::exists(aux.ref_into()) {
			// not yet a voter - deduct bond.
			<staking::Module<T>>::reserve_balance(aux.ref_into(), Self::voting_bond());
			<Voters<T>>::put({
				let mut v = Self::voters();
				v.push(aux.ref_into().clone());
				v
			});
		}
		<ApprovalsOf<T>>::insert(aux.ref_into().clone(), votes);
		<LastActiveOf<T>>::insert(aux.ref_into(), index);
	}

	/// Remove a voter. For it not to be a bond-consuming no-op, all approved candidate indices
	/// must now be either unregistered or registered to a candidate that registered the slot after
	/// the voter gave their last approval set.
	///
	/// May be called by anyone. Returns the voter deposit to `signed`.
	fn reap_inactive_voter(aux: &T::PublicAux, signed_index: u32, who: T::AccountId, who_index: u32, assumed_vote_index: VoteIndex) {
		ensure!(!Self::presentation_active(), "cannot reap during presentation period");
		ensure!(Self::voter_last_active(aux.ref_into()).is_some(), "reaper must be a voter");
		let last_active = ensure_unwrap!(Self::voter_last_active(&who), "target for inactivity cleanup must be active");
		ensure!(assumed_vote_index == Self::vote_index(), "vote index not current");
		ensure!(last_active < assumed_vote_index - Self::inactivity_grace_period(), "cannot reap during grace perid");
		let voters = Self::voters();
		let signed_index = signed_index as usize;
		let who_index = who_index as usize;
		ensure!(signed_index < voters.len() && &voters[signed_index] == aux.ref_into(), "bad reporter index");
		ensure!(who_index < voters.len() && voters[who_index] == who, "bad target index");

		// will definitely kill one of signed or who now.

		let valid = !Self::approvals_of(&who).iter()
			.zip(Self::candidates().iter())
			.any(|(&appr, addr)|
				appr &&
				*addr != T::AccountId::default() &&
				Self::candidate_reg_info(addr).map_or(false, |x| x.0 <= last_active)/*defensive only: all items in candidates list are registered*/
			);

		Self::remove_voter(
			if valid { &who } else { aux.ref_into() },
			if valid { who_index } else { signed_index },
			voters
		);
		if valid {
			<staking::Module<T>>::transfer_reserved_balance(&who, aux.ref_into(), Self::voting_bond());
		} else {
			<staking::Module<T>>::slash_reserved(aux.ref_into(), Self::voting_bond());
		}
	}

	/// Remove a voter. All votes are cancelled and the voter deposit is returned.
	fn retract_voter(aux: &T::PublicAux, index: u32) {
		ensure!(!Self::presentation_active(), "cannot retract when presenting");
		ensure!(<LastActiveOf<T>>::exists(aux.ref_into()), "cannot retract non-voter");
		let voters = Self::voters();
		let index = index as usize;
		ensure!(index < voters.len(), "retraction index invalid");
		ensure!(&voters[index] == aux.ref_into(), "retraction index mismatch");
		Self::remove_voter(aux.ref_into(), index, voters);
		<staking::Module<T>>::unreserve_balance(aux.ref_into(), Self::voting_bond());
	}

	/// Submit oneself for candidacy.
	///
	/// Account must have enough transferrable funds in it to pay the bond.
	fn submit_candidacy(aux: &T::PublicAux, slot: u32) {
		ensure!(!Self::is_a_candidate(aux.ref_into()), "duplicate candidate submission");
		ensure!(<staking::Module<T>>::can_deduct_unbonded(aux.ref_into(), Self::candidacy_bond()), "candidate has not enough funds");

		let slot = slot as usize;
		let count = Self::candidate_count() as usize;
		let candidates = Self::candidates();
		ensure!(
			(slot == count && count == candidates.len()) ||
			(slot < candidates.len() && candidates[slot] == T::AccountId::default()),
			"invalid candidate slot"
		);

		<staking::Module<T>>::deduct_unbonded(aux.ref_into(), Self::candidacy_bond());
		let mut candidates = candidates;
		if slot == candidates.len() {
			candidates.push(aux.ref_into().clone());
		} else {
			candidates[slot] = aux.ref_into().clone();
		}
		<Candidates<T>>::put(candidates);
		<CandidateCount<T>>::put(count as u32 + 1);
		<RegisterInfoOf<T>>::insert(aux.ref_into(), (Self::vote_index(), slot as u32));
	}

	/// Claim that `signed` is one of the top Self::carry_count() + current_vote().1 candidates.
	/// Only works if the `block_number >= current_vote().0` and `< current_vote().0 + presentation_duration()``
	/// `signed` should have at least
	fn present_winner(aux: &T::PublicAux, candidate: T::AccountId, total: T::Balance, index: VoteIndex) {
		ensure!(index == Self::vote_index(), "index not current");
		let (_, _, expiring) = ensure_unwrap!(Self::next_finalise(), "cannot present outside of presentation period");
		let stakes = Self::snapshoted_stakes();
		let voters = Self::voters();
		let bad_presentation_punishment = Self::present_slash_per_voter() * T::Balance::sa(voters.len());
		ensure!(<staking::Module<T>>::can_slash(aux.ref_into(), bad_presentation_punishment), "presenter must have sufficient slashable funds");

		let mut leaderboard = ensure_unwrap!(Self::leaderboard(), "leaderboard must exist while present phase active");
		ensure!(total > leaderboard[0].0, "candidate not worthy of leaderboard");

		if let Some(p) = Self::active_council().iter().position(|&(ref c, _)| c == &candidate) {
			ensure!(p < expiring.len(), "candidate must not form a duplicated member if elected");
		}

		let (registered_since, candidate_index): (VoteIndex, u32) =
			ensure_unwrap!(Self::candidate_reg_info(&candidate), "presented candidate must be current");
		let actual_total = voters.iter()
			.zip(stakes.iter())
			.filter_map(|(voter, stake)|
				match Self::voter_last_active(voter) {
					Some(b) if b >= registered_since =>
						Self::approvals_of(voter).get(candidate_index as usize)
							.and_then(|approved| if *approved { Some(*stake) } else { None }),
					_ => None,
				})
			.fold(Zero::zero(), |acc, n| acc + n);
		let dupe = leaderboard.iter().find(|&&(_, ref c)| c == &candidate).is_some();
		if total == actual_total && !dupe {
			// insert into leaderboard
			leaderboard[0] = (total, candidate);
			leaderboard.sort_by_key(|&(t, _)| t);
			<Leaderboard<T>>::put(leaderboard);
		} else {
			<staking::Module<T>>::slash(aux.ref_into(), bad_presentation_punishment);
		}
	}

	/// Set the desired member count; if lower than the current count, then seats will not be up
	/// election when they expire. If more, then a new vote will be started if one is not already
	/// in progress.
	fn set_desired_seats(count: u32) {
		<DesiredSeats<T>>::put(count);
	}

	/// Remove a particular member. A tally will happen instantly (if not already in a presentation
	/// period) to fill the seat if removal means that the desired members are not met.
	/// This is effective immediately.
	fn remove_member(who: T::AccountId) {
		let new_council: Vec<(T::AccountId, T::BlockNumber)> = Self::active_council()
			.into_iter()
			.filter(|i| i.0 != who)
			.collect();
		<ActiveCouncil<T>>::put(new_council);
	}

	/// Set the presentation duration. If there is current a vote being presented for, will
	/// invoke `finalise_vote`.
	fn set_presentation_duration(count: T::BlockNumber) {
		<PresentationDuration<T>>::put(count);
	}

	/// Set the presentation duration. If there is current a vote being presented for, will
	/// invoke `finalise_vote`.
	fn set_term_duration(count: T::BlockNumber) {
		<TermDuration<T>>::put(count);
	}

	// private

	/// Check there's nothing to do this block
	fn end_block(block_number: T::BlockNumber) {
		if (block_number % Self::voting_period()).is_zero() {
			if let Some(number) = Self::next_tally() {
				if block_number == number {
					Self::start_tally();
				}
			}
		}
		if let Some((number, _, _)) = Self::next_finalise() {
			if block_number == number {
				Self::finalise_tally();
			}
		}
	}

	/// Remove a voter from the system. Trusts that Self::voters()[index] != voter.
	fn remove_voter(voter: &T::AccountId, index: usize, mut voters: Vec<T::AccountId>) {
		<Voters<T>>::put({ voters.swap_remove(index); voters });
		<ApprovalsOf<T>>::remove(voter);
		<LastActiveOf<T>>::remove(voter);
	}

	/// Close the voting, snapshot the staking and the number of seats that are actually up for grabs.
	fn start_tally() {
		let active_council = Self::active_council();
		let desired_seats = Self::desired_seats() as usize;
		let number = <system::Module<T>>::block_number();
		let expiring = active_council.iter().take_while(|i| i.1 == number).map(|i| i.0.clone()).collect::<Vec<_>>();
		if active_council.len() - expiring.len() < desired_seats {
			let empty_seats = desired_seats - (active_council.len() - expiring.len());
			<NextFinalise<T>>::put((number + Self::presentation_duration(), empty_seats as u32, expiring));

			let voters = Self::voters();
			let votes = voters.iter().map(<staking::Module<T>>::balance).collect::<Vec<_>>();
			<SnapshotedStakes<T>>::put(votes);

			// initialise leaderboard.
			let leaderboard_size = empty_seats + Self::carry_count() as usize;
			<Leaderboard<T>>::put(vec![(T::Balance::zero(), T::AccountId::default()); leaderboard_size]);
		}
	}

	/// Finalise the vote, removing each of the `removals` and inserting `seats` of the most approved
	/// candidates in their place. If the total council members is less than the desired membership
	/// a new vote is started.
	/// Clears all presented candidates, returning the bond of the elected ones.
	fn finalise_tally() {
		<SnapshotedStakes<T>>::kill();
		let (_, coming, expiring): (T::BlockNumber, u32, Vec<T::AccountId>) =
			ensure_unwrap!(<NextFinalise<T>>::take(), "finalise can only be called after a tally is started.");
		let leaderboard: Vec<(T::Balance, T::AccountId)> = <Leaderboard<T>>::take().unwrap_or_default();
		let new_expiry = <system::Module<T>>::block_number() + Self::term_duration();

		// return bond to winners.
		let candidacy_bond = Self::candidacy_bond();
		for &(_, ref w) in leaderboard.iter()
			.rev()
			.take_while(|&&(b, _)| !b.is_zero())
			.take(coming as usize)
		{
			<staking::Module<T>>::refund(w, candidacy_bond);
		}

		// set the new council.
		let mut new_council: Vec<_> = Self::active_council()
			.into_iter()
			.skip(expiring.len())
			.chain(leaderboard.iter()
				.rev()
				.take_while(|&&(b, _)| !b.is_zero())
				.take(coming as usize)
				.cloned()
				.map(|(_, a)| (a, new_expiry)))
			.collect();
		new_council.sort_by_key(|&(_, expiry)| expiry);
		<ActiveCouncil<T>>::put(new_council);

		// clear all except runners-up from candidate list.
		let candidates = Self::candidates();
		let mut new_candidates = vec![T::AccountId::default(); candidates.len()];	// shrink later.
		let runners_up = leaderboard.into_iter()
			.rev()
			.take_while(|&(b, _)| !b.is_zero())
			.skip(coming as usize)
			.filter_map(|(_, a)| Self::candidate_reg_info(&a).map(|i| (a, i.1)));
		let mut count = 0u32;
		for (address, slot) in runners_up {
			new_candidates[slot as usize] = address;
			count += 1;
		}
		for (old, new) in candidates.iter().zip(new_candidates.iter()) {
			if old != new {
				// removed - kill it
				<RegisterInfoOf<T>>::remove(old);
			}
		}
		// discard any superfluous slots.
		if let Some(last_index) = new_candidates.iter().rposition(|c| *c != T::AccountId::default()) {
			new_candidates.truncate(last_index + 1);
		}
		<Candidates<T>>::put(new_candidates);
		<CandidateCount<T>>::put(count);
		<VoteCount<T>>::put(Self::vote_index() + 1);
	}
}

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait> {
	// for the voting onto the  council
	pub candidacy_bond: T::Balance,
	pub voter_bond: T::Balance,
	pub present_slash_per_voter: T::Balance,
	pub carry_count: u32,
	pub active_council: Vec<(T::AccountId, T::BlockNumber)>,
	pub approval_voting_period: T::BlockNumber,
	pub presentation_duration: T::BlockNumber,
	pub desired_seats: u32,
	pub term_duration: T::BlockNumber,
	pub inactive_grace_period: T::BlockNumber,


	// for the council's votes.
	pub cooloff_period: T::BlockNumber,
	pub voting_period: T::BlockNumber,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			candidacy_bond: T::Balance::sa(9),
			voter_bond: T::Balance::sa(0),
			present_slash_per_voter: T::Balance::sa(1),
			carry_count: 2,
			inactive_grace_period: T::BlockNumber::sa(1),
			active_council: vec![],
			approval_voting_period: T::BlockNumber::sa(1000),
			presentation_duration: T::BlockNumber::sa(1000),
			desired_seats: 0,
			term_duration: T::BlockNumber::sa(5),
			cooloff_period: T::BlockNumber::sa(1000),
			voting_period: T::BlockNumber::sa(3),
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
			twox_128(<CandidacyBond<T>>::key()).to_vec() => self.candidacy_bond.encode(),
			twox_128(<VotingBond<T>>::key()).to_vec() => self.voter_bond.encode(),
			twox_128(<PresentSlashPerVoter<T>>::key()).to_vec() => self.present_slash_per_voter.encode(),
			twox_128(<CarryCount<T>>::key()).to_vec() => self.carry_count.encode(),
			twox_128(<PresentationDuration<T>>::key()).to_vec() => self.presentation_duration.encode(),
			twox_128(<VotingPeriod<T>>::key()).to_vec() => self.approval_voting_period.encode(),
			twox_128(<TermDuration<T>>::key()).to_vec() => self.term_duration.encode(),
			twox_128(<DesiredSeats<T>>::key()).to_vec() => self.desired_seats.encode(),
			twox_128(<InactiveGracePeriod<T>>::key()).to_vec() => self.inactive_grace_period.encode(),
			twox_128(<ActiveCouncil<T>>::key()).to_vec() => self.active_council.encode(),

			twox_128(<voting::CooloffPeriod<T>>::key()).to_vec() => self.cooloff_period.encode(),
			twox_128(<voting::VotingPeriod<T>>::key()).to_vec() => self.voting_period.encode(),
			twox_128(<voting::Proposals<T>>::key()).to_vec() => vec![0u8; 0].encode()
		]
	}
}

#[cfg(test)]
mod tests {
	pub use super::*;
	pub use runtime_io::with_externalities;
	pub use substrate_primitives::H256;
	use primitives::BuildExternalities;
	use primitives::traits::{HasPublicAux, Identity};
	use primitives::testing::{Digest, Header};

	impl_outer_dispatch! {
		pub enum Proposal {
			Staking = 0,
			Democracy = 1,
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
	impl democracy::Trait for Test {
		type Proposal = Proposal;
	}
	impl Trait for Test {}

	pub fn new_test_ext(with_council: bool) -> runtime_io::TestExternalities {
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
			bonding_duration: 0,
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
		}.build_externalities());
		t.extend(democracy::GenesisConfig::<Test>{
			launch_period: 1,
			voting_period: 3,
			minimum_deposit: 1,
		}.build_externalities());
		t.extend(GenesisConfig::<Test>{
			candidacy_bond: 9,
			voter_bond: 3,
			present_slash_per_voter: 1,
			carry_count: 2,
			inactive_grace_period: 1,
			active_council: if with_council { vec![
				(1, 10),
				(2, 10),
				(3, 10)
			] } else { vec![] },
			approval_voting_period: 4,
			presentation_duration: 2,
			desired_seats: 2,
			term_duration: 5,
			cooloff_period: 2,
			voting_period: 1,
		}.build_externalities());
		t
	}

	pub type System = system::Module<Test>;
	pub type Staking = staking::Module<Test>;
	pub type Democracy = democracy::Module<Test>;
	pub type Council = Module<Test>;

	#[test]
	fn params_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::next_vote_from(1), 4);
			assert_eq!(Council::next_vote_from(4), 4);
			assert_eq!(Council::next_vote_from(5), 8);
			assert_eq!(Council::vote_index(), 0);
			assert_eq!(Council::candidacy_bond(), 9);
			assert_eq!(Council::voting_bond(), 3);
			assert_eq!(Council::present_slash_per_voter(), 1);
			assert_eq!(Council::presentation_duration(), 2);
			assert_eq!(Council::voting_period(), 4);
			assert_eq!(Council::term_duration(), 5);
			assert_eq!(Council::desired_seats(), 2);
			assert_eq!(Council::carry_count(), 2);

			assert_eq!(Council::active_council(), vec![]);
			assert_eq!(Council::next_tally(), Some(4));
			assert_eq!(Council::presentation_active(), false);
			assert_eq!(Council::next_finalise(), None);

			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_eq!(Council::is_a_candidate(&1), false);
			assert_eq!(Council::candidate_reg_info(1), None);

			assert_eq!(Council::voters(), Vec::<u64>::new());
			assert_eq!(Council::voter_last_active(1), None);
			assert_eq!(Council::approvals_of(1), vec![]);
		});
	}

	#[test]
	fn simple_candidate_submission_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_eq!(Council::candidate_reg_info(1), None);
			assert_eq!(Council::candidate_reg_info(2), None);
			assert_eq!(Council::is_a_candidate(&1), false);
			assert_eq!(Council::is_a_candidate(&2), false);

			Council::submit_candidacy(&1, 0);
			assert_eq!(Council::candidates(), vec![1]);
			assert_eq!(Council::candidate_reg_info(1), Some((0, 0)));
			assert_eq!(Council::candidate_reg_info(2), None);
			assert_eq!(Council::is_a_candidate(&1), true);
			assert_eq!(Council::is_a_candidate(&2), false);

			Council::submit_candidacy(&2, 1);
			assert_eq!(Council::candidates(), vec![1, 2]);
			assert_eq!(Council::candidate_reg_info(1), Some((0, 0)));
			assert_eq!(Council::candidate_reg_info(2), Some((0, 1)));
			assert_eq!(Council::is_a_candidate(&1), true);
			assert_eq!(Council::is_a_candidate(&2), true);
		});
	}

	fn new_test_ext_with_candidate_holes() -> runtime_io::TestExternalities {
		let mut t = new_test_ext(false);
		with_externalities(&mut t, || {
			<Candidates<Test>>::put(vec![0, 0, 1]);
			<CandidateCount<Test>>::put(1);
			<RegisterInfoOf<Test>>::insert(1, (0, 2));
		});
		t
	}

	#[test]
	fn candidate_submission_using_free_slot_should_work() {
		let mut t = new_test_ext_with_candidate_holes();

		with_externalities(&mut t, || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), vec![0, 0, 1]);

			Council::submit_candidacy(&2, 1);
			assert_eq!(Council::candidates(), vec![0, 2, 1]);

			Council::submit_candidacy(&3, 0);
			assert_eq!(Council::candidates(), vec![3, 2, 1]);
		});
	}

	#[test]
	fn candidate_submission_using_alternative_free_slot_should_work() {
		let mut t = new_test_ext_with_candidate_holes();

		with_externalities(&mut t, || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), vec![0, 0, 1]);

			Council::submit_candidacy(&2, 0);
			assert_eq!(Council::candidates(), vec![2, 0, 1]);

			Council::submit_candidacy(&3, 1);
			assert_eq!(Council::candidates(), vec![2, 3, 1]);
		});
	}

	#[test]
	fn candidate_submission_not_using_free_slot_should_not_work() {
		with_externalities(&mut new_test_ext_with_candidate_holes(), || {
			System::set_block_number(1);
			assert_noop!{Council::submit_candidacy(&4, 3)};	// gives "invalid candidate slot"
		});
	}

	#[test]
	fn bad_candidate_slot_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!{Council::submit_candidacy(&1, 1)};	// gives "invalid candidate slot"
		});
	}

	#[test]
	fn non_free_candidate_slot_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			Council::submit_candidacy(&1, 0);
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!{Council::submit_candidacy(&2, 0)};	// gives "invalid candidate slot"
		});
	}

	#[test]
	fn dupe_candidate_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			Council::submit_candidacy(&1, 0);
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!{Council::submit_candidacy(&1, 1)};	// gives "duplicate candidate submission"
		});
	}

	#[test]
	fn poor_candidate_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!{Council::submit_candidacy(&7, 0)};	// gives "candidate has not enough funds"
		});
	}

	#[test]
	fn voting_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);

			Council::submit_candidacy(&5, 0);

			Council::set_approvals(&1, vec![true], 0);
			Council::set_approvals(&4, vec![true], 0);

			assert_eq!(Council::approvals_of(1), vec![true]);
			assert_eq!(Council::approvals_of(4), vec![true]);
			assert_eq!(Council::voters(), vec![1, 4]);

			Council::submit_candidacy(&2, 1);
			Council::submit_candidacy(&3, 2);

			Council::set_approvals(&2, vec![false, true, true], 0);
			Council::set_approvals(&3, vec![false, true, true], 0);

			assert_eq!(Council::approvals_of(1), vec![true]);
			assert_eq!(Council::approvals_of(4), vec![true]);
			assert_eq!(Council::approvals_of(2), vec![false, true, true]);
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);

			assert_eq!(Council::voters(), vec![1, 4, 2, 3]);
		});
	}

	#[test]
	fn resubmitting_voting_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);

			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&4, vec![true], 0);

			assert_eq!(Council::approvals_of(4), vec![true]);

			Council::submit_candidacy(&2, 1);
			Council::submit_candidacy(&3, 2);
			Council::set_approvals(&4, vec![true, false, true], 0);

			assert_eq!(Council::approvals_of(4), vec![true, false, true]);
		});
	}

	#[test]
	fn retracting_voter_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);

			Council::submit_candidacy(&5, 0);
			Council::submit_candidacy(&2, 1);
			Council::submit_candidacy(&3, 2);

			Council::set_approvals(&1, vec![true], 0);
			Council::set_approvals(&2, vec![false, true, true], 0);
			Council::set_approvals(&3, vec![false, true, true], 0);
			Council::set_approvals(&4, vec![true, false, true], 0);

			assert_eq!(Council::voters(), vec![1, 2, 3, 4]);
			assert_eq!(Council::approvals_of(1), vec![true]);
			assert_eq!(Council::approvals_of(2), vec![false, true, true]);
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			Council::retract_voter(&1, 0);

			assert_eq!(Council::voters(), vec![4, 2, 3]);
			assert_eq!(Council::approvals_of(1), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(2), vec![false, true, true]);
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			Council::retract_voter(&2, 1);

			assert_eq!(Council::voters(), vec![4, 3]);
			assert_eq!(Council::approvals_of(1), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(2), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			Council::retract_voter(&3, 1);

			assert_eq!(Council::voters(), vec![4]);
			assert_eq!(Council::approvals_of(1), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(2), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(3), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);
		});
	}

	#[test]
	fn invalid_retraction_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			Council::submit_candidacy(&3, 0);
			Council::set_approvals(&1, vec![true], 0);
			Council::set_approvals(&2, vec![true], 0);
			assert_eq!(Council::voters(), vec![1, 2]);
			assert_noop!{Council::retract_voter(&1, 1)};	// gives "retraction index mismatch"
		});
	}

	#[test]
	fn overflow_retraction_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			Council::submit_candidacy(&3, 0);
			Council::set_approvals(&1, vec![true], 0);
			assert_noop!{Council::retract_voter(&1, 1)};	// gives "retraction index invalid"
		});
	}

	#[test]
	fn non_voter_retraction_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			Council::submit_candidacy(&3, 0);
			Council::set_approvals(&1, vec![true], 0);
			assert_noop!{Council::retract_voter(&2, 0)};	// gives "cannot retract non-voter"
		});
	}

	#[test]
	fn simple_tally_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			Council::submit_candidacy(&2, 0);
			Council::submit_candidacy(&5, 1);
			Council::set_approvals(&2, vec![true, false], 0);
			Council::set_approvals(&5, vec![false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			assert!(Council::presentation_active());
			Council::present_winner(&4, 2, 11, 0);
			Council::present_winner(&4, 5, 41, 0);
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (0, 0), (11, 2), (41, 5)]));

			Council::end_block(System::block_number());

			assert!(!Council::presentation_active());
			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);

			assert!(!Council::is_a_candidate(&2));
			assert!(!Council::is_a_candidate(&5));
			assert_eq!(Council::vote_index(), 1);
			assert_eq!(Council::voter_last_active(2), Some(0));
			assert_eq!(Council::voter_last_active(5), Some(0));
		});
	}

	#[test]
	fn double_presentations_should_be_punished() {
		with_externalities(&mut new_test_ext(false), || {
			assert!(Staking::can_slash(&4, 10));

			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::submit_candidacy(&5, 1);
			Council::set_approvals(&2, vec![true, false], 0);
			Council::set_approvals(&5, vec![false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::present_winner(&4, 5, 41, 0);
			Council::present_winner(&4, 5, 41, 0);
			Council::end_block(System::block_number());

			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);
			assert_eq!(Staking::balance(&4), 38);
		});
	}

	#[test]
	fn retracting_inactive_voter_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&5, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 5, 41, 1);
			Council::end_block(System::block_number());

			Council::reap_inactive_voter(&5,
				Council::voters().iter().position(|&i| i == 5).unwrap() as u32,
				2, Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			);

			assert_eq!(Council::voters(), vec![5]);
			assert_eq!(Council::approvals_of(2).len(), 0);
			assert_eq!(Staking::balance(&2), 17);
			assert_eq!(Staking::balance(&5), 53);
		});
	}

	#[test]
	fn presenting_for_double_election_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			assert_noop!{Council::present_winner(&4, 2, 11, 1)};	// gives "candidate must not form a duplicated member if elected"
		});
	}

	#[test]
	fn retracting_inactive_voter_with_other_candidates_in_slots_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&5, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 5, 41, 1);
			Council::end_block(System::block_number());

			System::set_block_number(11);
			Council::submit_candidacy(&1, 0);

			Council::reap_inactive_voter(&5,
				Council::voters().iter().position(|&i| i == 5).unwrap() as u32,
				2, Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			);

			assert_eq!(Council::voters(), vec![5]);
			assert_eq!(Council::approvals_of(2).len(), 0);
			assert_eq!(Staking::balance(&2), 17);
			assert_eq!(Staking::balance(&5), 53);
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_reporter_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 8, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&5, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 5, 38, 1);
			Council::end_block(System::block_number());

			assert_noop!{Council::reap_inactive_voter(&2,
				42,
				2, Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			)};	// given "bad reporter index"
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_target_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 8, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&5, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 5, 38, 1);
			Council::end_block(System::block_number());

			assert_noop!{Council::reap_inactive_voter(&2,
				Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2, 42,
				2
			)};	// gives "bad target index"
		});
	}

	#[test]
	fn attempting_to_retract_active_voter_should_slash_reporter() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::submit_candidacy(&3, 1);
			Council::submit_candidacy(&4, 2);
			Council::submit_candidacy(&5, 3);
			Council::set_approvals(&2, vec![true, false, false, false], 0);
			Council::set_approvals(&3, vec![false, true, false, false], 0);
			Council::set_approvals(&4, vec![false, false, true, false], 0);
			Council::set_approvals(&5, vec![false, false, false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::present_winner(&4, 3, 21, 0);
			Council::present_winner(&4, 4, 31, 0);
			Council::present_winner(&4, 5, 41, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::set_desired_seats(3);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 2, 11, 1);
			Council::present_winner(&4, 3, 21, 1);
			Council::end_block(System::block_number());

			Council::reap_inactive_voter(&4,
				Council::voters().iter().position(|&i| i == 4).unwrap() as u32,
				2, Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			);

			assert_eq!(Council::voters(), vec![2, 3, 5]);
			assert_eq!(Council::approvals_of(4).len(), 0);
			assert_eq!(Staking::balance(&4), 37);
		});
	}

	#[test]
	fn attempting_to_retract_inactive_voter_by_nonvoter_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::set_approvals(&2, vec![true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::submit_candidacy(&5, 0);
			Council::set_approvals(&5, vec![true], 1);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 5, 41, 1);
			Council::end_block(System::block_number());

			assert_noop!{Council::reap_inactive_voter(&4,
				0,
				2, Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			)};	// gives "reaper must be a voter"
		});
	}

	#[test]
	fn presenting_loser_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&1, 0);
			Council::set_approvals(&6, vec![true], 0);
			Council::submit_candidacy(&2, 1);
			Council::set_approvals(&2, vec![false, true], 0);
			Council::submit_candidacy(&3, 2);
			Council::set_approvals(&3, vec![false, false, true], 0);
			Council::submit_candidacy(&4, 3);
			Council::set_approvals(&4, vec![false, false, false, true], 0);
			Council::submit_candidacy(&5, 4);
			Council::set_approvals(&5, vec![false, false, false, false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 1, 60, 0);
			Council::present_winner(&4, 3, 21, 0);
			Council::present_winner(&4, 4, 31, 0);
			Council::present_winner(&4, 5, 41, 0);
			assert_noop!{Council::present_winner(&4, 2, 11, 0)};	// gives "candidate not worthy of leaderboard"
		});
	}

	#[test]
	fn presenting_loser_first_should_not_matter() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&1, 0);
			Council::set_approvals(&6, vec![true], 0);
			Council::submit_candidacy(&2, 1);
			Council::set_approvals(&2, vec![false, true], 0);
			Council::submit_candidacy(&3, 2);
			Council::set_approvals(&3, vec![false, false, true], 0);
			Council::submit_candidacy(&4, 3);
			Council::set_approvals(&4, vec![false, false, false, true], 0);
			Council::submit_candidacy(&5, 4);
			Council::set_approvals(&5, vec![false, false, false, false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 11, 0);
			Council::present_winner(&4, 1, 60, 0);
			Council::present_winner(&4, 3, 21, 0);
			Council::present_winner(&4, 4, 31, 0);
			Council::present_winner(&4, 5, 41, 0);

			assert_eq!(Council::leaderboard(), Some(vec![
				(21, 3),
				(31, 4),
				(41, 5),
				(60, 1)
			]));
		});
	}

	#[test]
	fn present_outside_of_presentation_period_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_noop!{Council::present_winner(&5, 5, 1, 0)};	// gives "cannot present outside of presentation period"
		});
	}

	#[test]
	fn present_with_invalid_vote_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&2, 0);
			Council::submit_candidacy(&5, 1);
			Council::set_approvals(&2, vec![true, false], 0);
			Council::set_approvals(&5, vec![false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			assert_noop!{Council::present_winner(&4, 2, 11, 1)};	// gives "index not current"
		});
	}

	#[test]
	fn present_when_presenter_is_poor_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			Council::submit_candidacy(&1, 0);
			Council::submit_candidacy(&5, 1);
			Council::set_approvals(&2, vec![true, false], 0);
			Council::set_approvals(&5, vec![false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			assert_eq!(Staking::balance(&1), 1);
			assert_noop!{Council::present_winner(&1, 1, 30, 0)};	// gives "presenter must have sufficient slashable funds"
		});
	}

	#[test]
	fn invalid_present_tally_should_slash() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_eq!(Staking::balance(&4), 40);

			Council::submit_candidacy(&2, 0);
			Council::submit_candidacy(&5, 1);
			Council::set_approvals(&2, vec![true, false], 0);
			Council::set_approvals(&5, vec![false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 2, 80, 0);

			assert_eq!(Staking::balance(&4), 38);
		});
	}

	#[test]
	fn runners_up_should_be_kept() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			Council::submit_candidacy(&1, 0);
			Council::set_approvals(&6, vec![true], 0);
			Council::submit_candidacy(&2, 1);
			Council::set_approvals(&2, vec![false, true], 0);
			Council::submit_candidacy(&3, 2);
			Council::set_approvals(&3, vec![false, false, true], 0);
			Council::submit_candidacy(&4, 3);
			Council::set_approvals(&4, vec![false, false, false, true], 0);
			Council::submit_candidacy(&5, 4);
			Council::set_approvals(&5, vec![false, false, false, false, true], 0);

			Council::end_block(System::block_number());

			System::set_block_number(6);
			assert!(Council::presentation_active());
			Council::present_winner(&4, 1, 60, 0);
			assert_eq!(Council::leaderboard(), Some(vec![
				(0, 0),
				(0, 0),
				(0, 0),
				(60, 1)
			]));
			Council::present_winner(&4, 3, 21, 0);
			Council::present_winner(&4, 4, 31, 0);
			Council::present_winner(&4, 5, 41, 0);
			assert_eq!(Council::leaderboard(), Some(vec![
				(21, 3),
				(31, 4),
				(41, 5),
				(60, 1)
			]));

			Council::end_block(System::block_number());

			assert!(!Council::presentation_active());
			assert_eq!(Council::active_council(), vec![(1, 11), (5, 11)]);

			assert!(!Council::is_a_candidate(&1));
			assert!(!Council::is_a_candidate(&5));
			assert!(!Council::is_a_candidate(&2));
			assert!(Council::is_a_candidate(&3));
			assert!(Council::is_a_candidate(&4));
			assert_eq!(Council::vote_index(), 1);
			assert_eq!(Council::voter_last_active(2), Some(0));
			assert_eq!(Council::voter_last_active(3), Some(0));
			assert_eq!(Council::voter_last_active(4), Some(0));
			assert_eq!(Council::voter_last_active(5), Some(0));
			assert_eq!(Council::voter_last_active(6), Some(0));
			assert_eq!(Council::candidate_reg_info(3), Some((0, 2)));
			assert_eq!(Council::candidate_reg_info(4), Some((0, 3)));
		});
	}

	#[test]
	fn second_tally_should_use_runners_up() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			Council::submit_candidacy(&1, 0);
			Council::set_approvals(&6, vec![true], 0);
			Council::submit_candidacy(&2, 1);
			Council::set_approvals(&2, vec![false, true], 0);
			Council::submit_candidacy(&3, 2);
			Council::set_approvals(&3, vec![false, false, true], 0);
			Council::submit_candidacy(&4, 3);
			Council::set_approvals(&4, vec![false, false, false, true], 0);
			Council::submit_candidacy(&5, 4);
			Council::set_approvals(&5, vec![false, false, false, false, true], 0);
			Council::end_block(System::block_number());

			System::set_block_number(6);
			Council::present_winner(&4, 1, 60, 0);
			Council::present_winner(&4, 3, 21, 0);
			Council::present_winner(&4, 4, 31, 0);
			Council::present_winner(&4, 5, 41, 0);
			Council::end_block(System::block_number());

			System::set_block_number(8);
			Council::set_approvals(&6, vec![false, false, true, false], 1);
			Council::set_desired_seats(3);
			Council::end_block(System::block_number());

			System::set_block_number(10);
			Council::present_winner(&4, 3, 81, 1);
			Council::present_winner(&4, 4, 31, 1);
			Council::end_block(System::block_number());

			assert!(!Council::presentation_active());
			assert_eq!(Council::active_council(), vec![(1, 11), (5, 11), (3, 15)]);

			assert!(!Council::is_a_candidate(&1));
			assert!(!Council::is_a_candidate(&2));
			assert!(!Council::is_a_candidate(&3));
			assert!(!Council::is_a_candidate(&5));
			assert!(Council::is_a_candidate(&4));
			assert_eq!(Council::vote_index(), 2);
			assert_eq!(Council::voter_last_active(2), Some(0));
			assert_eq!(Council::voter_last_active(3), Some(0));
			assert_eq!(Council::voter_last_active(4), Some(0));
			assert_eq!(Council::voter_last_active(5), Some(0));
			assert_eq!(Council::voter_last_active(6), Some(1));

			assert_eq!(Council::candidate_reg_info(4), Some((0, 3)));
		});
	}
}
