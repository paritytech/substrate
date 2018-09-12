// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Council system: Handles the voting in and maintenance of council members.

use rstd::prelude::*;
use primitives::traits::{Zero, One, As, Lookup, OnFinalise};
use runtime_io::print;
use srml_support::{StorageValue, StorageMap, dispatch::Result};
use democracy;
use balances::{self, address::Address};
use system::{self, ensure_signed, ensure_root};

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

pub trait Trait: democracy::Trait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn set_approvals(origin, votes: Vec<bool>, index: VoteIndex) -> Result;
		fn reap_inactive_voter(origin, reporter_index: u32, who: Address<T::AccountId, T::AccountIndex>, who_index: u32, assumed_vote_index: VoteIndex) -> Result;
		fn retract_voter(origin, index: u32) -> Result;
		fn submit_candidacy(origin, slot: u32) -> Result;
		fn present_winner(origin, candidate: Address<T::AccountId, T::AccountIndex>, total: T::Balance, index: VoteIndex) -> Result;

		fn set_desired_seats(origin, count: u32) -> Result;
		fn remove_member(origin, who: Address<T::AccountId, T::AccountIndex>) -> Result;
		fn set_presentation_duration(origin, count: T::BlockNumber) -> Result;
		fn set_term_duration(origin, count: T::BlockNumber) -> Result;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Council {

		// parameters
		/// How much should be locked up in order to submit one's candidacy.
		pub CandidacyBond get(candidacy_bond): required T::Balance;
		/// How much should be locked up in order to be able to submit votes.
		pub VotingBond get(voting_bond): required T::Balance;
		/// The punishment, per voter, if you provide an invalid presentation.
		pub PresentSlashPerVoter get(present_slash_per_voter): required T::Balance;
		/// How many runners-up should have their approvals persist until the next vote.
		pub CarryCount get(carry_count): required u32;
		/// How long to give each top candidate to present themselves after the vote ends.
		pub PresentationDuration get(presentation_duration): required T::BlockNumber;
		/// How many votes need to go by after a voter's last vote before they can be reaped if their
		/// approvals are moot.
		pub InactiveGracePeriod get(inactivity_grace_period): required VoteIndex;
		/// How often (in blocks) to check for new votes.
		pub VotingPeriod get(voting_period): required T::BlockNumber;
		/// How long each position is active for.
		pub TermDuration get(term_duration): required T::BlockNumber;
		/// Number of accounts that should be sitting on the council.
		pub DesiredSeats get(desired_seats): required u32;

		// permanent state (always relevant, changes only at the finalisation of voting)
		/// The current council. When there's a vote going on, this should still be used for executive
		/// matters.
		pub ActiveCouncil get(active_council): default Vec<(T::AccountId, T::BlockNumber)>;
		/// The total number of votes that have happened or are in progress.
		pub VoteCount get(vote_index): default VoteIndex;

		// persistent state (always relevant, changes constantly)
		/// The last cleared vote index that this voter was last active at.
		pub ApprovalsOf get(approvals_of): default map [ T::AccountId => Vec<bool> ];
		/// The vote index and list slot that the candidate `who` was registered or `None` if they are not
		/// currently registered.
		pub RegisterInfoOf get(candidate_reg_info): map [ T::AccountId => (VoteIndex, u32) ];
		/// The last cleared vote index that this voter was last active at.
		pub LastActiveOf get(voter_last_active): map [ T::AccountId => VoteIndex ];
		/// The present voter list.
		pub Voters get(voters): default Vec<T::AccountId>;
		/// The present candidate list.
		pub Candidates get(candidates): default Vec<T::AccountId>; // has holes
		pub CandidateCount get(candidate_count): default u32;

		// temporary state (only relevant during finalisation/presentation)
		/// The accounts holding the seats that will become free on the next tally.
		pub NextFinalise get(next_finalise): (T::BlockNumber, u32, Vec<T::AccountId>);
		/// The stakes as they were at the point that the vote ended.
		pub SnapshotedStakes get(snapshoted_stakes): required Vec<T::Balance>;
		/// Get the leaderboard if we;re in the presentation phase.
		pub Leaderboard get(leaderboard): Vec<(T::Balance, T::AccountId)>; // ORDERED low -> high
	}
}

decl_event!(
	/// An event in this module.
	pub enum Event<T> with RawEvent<AccountId>
		where <T as system::Trait>::AccountId
	{
		/// reaped voter, reaper
		VoterReaped(AccountId, AccountId),
		/// slashed reaper
		BadReaperSlashed(AccountId),
		/// A tally (for approval votes of council seat(s)) has started.
		TallyStarted(u32),
		/// A tally (for approval votes of council seat(s)) has ended (with one or more new members).
		TallyFinalised(Vec<AccountId>, Vec<AccountId>),
	}
);

impl<T: Trait> Module<T> {

	/// Deposit one of this module's events.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

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
	fn set_approvals(origin: T::Origin, votes: Vec<bool>, index: VoteIndex) -> Result {
		let who = ensure_signed(origin)?;

		ensure!(!Self::presentation_active(), "no approval changes during presentation period");
		ensure!(index == Self::vote_index(), "incorrect vote index");
		if !<LastActiveOf<T>>::exists(&who) {
			// not yet a voter - deduct bond.
			// NOTE: this must be the last potential bailer, since it changes state.
			<balances::Module<T>>::reserve(&who, Self::voting_bond())?;

			<Voters<T>>::put({
				let mut v = Self::voters();
				v.push(who.clone());
				v
			});
		}
		<LastActiveOf<T>>::insert(&who, index);
		<ApprovalsOf<T>>::insert(&who, votes);
		Ok(())
	}

	/// Remove a voter. For it not to be a bond-consuming no-op, all approved candidate indices
	/// must now be either unregistered or registered to a candidate that registered the slot after
	/// the voter gave their last approval set.
	///
	/// May be called by anyone. Returns the voter deposit to `signed`.
	fn reap_inactive_voter(
		origin: T::Origin,
		reporter_index: u32,
		who: Address<T::AccountId, T::AccountIndex>,
		who_index: u32,
		assumed_vote_index: VoteIndex
	) -> Result {
		let reporter = ensure_signed(origin)?;

		let who = <balances::Module<T>>::lookup(who)?;
		ensure!(!Self::presentation_active(), "cannot reap during presentation period");
		ensure!(Self::voter_last_active(&reporter).is_some(), "reporter must be a voter");
		let last_active = Self::voter_last_active(&who).ok_or("target for inactivity cleanup must be active")?;
		ensure!(assumed_vote_index == Self::vote_index(), "vote index not current");
		ensure!(last_active < assumed_vote_index - Self::inactivity_grace_period(), "cannot reap during grace perid");
		let voters = Self::voters();
		let reporter_index = reporter_index as usize;
		let who_index = who_index as usize;
		ensure!(reporter_index < voters.len() && voters[reporter_index] == reporter, "bad reporter index");
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
			if valid { &who } else { &reporter },
			if valid { who_index } else { reporter_index },
			voters
		);
		if valid {
			// This only fails if `who` doesn't exist, which it clearly must do since its the origin.
			// Still, it's no more harmful to propagate any error at this point.
			<balances::Module<T>>::repatriate_reserved(&who, &reporter, Self::voting_bond())?;
			Self::deposit_event(RawEvent::VoterReaped(who, reporter));
		} else {
			<balances::Module<T>>::slash_reserved(&reporter, Self::voting_bond());
			Self::deposit_event(RawEvent::BadReaperSlashed(reporter));
		}
		Ok(())
	}

	/// Remove a voter. All votes are cancelled and the voter deposit is returned.
	fn retract_voter(origin: T::Origin, index: u32) -> Result {
		let who = ensure_signed(origin)?;

		ensure!(!Self::presentation_active(), "cannot retract when presenting");
		ensure!(<LastActiveOf<T>>::exists(&who), "cannot retract non-voter");
		let voters = Self::voters();
		let index = index as usize;
		ensure!(index < voters.len(), "retraction index invalid");
		ensure!(voters[index] == who, "retraction index mismatch");

		Self::remove_voter(&who, index, voters);
		<balances::Module<T>>::unreserve(&who, Self::voting_bond());
		Ok(())
	}

	/// Submit oneself for candidacy.
	///
	/// Account must have enough transferrable funds in it to pay the bond.
	fn submit_candidacy(origin: T::Origin, slot: u32) -> Result {
		let who = ensure_signed(origin)?;

		ensure!(!Self::is_a_candidate(&who), "duplicate candidate submission");
		let slot = slot as usize;
		let count = Self::candidate_count() as usize;
		let candidates = Self::candidates();
		ensure!(
			(slot == count && count == candidates.len()) ||
			(slot < candidates.len() && candidates[slot] == T::AccountId::default()),
			"invalid candidate slot"
		);
		// NOTE: This must be last as it has side-effects.
		<balances::Module<T>>::reserve(&who, Self::candidacy_bond())
			.map_err(|_| "candidate has not enough funds")?;

		<RegisterInfoOf<T>>::insert(&who, (Self::vote_index(), slot as u32));
		let mut candidates = candidates;
		if slot == candidates.len() {
			candidates.push(who);
		} else {
			candidates[slot] = who;
		}
		<Candidates<T>>::put(candidates);
		<CandidateCount<T>>::put(count as u32 + 1);
		Ok(())
	}

	/// Claim that `signed` is one of the top Self::carry_count() + current_vote().1 candidates.
	/// Only works if the `block_number >= current_vote().0` and `< current_vote().0 + presentation_duration()``
	/// `signed` should have at least
	fn present_winner(
		origin: T::Origin,
		candidate: Address<T::AccountId, T::AccountIndex>,
		total: T::Balance,
		index: VoteIndex
	) -> Result {
		let who = ensure_signed(origin)?;

		let candidate = <balances::Module<T>>::lookup(candidate)?;
		ensure!(index == Self::vote_index(), "index not current");
		let (_, _, expiring) = Self::next_finalise().ok_or("cannot present outside of presentation period")?;
		let stakes = Self::snapshoted_stakes();
		let voters = Self::voters();
		let bad_presentation_punishment = Self::present_slash_per_voter() * T::Balance::sa(voters.len() as u64);
		ensure!(<balances::Module<T>>::can_slash(&who, bad_presentation_punishment), "presenter must have sufficient slashable funds");

		let mut leaderboard = Self::leaderboard().ok_or("leaderboard must exist while present phase active")?;
		ensure!(total > leaderboard[0].0, "candidate not worthy of leaderboard");

		if let Some(p) = Self::active_council().iter().position(|&(ref c, _)| c == &candidate) {
			ensure!(p < expiring.len(), "candidate must not form a duplicated member if elected");
		}

		let (registered_since, candidate_index): (VoteIndex, u32) =
			Self::candidate_reg_info(&candidate).ok_or("presented candidate must be current")?;
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
			Ok(())
		} else {
			// we can rest assured it will be Ok since we checked `can_slash` earlier; still
			// better safe than sorry.
			let _ = <balances::Module<T>>::slash(&who, bad_presentation_punishment);
			Err(if dupe { "duplicate presentation" } else { "incorrect total" })
		}
	}

	/// Set the desired member count; if lower than the current count, then seats will not be up
	/// election when they expire. If more, then a new vote will be started if one is not already
	/// in progress.
	fn set_desired_seats(origin: T::Origin, count: u32) -> Result {
		ensure_root(origin)?;
		<DesiredSeats<T>>::put(count);
		Ok(())
	}

	/// Remove a particular member. A tally will happen instantly (if not already in a presentation
	/// period) to fill the seat if removal means that the desired members are not met.
	/// This is effective immediately.
	fn remove_member(origin: T::Origin, who: Address<T::AccountId, T::AccountIndex>) -> Result {
		ensure_root(origin)?;
		let who = <balances::Module<T>>::lookup(who)?;
		let new_council: Vec<(T::AccountId, T::BlockNumber)> = Self::active_council()
			.into_iter()
			.filter(|i| i.0 != who)
			.collect();
		<ActiveCouncil<T>>::put(new_council);
		Ok(())
	}

	/// Set the presentation duration. If there is currently a vote being presented for, will
	/// invoke `finalise_vote`.
	fn set_presentation_duration(origin: T::Origin, count: T::BlockNumber) -> Result {
		ensure_root(origin)?;
		<PresentationDuration<T>>::put(count);
		Ok(())
	}

	/// Set the presentation duration. If there is current a vote being presented for, will
	/// invoke `finalise_vote`.
	fn set_term_duration(origin: T::Origin, count: T::BlockNumber) -> Result {
		ensure_root(origin)?;
		<TermDuration<T>>::put(count);
		Ok(())
	}

	// private

	/// Check there's nothing to do this block
	fn end_block(block_number: T::BlockNumber) -> Result {
		if (block_number % Self::voting_period()).is_zero() {
			if let Some(number) = Self::next_tally() {
				if block_number == number {
					Self::start_tally();
				}
			}
		}
		if let Some((number, _, _)) = Self::next_finalise() {
			if block_number == number {
				Self::finalise_tally()?
			}
		}
		Ok(())
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
			let votes = voters.iter().map(<balances::Module<T>>::total_balance).collect::<Vec<_>>();
			<SnapshotedStakes<T>>::put(votes);

			// initialise leaderboard.
			let leaderboard_size = empty_seats + Self::carry_count() as usize;
			<Leaderboard<T>>::put(vec![(T::Balance::zero(), T::AccountId::default()); leaderboard_size]);

			Self::deposit_event(RawEvent::TallyStarted(empty_seats as u32));
		}
	}

	/// Finalise the vote, removing each of the `removals` and inserting `seats` of the most approved
	/// candidates in their place. If the total council members is less than the desired membership
	/// a new vote is started.
	/// Clears all presented candidates, returning the bond of the elected ones.
	fn finalise_tally() -> Result {
		<SnapshotedStakes<T>>::kill();
		let (_, coming, expiring): (T::BlockNumber, u32, Vec<T::AccountId>) =
			<NextFinalise<T>>::take().ok_or("finalise can only be called after a tally is started.")?;
		let leaderboard: Vec<(T::Balance, T::AccountId)> = <Leaderboard<T>>::take().unwrap_or_default();
		let new_expiry = <system::Module<T>>::block_number() + Self::term_duration();

		// return bond to winners.
		let candidacy_bond = Self::candidacy_bond();
		let incoming: Vec<T::AccountId> = leaderboard.iter()
			.rev()
			.take_while(|&&(b, _)| !b.is_zero())
			.take(coming as usize)
			.map(|(_, a)| a)
			.cloned()
			.inspect(|a| {<balances::Module<T>>::unreserve(a, candidacy_bond);})
			.collect();
		let active_council = Self::active_council();
		let outgoing = active_council.iter().take(expiring.len()).map(|a| a.0.clone()).collect();

		// set the new council.
		let mut new_council: Vec<_> = active_council
			.into_iter()
			.skip(expiring.len())
			.chain(incoming.iter().cloned().map(|a| (a, new_expiry)))
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

		Self::deposit_event(RawEvent::TallyFinalised(incoming, outgoing));

		<Candidates<T>>::put(new_candidates);
		<CandidateCount<T>>::put(count);
		<VoteCount<T>>::put(Self::vote_index() + 1);
		Ok(())
	}
}

impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(n: T::BlockNumber) {
		if let Err(e) = Self::end_block(n) {
			print("Guru meditation");
			print(e);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use ::tests::*;

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

			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_eq!(Council::candidates(), vec![1]);
			assert_eq!(Council::candidate_reg_info(1), Some((0, 0)));
			assert_eq!(Council::candidate_reg_info(2), None);
			assert_eq!(Council::is_a_candidate(&1), true);
			assert_eq!(Council::is_a_candidate(&2), false);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_eq!(Council::candidates(), vec![1, 2]);
			assert_eq!(Council::candidate_reg_info(1), Some((0, 0)));
			assert_eq!(Council::candidate_reg_info(2), Some((0, 1)));
			assert_eq!(Council::is_a_candidate(&1), true);
			assert_eq!(Council::is_a_candidate(&2), true);
		});
	}

	fn new_test_ext_with_candidate_holes() -> runtime_io::TestExternalities<Blake2Hasher> {
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

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_eq!(Council::candidates(), vec![0, 2, 1]);

			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_eq!(Council::candidates(), vec![3, 2, 1]);
		});
	}

	#[test]
	fn candidate_submission_using_alternative_free_slot_should_work() {
		let mut t = new_test_ext_with_candidate_holes();

		with_externalities(&mut t, || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), vec![0, 0, 1]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_eq!(Council::candidates(), vec![2, 0, 1]);

			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));
			assert_eq!(Council::candidates(), vec![2, 3, 1]);
		});
	}

	#[test]
	fn candidate_submission_not_using_free_slot_should_not_work() {
		with_externalities(&mut new_test_ext_with_candidate_holes(), || {
			System::set_block_number(1);
			assert_noop!(Council::submit_candidacy(Origin::signed(4), 3), "invalid candidate slot");
		});
	}

	#[test]
	fn bad_candidate_slot_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!(Council::submit_candidacy(Origin::signed(1), 1), "invalid candidate slot");
		});
	}

	#[test]
	fn non_free_candidate_slot_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!(Council::submit_candidacy(Origin::signed(2), 0), "invalid candidate slot");
		});
	}

	#[test]
	fn dupe_candidate_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!(Council::submit_candidacy(Origin::signed(1), 1), "duplicate candidate submission");
		});
	}

	#[test]
	fn poor_candidate_submission_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!(Council::submit_candidacy(Origin::signed(7), 0), "candidate has not enough funds");
		});
	}

	#[test]
	fn voting_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));

			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0));

			assert_eq!(Council::approvals_of(1), vec![true]);
			assert_eq!(Council::approvals_of(4), vec![true]);
			assert_eq!(Council::voters(), vec![1, 4]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));

			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true, true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, true], 0));

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

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0));

			assert_eq!(Council::approvals_of(4), vec![true]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true, false, true], 0));

			assert_eq!(Council::approvals_of(4), vec![true, false, true]);
		});
	}

	#[test]
	fn retracting_voter_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));

			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true, true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true, false, true], 0));

			assert_eq!(Council::voters(), vec![1, 2, 3, 4]);
			assert_eq!(Council::approvals_of(1), vec![true]);
			assert_eq!(Council::approvals_of(2), vec![false, true, true]);
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(1), 0));

			assert_eq!(Council::voters(), vec![4, 2, 3]);
			assert_eq!(Council::approvals_of(1), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(2), vec![false, true, true]);
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(2), 1));

			assert_eq!(Council::voters(), vec![4, 3]);
			assert_eq!(Council::approvals_of(1), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(2), Vec::<bool>::new());
			assert_eq!(Council::approvals_of(3), vec![false, true, true]);
			assert_eq!(Council::approvals_of(4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(3), 1));

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
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_eq!(Council::voters(), vec![1, 2]);
			assert_noop!(Council::retract_voter(Origin::signed(1), 1), "retraction index mismatch");
		});
	}

	#[test]
	fn overflow_retraction_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0));
			assert_noop!(Council::retract_voter(Origin::signed(1), 1), "retraction index invalid");
		});
	}

	#[test]
	fn non_voter_retraction_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(1);
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0));
			assert_noop!(Council::retract_voter(Origin::signed(2), 0), "cannot retract non-voter");
		});
	}

	#[test]
	fn simple_tally_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0));
			assert_eq!(Council::voters(), vec![2, 5]);
			assert_eq!(Council::approvals_of(2), vec![true, false]);
			assert_eq!(Council::approvals_of(5), vec![false, true]);
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (0, 0), (20, 2), (50, 5)]));

			assert_ok!(Council::end_block(System::block_number()));

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
			assert!(Balances::can_slash(&4, 10));

			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));
			assert_eq!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0), Err("duplicate presentation"));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);
			assert_eq!(Balances::total_balance(&4), 38);
		});
	}

	#[test]
	fn retracting_inactive_voter_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(5),
				Council::voters().iter().position(|&i| i == 5).unwrap() as u32,
				2.into(), Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			));

			assert_eq!(Council::voters(), vec![5]);
			assert_eq!(Council::approvals_of(2).len(), 0);
			assert_eq!(Balances::total_balance(&2), 17);
			assert_eq!(Balances::total_balance(&5), 53);
		});
	}

	#[test]
	fn presenting_for_double_election_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_eq!(Council::submit_candidacy(Origin::signed(2), 0), Ok(()));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_eq!(Council::submit_candidacy(Origin::signed(2), 0), Ok(()));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_noop!(Council::present_winner(Origin::signed(4), 2.into(), 20, 1), "candidate must not form a duplicated member if elected");
		});
	}

	#[test]
	fn retracting_inactive_voter_with_other_candidates_in_slots_should_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(11);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(5),
				Council::voters().iter().position(|&i| i == 5).unwrap() as u32,
				2.into(), Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			));

			assert_eq!(Council::voters(), vec![5]);
			assert_eq!(Council::approvals_of(2).len(), 0);
			assert_eq!(Balances::total_balance(&2), 17);
			assert_eq!(Balances::total_balance(&5), 53);
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_reporter_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(2),
				42,
				2.into(), Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			), "bad reporter index");
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_target_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(2),
				Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2.into(), 42,
				2
			), "bad target index");
		});
	}

	#[test]
	fn attempting_to_retract_active_voter_should_slash_reporter() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 2));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 3));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false, false, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, false, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::set_desired_seats(Origin::ROOT, 3));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 1));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(4),
				Council::voters().iter().position(|&i| i == 4).unwrap() as u32,
				2.into(), Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			));

			assert_eq!(Council::voters(), vec![2, 3, 5]);
			assert_eq!(Council::approvals_of(4).len(), 0);
			assert_eq!(Balances::total_balance(&4), 37);
		});
	}

	#[test]
	fn attempting_to_retract_inactive_voter_by_nonvoter_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(4),
				0,
				2.into(), Council::voters().iter().position(|&i| i == 2).unwrap() as u32,
				2
			), "reporter must be a voter");
		});
	}

	#[test]
	fn presenting_loser_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 1.into(), 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));
			assert_noop!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0), "candidate not worthy of leaderboard");
		});
	}

	#[test]
	fn presenting_loser_first_should_not_matter() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2.into(), 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 1.into(), 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));

			assert_eq!(Council::leaderboard(), Some(vec![
				(30, 3),
				(40, 4),
				(50, 5),
				(60, 1)
			]));
		});
	}

	#[test]
	fn present_outside_of_presentation_period_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_noop!(Council::present_winner(Origin::signed(5), 5.into(), 1, 0), "cannot present outside of presentation period");
		});
	}

	#[test]
	fn present_with_invalid_vote_index_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_noop!(Council::present_winner(Origin::signed(4), 2.into(), 20, 1), "index not current");
		});
	}

	#[test]
	fn present_when_presenter_is_poor_should_not_work() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_eq!(Balances::free_balance(&1), 1);
			assert_eq!(Balances::reserved_balance(&1), 9);
			assert_noop!(Council::present_winner(Origin::signed(1), 1.into(), 20, 0), "presenter must have sufficient slashable funds");
		});
	}

	#[test]
	fn invalid_present_tally_should_slash() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_eq!(Balances::total_balance(&4), 40);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_err!(Council::present_winner(Origin::signed(4), 2.into(), 80, 0), "incorrect total");

			assert_eq!(Balances::total_balance(&4), 38);
		});
	}

	#[test]
	fn runners_up_should_be_kept() {
		with_externalities(&mut new_test_ext(false), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0));

			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_ok!(Council::present_winner(Origin::signed(4), 1.into(), 60, 0));
			assert_eq!(Council::leaderboard(), Some(vec![
				(0, 0),
				(0, 0),
				(0, 0),
				(60, 1)
			]));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));
			assert_eq!(Council::leaderboard(), Some(vec![
				(30, 3),
				(40, 4),
				(50, 5),
				(60, 1)
			]));

			assert_ok!(Council::end_block(System::block_number()));

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
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 1.into(), 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5.into(), 50, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![false, false, true, false], 1));
			assert_ok!(Council::set_desired_seats(Origin::ROOT, 3));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 3.into(), 90, 1));
			assert_ok!(Council::present_winner(Origin::signed(4), 4.into(), 40, 1));
			assert_ok!(Council::end_block(System::block_number()));

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
