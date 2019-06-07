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

//! Council system: Handles the voting in and maintenance of council members.

use rstd::prelude::*;
use primitives::traits::{Zero, One, StaticLookup, Bounded, Saturating};
use runtime_io::print;
use srml_support::{
	StorageValue, StorageMap,
	dispatch::Result, decl_storage, decl_event, ensure, decl_module,
	traits::{
		Currency, ReservableCurrency, OnUnbalanced, LockIdentifier,
		LockableCurrency, WithdrawReasons, WithdrawReason, ExistenceRequirement
	}
};
use democracy;
use parity_codec::{Encode, Decode};
use system::{self, ensure_signed};
use super::OnMembersChanged;

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

// for an approval vote of C councillors:

// top K runners-up are maintained between votes. all others are discarded.
// - candidate removed & bond returned when elected.
// - candidate removed & bond burned when discarded.

// at the point that the vote ends (), all voters' balances are snapshotted.

// for B blocks following, there's a counting period whereby each of the candidates that believe
// they fall in the top K+C voted can present themselves. they get the total stake
// recorded (based on the snapshot); an ordered list is maintained (the leaderboard). Noone may
// present themselves that, if elected, would result in being included twice on the council
// (important since existing councillors will have their approval votes as it may be that they
// don't get removed), nor if existing presenters would mean they're not in the top K+C.

// following B blocks, the top C candidates are elected and have their bond returned. the top C
// candidates and all other candidates beyond the top C+K are cleared.

// vote-clearing happens lazily; for an approval to count, the most recent vote at the time of the
// voter's most recent vote must be no later than the most recent vote at the time that the
// candidate in the approval position was registered there. as candidates are removed from the
// register and others join in their place, this prevents an approval meant for an earlier candidate
// being used to elect a new candidate.

// the candidate list increases as needed, but the contents (though not really the capacity) reduce
// after each vote as all but K entries are cleared. newly registering candidates must use cleared
// entries before they increase the capacity.


/// The activity status of a voter.
#[derive(PartialEq, Eq, Copy, Clone, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct VoterInfo<Balance> {
	/// Last VoteIndex in which this voter assigned (or initialized) approvals.
	last_active: VoteIndex,
	/// Last VoteIndex in which one of this voter's approvals won.
	/// Note that `last_win = N` indicates a last win at index `N-1`, hence `last_win = 0` means no win ever.
	last_win: VoteIndex,
	/// The amount of stored weight as a result of not winning but changing approvals.
	pot: Balance,
	/// Current staked amount. A lock equal to this value always exists.
	stake: Balance,
}

/// Used to demonstrate the status of a particular index in the global voter list.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum CellStatus {
	/// Any out of bound index. Means a push a must happen to the chunk pointed by `NextVoterSet<T>`.
	/// Voting fee is applied in case a new chunk is created.
	Head,
	/// Already occupied by another voter. Voting fee is applied.
	Occupied,
	/// Empty hole which should be filled. No fee will be applied.
	Hole,
}

const COUNCIL_SEATS_ID: LockIdentifier = *b"councils";

pub const VOTER_SET_SIZE: usize = 64;
pub const APPROVAL_SET_SIZE: usize = 8;

type BalanceOf<T> = <<T as democracy::Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as democracy::Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

type SetIndex = u32;
pub type VoteIndex = u32;

// all three must be in sync.
type ApprovalFlag = u32;
pub const APPROVAL_FLAG_MASK: ApprovalFlag = 0x8000_0000;
pub const APPROVAL_FLAG_LEN: usize = 32;

pub trait Trait: democracy::Trait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Handler for the unbalanced reduction when slashing a validator.
	type BadPresentation: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when slashing an invalid reaping attempt.
	type BadReaper: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when submitting a bad `voter_index`.
	type BadVoterIndex: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when a candidate has lost (and is not a runner up)
	type LoserCandidate: OnUnbalanced<NegativeImbalanceOf<Self>>;
	/// What to do when the members change.
	type OnMembersChanged: OnMembersChanged<Self::AccountId>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Set candidate approvals. Approval slots stay valid as long as candidates in those slots
		/// are registered.
		///
		/// Locks the total balance of caller indefinitely.
		/// Only [`retract_voter`] or [`reap_inactive_voter`] can unlock the balance.
		///
		/// `hint` argument is interpreted differently based on:
		/// - if `origin` is setting approvals for the first time: The index will be checked
		/// for being a valid _hole_ in the voter list.
		///   - if the hint is correctly pointing to a hole, no fee is deducted from `origin`.
		///   - Otherwise, the call will succeed but the index is ignored and simply a push to the last chunk
		///   with free space happens. If the new push causes a new chunk to be created, a fee indicated by
		///   [`VotingFee`] is deducted.
		/// - if `origin` is already a voter: the index __must__ be valid and point to the correct
		/// position of the `origin` in the current voters list.
		///
		/// Note that any trailing `false` votes in `votes` is ignored; In approval voting, not voting for a candidate
		/// and voting false, are equal.
		fn set_approvals(origin, votes: Vec<bool>, #[compact] index: VoteIndex, hint: SetIndex) -> Result {
			let who = ensure_signed(origin)?;
			Self::do_set_approvals(who, votes, index, hint)
		}

		/// Set candidate approvals from a proxy. Approval slots stay valid as long as candidates in those slots
		/// are registered.
		fn proxy_set_approvals(origin, votes: Vec<bool>, #[compact] index: VoteIndex, hint: SetIndex) -> Result {
			let who = <democracy::Module<T>>::proxy(ensure_signed(origin)?).ok_or("not a proxy")?;
			Self::do_set_approvals(who, votes, index, hint)
		}

		/// Remove a voter. For it not to be a bond-consuming no-op, all approved candidate indices
		/// must now be either unregistered or registered to a candidate that registered the slot after
		/// the voter gave their last approval set.
		///
		/// Both indices must be provided as explained in [`voter_at`] function.
		///
		/// May be called by anyone. Returns the voter deposit to `signed`.
		fn reap_inactive_voter(
			origin,
			#[compact] reporter_index: u32,
			who: <T::Lookup as StaticLookup>::Source,
			#[compact] who_index: u32,
			#[compact] assumed_vote_index: VoteIndex
		) {
			let reporter = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			ensure!(!Self::presentation_active(), "cannot reap during presentation period");
			ensure!(Self::voter_info(&reporter).is_some(), "reporter must be a voter");

			let info = Self::voter_info(&who).ok_or("target for inactivity cleanup must be active")?;
			let last_active = info.last_active;

			ensure!(assumed_vote_index == Self::vote_index(), "vote index not current");
			ensure!(
				assumed_vote_index > last_active+ Self::inactivity_grace_period(),
				"cannot reap during grace period"
			);

			let reporter_index = reporter_index as usize;
			let who_index = who_index as usize;
			let assumed_reporter = Self::voter_at(reporter_index).ok_or("invalid reporter index")?;
			let assumed_who = Self::voter_at(who_index).ok_or("invalid target index")?;

			ensure!(assumed_reporter == reporter, "bad reporter index");
			ensure!(assumed_who == who, "bad target index");

			// will definitely kill one of reporter or who now.

			let valid = !Self::all_approvals_of(&who).iter()
				.zip(Self::candidates().iter())
				.any(|(&appr, addr)|
					 appr &&
					 *addr != T::AccountId::default() &&
					 // defensive only: all items in candidates list are registered
					 Self::candidate_reg_info(addr).map_or(false, |x| x.0 <= last_active)
				);

			Self::remove_voter(
				if valid { &who } else { &reporter },
				if valid { who_index } else { reporter_index }
			);

			T::Currency::remove_lock(
				COUNCIL_SEATS_ID,
				if valid { &who } else { &reporter }
			);

			if valid {
				// This only fails if `reporter` doesn't exist, which it clearly must do since its the origin.
				// Still, it's no more harmful to propagate any error at this point.
				T::Currency::repatriate_reserved(&who, &reporter, Self::voting_bond())?;
				Self::deposit_event(RawEvent::VoterReaped(who, reporter));
			} else {
				let imbalance = T::Currency::slash_reserved(&reporter, Self::voting_bond()).0;
				T::BadReaper::on_unbalanced(imbalance);
				Self::deposit_event(RawEvent::BadReaperSlashed(reporter));
			}
		}

		/// Remove a voter. All votes are cancelled and the voter deposit is returned.
		///
		/// The index must be provided as explained in [`voter_at`] function.
		///
		/// Also removes the lock on the balance of the voter. See [`do_set_approvals()`].
		fn retract_voter(origin, #[compact] index: u32) {
			let who = ensure_signed(origin)?;

			ensure!(!Self::presentation_active(), "cannot retract when presenting");
			ensure!(<VoterInfoOf<T>>::exists(&who), "cannot retract non-voter");
			let index = index as usize;
			let voter = Self::voter_at(index).ok_or("retraction index invalid")?;
			ensure!(voter == who, "retraction index mismatch");

			Self::remove_voter(&who, index);
			T::Currency::unreserve(&who, Self::voting_bond());
			T::Currency::remove_lock(COUNCIL_SEATS_ID, &who);
		}

		/// Submit oneself for candidacy.
		///
		/// Account must have enough transferrable funds in it to pay the bond.
		///
		/// NOTE: if `origin` has already assigned approvals via [`set_approvals`],
		/// it will NOT have any usable funds to pass candidacy bond and must first retract.
		/// Note that setting approvals will lock the entire balance of the voter until
		/// retraction or being reported.
		fn submit_candidacy(origin, #[compact] slot: u32) {
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
			T::Currency::reserve(&who, Self::candidacy_bond())
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
		}

		/// Claim that `signed` is one of the top Self::carry_count() + current_vote().1 candidates.
		/// Only works if the `block_number >= current_vote().0` and `< current_vote().0 + presentation_duration()`
		/// `signed` should have at least
		fn present_winner(
			origin,
			candidate: <T::Lookup as StaticLookup>::Source,
			#[compact] total: BalanceOf<T>,
			#[compact] index: VoteIndex
		) -> Result {
			let who = ensure_signed(origin)?;
			ensure!(
				!total.is_zero(),
				"stake deposited to present winner and be added to leaderboard should be non-zero"
			);

			let candidate = T::Lookup::lookup(candidate)?;
			ensure!(index == Self::vote_index(), "index not current");
			let (_, _, expiring) = Self::next_finalize().ok_or("cannot present outside of presentation period")?;
			let bad_presentation_punishment =
				Self::present_slash_per_voter()
				* BalanceOf::<T>::from(Self::voter_count() as u32);
			ensure!(
				T::Currency::can_slash(&who, bad_presentation_punishment),
				"presenter must have sufficient slashable funds"
			);

			let mut leaderboard = Self::leaderboard().ok_or("leaderboard must exist while present phase active")?;
			ensure!(total > leaderboard[0].0, "candidate not worthy of leaderboard");

			if let Some(p) = Self::active_council().iter().position(|&(ref c, _)| c == &candidate) {
				ensure!(p < expiring.len(), "candidate must not form a duplicated member if elected");
			}

			let voters = Self::all_voters();
			let (registered_since, candidate_index): (VoteIndex, u32) =
				Self::candidate_reg_info(&candidate).ok_or("presented candidate must be current")?;
			let actual_total = voters.iter()
				.filter_map(|maybe_voter| maybe_voter.as_ref())
				.filter_map(|voter| match Self::voter_info(voter) {
					Some(b) if b.last_active >= registered_since => {
						let last_win = b.last_win;
						let now = Self::vote_index();
						let stake = b.stake;
						let offset = Self::get_offset(stake, now - last_win);
						let weight = stake + offset + b.pot;
						if Self::approvals_of_at(voter, candidate_index as usize) {
							Some(weight)
						} else { None }
					},
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
				let imbalance = T::Currency::slash(&who, bad_presentation_punishment).0;
				T::BadPresentation::on_unbalanced(imbalance);
				Err(if dupe { "duplicate presentation" } else { "incorrect total" })
			}
		}

		/// Set the desired member count; if lower than the current count, then seats will not be up
		/// election when they expire. If more, then a new vote will be started if one is not
		/// already in progress.
		fn set_desired_seats(#[compact] count: u32) {
			<DesiredSeats<T>>::put(count);
		}

		/// Remove a particular member from the council. This is effective immediately.
		///
		/// Note: A tally should happen instantly (if not already in a presentation
		/// period) to fill the seat if removal means that the desired members are not met.
		fn remove_member(who: <T::Lookup as StaticLookup>::Source) {
			let who = T::Lookup::lookup(who)?;
			let new_council: Vec<(T::AccountId, T::BlockNumber)> = Self::active_council()
				.into_iter()
				.filter(|i| i.0 != who)
				.collect();
			<ActiveCouncil<T>>::put(new_council);
			T::OnMembersChanged::on_members_changed(&[], &[who]);
		}

		/// Set the presentation duration. If there is currently a vote being presented for, will
		/// invoke `finalize_vote`.
		fn set_presentation_duration(#[compact] count: T::BlockNumber) {
			<PresentationDuration<T>>::put(count);
		}

		/// Set the presentation duration. If there is current a vote being presented for, will
		/// invoke `finalize_vote`.
		fn set_term_duration(#[compact] count: T::BlockNumber) {
			<TermDuration<T>>::put(count);
		}

		fn on_initialize(n: T::BlockNumber) {
			if let Err(e) = Self::end_block(n) {
				print("Guru meditation");
				print(e);
			}
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Council {

		// ---- parameters
		/// How much should be locked up in order to submit one's candidacy.
		pub CandidacyBond get(candidacy_bond) config(): BalanceOf<T> = 9.into();
		/// How much should be locked up in order to be able to submit votes.
		pub VotingBond get(voting_bond) config(voter_bond): BalanceOf<T>;
		/// The amount of fee paid upon each vote submission, unless if they submit a _hole_ index and replace it.
		pub VotingFee get(voting_fee) config(voting_fee): BalanceOf<T>;
		/// The punishment, per voter, if you provide an invalid presentation.
		pub PresentSlashPerVoter get(present_slash_per_voter) config(): BalanceOf<T> = 1.into();
		/// How many runners-up should have their approvals persist until the next vote.
		pub CarryCount get(carry_count) config(): u32 = 2;
		/// How long to give each top candidate to present themselves after the vote ends.
		pub PresentationDuration get(presentation_duration) config(): T::BlockNumber = 1000.into();
		/// How many vote indices need to go by after a target voter's last vote before they can be reaped if their
		/// approvals are moot.
		pub InactiveGracePeriod get(inactivity_grace_period) config(inactive_grace_period): VoteIndex = 1;
		/// How often (in blocks) to check for new votes.
		pub VotingPeriod get(voting_period) config(approval_voting_period): T::BlockNumber = 1000.into();
		/// How long each position is active for.
		pub TermDuration get(term_duration) config(): T::BlockNumber = 5.into();
		/// Number of accounts that should be sitting on the council.
		pub DesiredSeats get(desired_seats) config(): u32;
		/// Decay factor of weight when being accumulated. It should typically be set to
		/// __at least__ `council_size -1` to keep the council secure.
		/// When set to `N`, it indicates `(1/N)^t` of staked is decayed at weight increment step `t`.
		/// 0 will result in no weight being added at all (normal approval voting).
		pub DecayRatio get(decay_ratio) config(decay_ratio): u32 = 24;

		// ---- permanent state (always relevant, changes only at the finalization of voting)
		/// The current council. When there's a vote going on, this should still be used for executive
		/// matters. The block number (second element in the tuple) is the block that their position is
		/// active until (calculated by the sum of the block number when the council member was elected
		/// and their term duration).
		pub ActiveCouncil get(active_council) config(): Vec<(T::AccountId, T::BlockNumber)>;
		/// The total number of vote rounds that have happened or are in progress.
		pub VoteCount get(vote_index): VoteIndex;

		// ---- persistent state (always relevant, changes constantly)
		/// A list of votes for each voter. The votes are stored as numeric values and parsed in a bit-wise manner.
		///
		/// In order to get a human-readable representation (`Vec<bool>`), use [`all_approvals_of`].
		///
		/// Furthermore, each vector of scalars is chunked with the cap of `APPROVAL_SET_SIZE`.
		pub ApprovalsOf get(approvals_of): map (T::AccountId, SetIndex) => Vec<ApprovalFlag>;
		/// The vote index and list slot that the candidate `who` was registered or `None` if they are not
		/// currently registered.
		pub RegisterInfoOf get(candidate_reg_info): map T::AccountId => Option<(VoteIndex, u32)>;
		/// Basic information about a voter.
		pub VoterInfoOf get(voter_info): map T::AccountId => Option<VoterInfo<BalanceOf<T>>>;
		/// The present voter list (chunked and capped at [`VOTER_SET_SIZE`]).
		pub Voters get(voters): map SetIndex => Vec<Option<T::AccountId>>;
		/// the next free set to store a voter in. This will keep growing.
		pub NextVoterSet get(next_nonfull_voter_set): SetIndex = 0;
		/// Current number of Voters.
		pub VoterCount get(voter_count): SetIndex = 0;
		/// The present candidate list.
		pub Candidates get(candidates): Vec<T::AccountId>; // has holes
		/// Current number of active candidates
		pub CandidateCount get(candidate_count): u32;

		// ---- temporary state (only relevant during finalization/presentation)
		/// The accounts holding the seats that will become free on the next tally.
		pub NextFinalize get(next_finalize): Option<(T::BlockNumber, u32, Vec<T::AccountId>)>;
		/// Get the leaderboard if we're in the presentation phase. The first element is the weight of each entry;
		/// It may be the direct summed approval stakes, or a weighted version of it.
		pub Leaderboard get(leaderboard): Option<Vec<(BalanceOf<T>, T::AccountId)> >; // ORDERED low -> high
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::AccountId {
		/// reaped voter, reaper
		VoterReaped(AccountId, AccountId),
		/// slashed reaper
		BadReaperSlashed(AccountId),
		/// A tally (for approval votes of council seat(s)) has started.
		TallyStarted(u32),
		/// A tally (for approval votes of council seat(s)) has ended (with one or more new members).
		TallyFinalized(Vec<AccountId>, Vec<AccountId>),
	}
);

impl<T: Trait> Module<T> {
	// exposed immutables.

	/// True if we're currently in a presentation period.
	pub fn presentation_active() -> bool {
		<NextFinalize<T>>::exists()
	}

	/// If `who` a candidate at the moment?
	pub fn is_a_candidate(who: &T::AccountId) -> bool {
		<RegisterInfoOf<T>>::exists(who)
	}

	/// Iff the councillor `who` still has a seat at blocknumber `n` returns `true`.
	pub fn will_still_be_councillor_at(who: &T::AccountId, n: T::BlockNumber) -> bool {
		Self::active_council().iter()
			.find(|&&(ref a, _)| a == who)
			.map(|&(_, expires)| expires > n)
			.unwrap_or(false)
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
				if let Some((tally_end, comers, leavers)) = Self::next_finalize() {
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

	// Private
	/// Check there's nothing to do this block
	fn end_block(block_number: T::BlockNumber) -> Result {
		if (block_number % Self::voting_period()).is_zero() {
			if let Some(number) = Self::next_tally() {
				if block_number == number {
					Self::start_tally();
				}
			}
		}
		if let Some((number, _, _)) = Self::next_finalize() {
			if block_number == number {
				Self::finalize_tally()?
			}
		}
		Ok(())
	}

	/// Remove a voter at a specified index from the system.
	fn remove_voter(voter: &T::AccountId, index: usize) {
		let (set_index, vec_index) = Self::split_index(index, VOTER_SET_SIZE);
		let mut set = Self::voters(set_index);
		set[vec_index] = None;
		<Voters<T>>::insert(set_index, set);
		<VoterCount<T>>::mutate(|c| *c = *c - 1);
		Self::remove_all_approvals_of(voter);
		<VoterInfoOf<T>>::remove(voter);
	}

	/// Actually do the voting.
	///
	/// The voter index must be provided as explained in [`voter_at`] function.
	fn do_set_approvals(who: T::AccountId, votes: Vec<bool>, index: VoteIndex, hint: SetIndex) -> Result {
		let candidates = Self::candidates();

		ensure!(!Self::presentation_active(), "no approval changes during presentation period");
		ensure!(index == Self::vote_index(), "incorrect vote index");
		ensure!(!candidates.is_empty(), "amount of candidates to receive approval votes should be non-zero");
		// Prevent a vote from voters that provide a list of votes that exceeds the candidates length
		// since otherwise an attacker may be able to submit a very long list of `votes` that far exceeds
		// the amount of candidates and waste more computation than a reasonable voting bond would cover.
		ensure!(candidates.len() >= votes.len(), "amount of candidate votes cannot exceed amount of candidates");

		// Amount to be locked up.
		let mut locked_balance = T::Currency::total_balance(&who);
		let mut pot_to_set = Zero::zero();
		let hint = hint as usize;

		if let Some(info) = Self::voter_info(&who) {
			// already a voter. Index must be valid. No fee. update pot. O(1)
			let voter = Self::voter_at(hint).ok_or("invalid voter index")?;
			ensure!(voter == who, "wrong voter index");

			// write new accumulated offset.
			let last_win = info.last_win;
			let now = index;
			let offset = Self::get_offset(info.stake, now - last_win);
			pot_to_set = info.pot + offset;
		} else {
			// not yet a voter. Index _could be valid_. Fee might apply. Bond will be reserved O(1).
			ensure!(
				T::Currency::free_balance(&who) > Self::voting_bond(),
				"new voter must have sufficient funds to pay the bond"
			);

			let (set_index, vec_index) = Self::split_index(hint, VOTER_SET_SIZE);
			match Self::cell_status(set_index, vec_index) {
				CellStatus::Hole => {
					// requested cell was a valid hole.
					<Voters<T>>::mutate(set_index, |set| set[vec_index] = Some(who.clone()));
				},
				CellStatus::Head | CellStatus::Occupied => {
					// Either occupied or out-of-range.
					let next = Self::next_nonfull_voter_set();
					let mut set = Self::voters(next);
					// Caused a new set to be created. Pay for it.
					// This is the last potential error. Writes will begin afterwards.
					if set.is_empty() {
						let imbalance = T::Currency::withdraw(
							&who,
							Self::voting_fee(),
							WithdrawReason::Fee,
							ExistenceRequirement::KeepAlive,
						)?;
						T::BadVoterIndex::on_unbalanced(imbalance);
						// NOTE: this is safe since the `withdraw()` will check this.
						locked_balance -= Self::voting_fee();
					}
					Self::checked_push_voter(&mut set, who.clone(), next);
					<Voters<T>>::insert(next, set);
				}
			}

			T::Currency::reserve(&who, Self::voting_bond())?;
			<VoterCount<T>>::mutate(|c| *c = *c + 1);
		}

		T::Currency::set_lock(
			COUNCIL_SEATS_ID,
			&who,
			locked_balance,
			T::BlockNumber::max_value(),
			WithdrawReasons::all()
		);

		<VoterInfoOf<T>>::insert(
			&who,
			VoterInfo::<BalanceOf<T>> {
				last_active: index,
				last_win: index,
				stake: locked_balance,
				pot: pot_to_set,
			}
		);
		Self::set_approvals_chunked(&who, votes);

		Ok(())
	}

	/// Close the voting, record the number of seats that are actually up for grabs.
	fn start_tally() {
		let active_council = Self::active_council();
		let desired_seats = Self::desired_seats() as usize;
		let number = <system::Module<T>>::block_number();
		let expiring = active_council.iter().take_while(|i| i.1 <= number).map(|i| i.0.clone()).collect::<Vec<_>>();
		let retaining_seats = active_council.len() - expiring.len();
		if retaining_seats < desired_seats {
			let empty_seats = desired_seats - retaining_seats;
			<NextFinalize<T>>::put((number + Self::presentation_duration(), empty_seats as u32, expiring));

			// initialize leaderboard.
			let leaderboard_size = empty_seats + Self::carry_count() as usize;
			<Leaderboard<T>>::put(vec![(Zero::zero(), T::AccountId::default()); leaderboard_size]);

			Self::deposit_event(RawEvent::TallyStarted(empty_seats as u32));
		}
	}

	/// Finalize the vote, removing each of the `removals` and inserting `seats` of the most approved
	/// candidates in their place. If the total council members is less than the desired membership
	/// a new vote is started.
	/// Clears all presented candidates, returning the bond of the elected ones.
	fn finalize_tally() -> Result {
		let (_, coming, expiring): (T::BlockNumber, u32, Vec<T::AccountId>) =
			<NextFinalize<T>>::take().ok_or("finalize can only be called after a tally is started.")?;
		let leaderboard: Vec<(BalanceOf<T>, T::AccountId)> = <Leaderboard<T>>::take().unwrap_or_default();
		let new_expiry = <system::Module<T>>::block_number() + Self::term_duration();

		// return bond to winners.
		let candidacy_bond = Self::candidacy_bond();
		let incoming: Vec<_> = leaderboard.iter()
			.rev()
			.take_while(|&&(b, _)| !b.is_zero())
			.take(coming as usize)
			.map(|(_, a)| a)
			.cloned()
			.inspect(|a| { T::Currency::unreserve(a, candidacy_bond); })
			.collect();

		// Update last win index for anyone voted for any of the incomings.
		incoming.iter().filter_map(|i| Self::candidate_reg_info(i)).for_each(|r| {
			let index = r.1 as usize;
			Self::all_voters()
				.iter()
				.filter_map(|mv| mv.as_ref())
				.filter(|v| Self::approvals_of_at(*v, index))
				.for_each(|v| <VoterInfoOf<T>>::mutate(v, |a| {
					if let Some(activity) = a { activity.last_win = Self::vote_index() + 1; }
				}));
		});
		let active_council = Self::active_council();
		let outgoing: Vec<_> = active_council.iter()
			.take(expiring.len())
			.map(|a| a.0.clone()).collect();

		// set the new council.
		let mut new_council: Vec<_> = active_council
			.into_iter()
			.skip(expiring.len())
			.chain(incoming.iter().cloned().map(|a| (a, new_expiry)))
			.collect();
		new_council.sort_by_key(|&(_, expiry)| expiry);
		<ActiveCouncil<T>>::put(new_council);

		T::OnMembersChanged::on_members_changed(&incoming, &outgoing);

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

		Self::deposit_event(RawEvent::TallyFinalized(incoming, outgoing));

		<Candidates<T>>::put(new_candidates);
		<CandidateCount<T>>::put(count);
		<VoteCount<T>>::put(Self::vote_index() + 1);
		Ok(())
	}

	fn checked_push_voter(set: &mut Vec<Option<T::AccountId>>, who: T::AccountId, index: u32) {
		let len = set.len();

		// Defensive only: this should never happen. Don't push since it will break more things.
		if len == VOTER_SET_SIZE { return; }

		set.push(Some(who));
		if len + 1 == VOTER_SET_SIZE {
			<NextVoterSet<T>>::put(index + 1);
		}
	}

	/// Get the set and vector index of a global voter index.
	///
	/// Note that this function does not take holes into account.
	/// See [`voter_at`].
	fn split_index(index: usize, scale: usize) -> (SetIndex, usize) {
		let set_index = (index / scale) as u32;
		let vec_index = index % scale;
		(set_index, vec_index)
	}

	/// Return a concatenated vector over all voter sets.
	fn all_voters() -> Vec<Option<T::AccountId>> {
		let mut all = <Voters<T>>::get(0);
		let mut index = 1;
		// NOTE: we could also use `Self::next_nonfull_voter_set()` here but that might change based
		// on how we do chunking. This is more generic.
		loop {
			let next_set = <Voters<T>>::get(index);
			if next_set.is_empty() {
				break;
			} else {
				index += 1;
				all.extend(next_set);
			}
		}
		all
	}

	/// Shorthand for fetching a voter at a specific (global) index.
	///
	/// NOTE: this function is used for checking indices. Yet, it does not take holes into account.
	/// This means that any account submitting an index at any point in time should submit:
	/// `VOTER_SET_SIZE * set_index + local_index`, meaning that you are ignoring all holes in the
	/// first `set_index` sets.
	fn voter_at(index: usize) -> Option<T::AccountId> {
		let (set_index, vec_index) = Self::split_index(index, VOTER_SET_SIZE);
		let set = Self::voters(set_index);
		if vec_index < set.len() {
			set[vec_index].clone()
		} else {
			None
		}
	}

	/// A more sophisticated version of `voter_at`. Will be kept separate as most often it is an overdue
	/// compared to `voter_at`. Only used when setting approvals.
	fn cell_status(set_index: SetIndex, vec_index: usize) -> CellStatus {
		let set = Self::voters(set_index);
		if vec_index < set.len() {
			if let Some(_) = set[vec_index] {
				CellStatus::Occupied
			} else {
				CellStatus::Hole
			}
		} else {
			CellStatus::Head
		}
	}

	/// Sets the approval of a voter in a chunked manner.
	fn set_approvals_chunked(who: &T::AccountId, approvals: Vec<bool>) {
		let approvals_flag_vec = Self::bool_to_flag(approvals);
		approvals_flag_vec
			.chunks(APPROVAL_SET_SIZE)
			.enumerate()
			.for_each(|(index, slice)| <ApprovalsOf<T>>::insert((who.clone(), index as SetIndex), slice.to_vec()));
	}

	/// shorthand for fetching a specific approval of a voter at a specific (global) index.
	///
	/// Using this function to read a vote is preferred as it reads `APPROVAL_SET_SIZE` items of type
	/// `ApprovalFlag` from storage at most; not all of them.
	///
	/// Note that false is returned in case of no-vote or an explicit `false`.
	fn approvals_of_at(who: &T::AccountId, index: usize) -> bool {
		let (flag_index, bit) = Self::split_index(index, APPROVAL_FLAG_LEN);
		let (set_index, vec_index) = Self::split_index(flag_index as usize, APPROVAL_SET_SIZE);
		let set = Self::approvals_of((who.clone(), set_index));
		if vec_index < set.len() {
			// This is because bit_at treats numbers in lsb -> msb order.
			let reversed_index = set.len() - 1 - vec_index;
			Self::bit_at(set[reversed_index], bit)
		} else {
			false
		}
	}

	/// Return true of the bit `n` of scalar `x` is set to `1` and false otherwise.
	fn bit_at(x: ApprovalFlag, n: usize) -> bool {
		if n < APPROVAL_FLAG_LEN {
			// x & ( APPROVAL_FLAG_MASK >> n ) != 0
			x & ( 1 << n ) != 0
		} else {
			false
		}
	}

	/// Convert a vec of boolean approval flags to a vec of integers, as denoted by
	/// the type `ApprovalFlag`. see `bool_to_flag_should_work` test for examples.
	pub fn bool_to_flag(x: Vec<bool>) -> Vec<ApprovalFlag> {
		let mut result: Vec<ApprovalFlag> = Vec::with_capacity(x.len() / APPROVAL_FLAG_LEN);
		if x.is_empty() {
			return result;
		}
		result.push(0);
		let mut index = 0;
		let mut counter = 0;
		loop {
			let shl_index = counter % APPROVAL_FLAG_LEN;
			result[index] += (if x[counter] { 1 } else { 0 }) << shl_index;
			counter += 1;
			if counter > x.len() - 1 { break; }
			if counter % APPROVAL_FLAG_LEN == 0 {
				result.push(0);
				index += 1;
			}
		}
		result
	}

	/// Convert a vec of flags (u32) to boolean.
	pub fn flag_to_bool(chunk: Vec<ApprovalFlag>) -> Vec<bool> {
		let mut result = Vec::with_capacity(chunk.len());
		if chunk.is_empty() { return vec![] }
		chunk.into_iter()
			.map(|num| (0..APPROVAL_FLAG_LEN).map(|bit| Self::bit_at(num, bit)).collect::<Vec<bool>>())
			.for_each(|c| {
				let last_approve = match c.iter().rposition(|n| *n) {
					Some(index) => index + 1,
					None => 0
				};
				result.extend(c.into_iter().take(last_approve));
			});
		result
	}

	/// Return a concatenated vector over all approvals of a voter as boolean.
	/// The trailing zeros are removed.
	fn all_approvals_of(who: &T::AccountId) -> Vec<bool> {
		let mut all: Vec<bool> = vec![];
		let mut index = 0_u32;
		loop {
			let chunk = Self::approvals_of((who.clone(), index));
			if chunk.is_empty() { break; }
			all.extend(Self::flag_to_bool(chunk));
			index += 1;
		}
		all
	}

	/// Remove all approvals associated with one account.
	fn remove_all_approvals_of(who: &T::AccountId) {
		let mut index = 0;
		loop {
			let set = Self::approvals_of((who.clone(), index));
			if set.len() > 0 {
				<ApprovalsOf<T>>::remove((who.clone(), index));
				index += 1;
			} else {
				break
			}
		}
	}

	/// Calculates the offset value (stored pot) of a stake, based on the distance
	/// to the last win_index, `t`. Regardless of the internal implementation,
	/// it should always be used with the following structure:
	///
	/// Given Stake of voter `V` being `x` and distance to last_win index `t`, the new weight
	/// of `V` is `x + get_offset(x, t)`.
	///
	/// In other words, this function returns everything extra that should be added
	/// to a voter's stake value to get the correct weight. Indeed, zero is
	/// returned if `t` is zero.
	fn get_offset(stake: BalanceOf<T>, t: VoteIndex) -> BalanceOf<T> {
		let decay_ratio: BalanceOf<T> = Self::decay_ratio().into();
		if t > 150 { return stake * decay_ratio }
		let mut offset = stake;
		let mut r = Zero::zero();
		let decay = decay_ratio + One::one();
		for _ in 0..t {
			offset = offset.saturating_sub(offset / decay);
			r += offset
		}
		r
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::*;
	use srml_support::{assert_ok, assert_noop, assert_err};

	fn voter_ids() -> Vec<u64> {
		Council::all_voters().iter().map(|v| v.unwrap_or(0) ).collect::<Vec<u64>>()
	}

	fn vote(i: u64, l: usize) {
		let _ = Balances::make_free_balance_be(&i, 20);
		assert_ok!(Council::set_approvals(Origin::signed(i), (0..l).map(|_| true).collect::<Vec<bool>>(), 0, 0));
	}

	fn vote_at(i: u64, l: usize, index: VoteIndex) {
		let _ = Balances::make_free_balance_be(&i, 20);
		assert_ok!(Council::set_approvals(Origin::signed(i), (0..l).map(|_| true).collect::<Vec<bool>>(), 0, index));
	}

	fn create_candidate(i: u64, index: u32) {
		let _ = Balances::make_free_balance_be(&i, 20);
		assert_ok!(Council::submit_candidacy(Origin::signed(i), index));
	}

	fn bond() -> u64 {
		Council::voting_bond()
	}


	#[test]
	fn bool_to_flag_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Council::bool_to_flag(vec![]), vec![]);
			assert_eq!(Council::bool_to_flag(vec![false]), vec![0]);
			assert_eq!(Council::bool_to_flag(vec![true]), vec![1]);
			assert_eq!(Council::bool_to_flag(vec![true, true, true, true]), vec![15]);
			assert_eq!(Council::bool_to_flag(vec![true, true, true, true, true]), vec![15 + 16]);

			let set_1 = vec![
					true, false, false, false, // 0x1
					false, true, true, true, // 0xE
			];
			assert_eq!(
				Council::bool_to_flag(set_1.clone()),
				vec![0x00_00_00_E1_u32]
			);
			assert_eq!(
				Council::flag_to_bool(vec![0x00_00_00_E1_u32]),
				set_1
			);

			let set_2 = vec![
					false, false, false, true, // 0x8
					false, true, false, true, // 0xA
			];
			assert_eq!(
				Council::bool_to_flag(set_2.clone()),
				vec![0x00_00_00_A8_u32]
			);
			assert_eq!(
				Council::flag_to_bool(vec![0x00_00_00_A8_u32]),
				set_2
			);

			let mut rhs = (0..100/APPROVAL_FLAG_LEN).map(|_| 0xFFFFFFFF_u32).collect::<Vec<u32>>();
			// NOTE: this might be need change based on `APPROVAL_FLAG_LEN`.
			rhs.extend(vec![0x00_00_00_0F]);
			assert_eq!(
				Council::bool_to_flag((0..100).map(|_| true).collect()),
				rhs
			)
		})
	}

	#[test]
	fn params_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::next_vote_from(1), 4);
			assert_eq!(Council::next_vote_from(4), 4);
			assert_eq!(Council::next_vote_from(5), 8);
			assert_eq!(Council::vote_index(), 0);
			assert_eq!(Council::candidacy_bond(), 3);
			assert_eq!(Council::voting_bond(), 0);
			assert_eq!(Council::voting_fee(), 0);
			assert_eq!(Council::present_slash_per_voter(), 1);
			assert_eq!(Council::presentation_duration(), 2);
			assert_eq!(Council::inactivity_grace_period(), 1);
			assert_eq!(Council::voting_period(), 4);
			assert_eq!(Council::term_duration(), 5);
			assert_eq!(Council::desired_seats(), 2);
			assert_eq!(Council::carry_count(), 2);

			assert_eq!(Council::active_council(), vec![]);
			assert_eq!(Council::next_tally(), Some(4));
			assert_eq!(Council::presentation_active(), false);
			assert_eq!(Council::next_finalize(), None);

			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_eq!(Council::is_a_candidate(&1), false);
			assert_eq!(Council::candidate_reg_info(1), None);

			assert_eq!(Council::voters(0), Vec::<Option<u64>>::new());
			assert_eq!(Council::voter_info(1), None);
			assert_eq!(Council::all_approvals_of(&1), vec![]);
		});
	}

	#[test]
	fn voter_set_growth_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			// create 65. 64 (set0) + 1 (set1)
			(1..=63).for_each(|i| vote(i, 2));
			assert_eq!(Council::next_nonfull_voter_set(), 0);
			vote(64, 2);
			assert_eq!(Council::next_nonfull_voter_set(), 1);
			vote(65, 2);

			let set1 = Council::voters(0);
			let set2 = Council::voters(1);

			assert_eq!(set1.len(), 64);
			assert_eq!(set2.len(), 1);

			assert_eq!(set1[0], Some(1));
			assert_eq!(set1[10], Some(11));
			assert_eq!(set2[0], Some(65));
		})
	}

	#[test]
	fn voter_set_reclaim_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			(1..=129).for_each(|i| vote(i, 2));
			assert_eq!(Council::next_nonfull_voter_set(), 2);

			assert_ok!(Council::retract_voter(Origin::signed(11), 10));

			assert_ok!(Council::retract_voter(Origin::signed(66), 65));
			assert_ok!(Council::retract_voter(Origin::signed(67), 66));

			// length does not show it but holes do exist.
			assert_eq!(Council::voters(0).len(), 64);
			assert_eq!(Council::voters(1).len(), 64);
			assert_eq!(Council::voters(2).len(), 1);

			assert_eq!(Council::voters(0)[10], None);
			assert_eq!(Council::voters(1)[1], None);
			assert_eq!(Council::voters(1)[2], None);
			// Next set with capacity is 2.
			assert_eq!(Council::next_nonfull_voter_set(), 2);

			// But we can fill a hole.
			vote_at(130, 2, 10);

			// Nothing added to set 2. A hole was filled.
			assert_eq!(Council::voters(0).len(), 64);
			assert_eq!(Council::voters(1).len(), 64);
			assert_eq!(Council::voters(2).len(), 1);

			// and the next two (scheduled) to the second set.
			assert_eq!(Council::next_nonfull_voter_set(), 2);
		})
	}

	#[test]
	fn approvals_set_growth_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			// create candidates and voters.
			(1..=250).for_each(|i| create_candidate(i, (i-1) as u32));
			(1..=250).for_each(|i| vote(i, i as usize));

			// all approvals of should return the exact expected vector.
			assert_eq!(Council::all_approvals_of(&180), (0..180).map(|_| true).collect::<Vec<bool>>());

			assert_eq!(Council::all_approvals_of(&32), (0..32).map(|_| true).collect::<Vec<bool>>());
			assert_eq!(Council::all_approvals_of(&8), (0..8).map(|_| true).collect::<Vec<bool>>());
			assert_eq!(Council::all_approvals_of(&64), (0..64).map(|_| true).collect::<Vec<bool>>());
			assert_eq!(Council::all_approvals_of(&65), (0..65).map(|_| true).collect::<Vec<bool>>());
			assert_eq!(Council::all_approvals_of(&63), (0..63).map(|_| true).collect::<Vec<bool>>());

			// NOTE: assuming that APPROVAL_SET_SIZE is more or less small-ish. Might fail otherwise.
			let full_sets = (180 / APPROVAL_FLAG_LEN) / APPROVAL_SET_SIZE;
			let left_over = (180 / APPROVAL_FLAG_LEN) / APPROVAL_SET_SIZE;
			let rem = 180 % APPROVAL_FLAG_LEN;

			// grab and check the last full set, if it exists.
			if full_sets > 0 {
				assert_eq!(
					Council::approvals_of((180, (full_sets-1) as SetIndex )),
					Council::bool_to_flag((0..APPROVAL_SET_SIZE * APPROVAL_FLAG_LEN).map(|_| true).collect::<Vec<bool>>())
				);
			}

			// grab and check the last, half-empty, set.
			if left_over > 0 {
				assert_eq!(
					Council::approvals_of((180, full_sets as SetIndex)),
					Council::bool_to_flag((0..left_over * APPROVAL_FLAG_LEN + rem).map(|_| true).collect::<Vec<bool>>())
				);
			}
		})
	}


	#[test]
	fn cell_status_works() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			(1..=63).for_each(|i| vote(i, 2));

			assert_ok!(Council::retract_voter(Origin::signed(11), 10));
			assert_ok!(Council::retract_voter(Origin::signed(21), 20));

			assert_eq!(Council::cell_status(0, 10), CellStatus::Hole);
			assert_eq!(Council::cell_status(0, 0), CellStatus::Occupied);
			assert_eq!(Council::cell_status(0, 20), CellStatus::Hole);
			assert_eq!(Council::cell_status(0, 63), CellStatus::Head);
			assert_eq!(Council::cell_status(1, 0), CellStatus::Head);
			assert_eq!(Council::cell_status(1, 10), CellStatus::Head);
		})
	}

	#[test]
	fn initial_set_approvals_ignores_voter_index() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));

			// Last argument is essentially irrelevant. You might get or miss a tip.
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0, 5));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 0, 100));

			// indices are more or less ignored. all is pushed.
			assert_eq!(voter_ids(), vec![3, 4, 5]);
		})
	}

	#[test]
	fn bad_approval_index_slashes_voters_and_bond_reduces_stake() {
		with_externalities(&mut ExtBuilder::default().voting_fee(5).voter_bond(2).build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			(1..=63).for_each(|i| vote(i, 2));
			assert_eq!(Balances::free_balance(&1), 20 - 5 - 2); // -5 fee -2 bond
			assert_eq!(Balances::free_balance(&10), 20 - 2);
			assert_eq!(Balances::free_balance(&60), 20 - 2);

			// still no fee
			vote(64, 2);
			assert_eq!(Balances::free_balance(&64), 20 - 2); // -2 bond
			assert_eq!(
				Council::voter_info(&64).unwrap(),
				VoterInfo { last_win: 0, last_active: 0, stake: 20, pot:0 }
			);

			assert_eq!(Council::next_nonfull_voter_set(), 1);

			// now we charge the next voter.
			vote(65, 2);
			assert_eq!(Balances::free_balance(&65), 20 - 5 - 2);
			assert_eq!(
				Council::voter_info(&65).unwrap(),
				VoterInfo { last_win: 0, last_active: 0, stake: 15, pot:0 }
			);
		});
	}

	#[test]
	fn subsequent_set_approvals_checks_voter_index() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));

			assert_ok!(Council::set_approvals(Origin::signed(3), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0, 5));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 0, 100));

			// invalid index
			assert_noop!(Council::set_approvals(Origin::signed(4), vec![true], 0, 5), "invalid voter index");
			// wrong index
			assert_noop!(Council::set_approvals(Origin::signed(4), vec![true], 0, 0), "wrong voter index");
			// correct
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0, 1));
		})
	}

	#[test]
	fn voter_index_does_not_take_holes_into_account() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			// create 65. 64 (set0) + 1 (set1)
			(1..=65).for_each(|i| vote(i, 2));

			// account 65 has global index 65.
			assert_eq!(Council::voter_at(64).unwrap(), 65);

			assert_ok!(Council::retract_voter(Origin::signed(1), 0));
			assert_ok!(Council::retract_voter(Origin::signed(2), 1));

			// still the same. These holes are in some other set.
			assert_eq!(Council::voter_at(64).unwrap(), 65);
			// proof: can submit a new approval with the old index.
			assert_noop!(Council::set_approvals(Origin::signed(65), vec![false, true], 0, 64 - 2), "wrong voter index");
			assert_ok!(Council::set_approvals(Origin::signed(65), vec![false, true], 0, 64));
		})
	}

	#[test]
	fn simple_candidate_submission_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
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
		let mut t = ExtBuilder::default().build();
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
		let mut t = new_test_ext_with_candidate_holes();

		with_externalities(&mut t, || {
			System::set_block_number(1);
			assert_noop!(Council::submit_candidacy(Origin::signed(4), 3), "invalid candidate slot");
		});
	}

	#[test]
	fn bad_candidate_slot_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!(Council::submit_candidacy(Origin::signed(1), 1), "invalid candidate slot");
		});
	}

	#[test]
	fn non_free_candidate_slot_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!(Council::submit_candidacy(Origin::signed(2), 0), "invalid candidate slot");
		});
	}

	#[test]
	fn dupe_candidate_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_eq!(Council::candidates(), vec![1]);
			assert_noop!(Council::submit_candidacy(Origin::signed(1), 1), "duplicate candidate submission");
		});
	}

	#[test]
	fn poor_candidate_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_noop!(Council::submit_candidacy(Origin::signed(7), 0), "candidate has not enough funds");
		});
	}

	#[test]
	fn balance_should_lock_to_the_maximum() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_eq!(Balances::free_balance(&2), 20);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));

			assert_eq!(Balances::free_balance(&2), 20 - bond() );
			assert_noop!(Balances::reserve(&2, 1), "account liquidity restrictions prevent withdrawal"); // locked.

			// deposit a bit more.
			let _ = Balances::deposit_creating(&2, 100);
			assert_ok!(Balances::reserve(&2, 1)); // locked but now has enough.

			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_noop!(Balances::reserve(&2, 1), "account liquidity restrictions prevent withdrawal"); // locked.
			assert_eq!(Balances::locks(&2).len(), 1);
			assert_eq!(Balances::locks(&2)[0].amount, 100 + 20);

			assert_ok!(Council::retract_voter(Origin::signed(2), 0));

			assert_eq!(Balances::locks(&2).len(), 0);
			assert_eq!(Balances::free_balance(&2), 120 - 1); // 1 ok call to .reserve() happened.
			assert_ok!(Balances::reserve(&2, 1)); // unlocked.
		});
	}

	#[test]
	fn balance_should_lock_on_submit_approvals_unlock_on_retract() {
		with_externalities(&mut ExtBuilder::default().voter_bond(8).voting_fee(0).build(), || {
			System::set_block_number(1);
			assert_eq!(Council::candidates(), Vec::<u64>::new());
			assert_eq!(Balances::free_balance(&2), 20);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));

			assert_eq!(Balances::free_balance(&2), 12); // 20 - 8 (bond)
			assert_noop!(Balances::reserve(&2, 10), "account liquidity restrictions prevent withdrawal"); // locked.

			assert_ok!(Council::retract_voter(Origin::signed(2), 0));

			assert_eq!(Balances::free_balance(&2), 20);
			assert_ok!(Balances::reserve(&2, 10)); // unlocked.
		});
	}

	#[test]
	fn accumulating_weight_and_decaying_should_work() {
		with_externalities(&mut ExtBuilder::default().balance_factor(10).build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 2));

			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![false, false, true], 0, 0));

			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());

			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 100, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (100, 1), (500, 5), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 11), (5, 11)]);
			assert_eq!(Council::voter_info(6).unwrap(), VoterInfo { last_win: 1, last_active: 0, stake: 600, pot: 0});
			assert_eq!(Council::voter_info(5).unwrap(), VoterInfo { last_win: 1, last_active: 0, stake: 500, pot: 0});
			assert_eq!(Council::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0});

			System::set_block_number(12);
			// retract needed to unlock approval funds => submit candidacy again.
			assert_ok!(Council::retract_voter(Origin::signed(6), 0));
			assert_ok!(Council::retract_voter(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 1, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 1, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(14);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 100 + Council::get_offset(100, 1), 1), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (100 + 96, 1), (500, 5), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 19), (5, 19)]);
			assert_eq!(
				Council::voter_info(6).unwrap(),
				VoterInfo { last_win: 2, last_active: 1, stake: 600, pot:0 }
			);
			assert_eq!(Council::voter_info(5).unwrap(), VoterInfo { last_win: 2, last_active: 1, stake: 500, pot:0 });
			assert_eq!(Council::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot:0 });

			System::set_block_number(20);
			assert_ok!(Council::retract_voter(Origin::signed(6), 0));
			assert_ok!(Council::retract_voter(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 2, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 2, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(22);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 2), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 2), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 100 + Council::get_offset(100, 2), 2), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (100 + 96 + 93, 1), (500, 5), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 27), (5, 27)]);
			assert_eq!(
				Council::voter_info(6).unwrap(),
				VoterInfo { last_win: 3, last_active: 2, stake: 600, pot: 0}
			);
			assert_eq!(Council::voter_info(5).unwrap(), VoterInfo { last_win: 3, last_active: 2, stake: 500, pot: 0});
			assert_eq!(Council::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0});


			System::set_block_number(28);
			assert_ok!(Council::retract_voter(Origin::signed(6), 0));
			assert_ok!(Council::retract_voter(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 3, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 3, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(30);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 3), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 3), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 100 + Council::get_offset(100, 3), 3), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (100 + 96 + 93 + 90, 1), (500, 5), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 35), (5, 35)]);
			assert_eq!(
				Council::voter_info(6).unwrap(),
				VoterInfo { last_win: 4, last_active: 3, stake: 600, pot: 0}
			);
			assert_eq!(Council::voter_info(5).unwrap(), VoterInfo { last_win: 4, last_active: 3, stake: 500, pot: 0});
			assert_eq!(Council::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0});
		})
	}

	#[test]
	fn winning_resets_accumulated_pot() {
		with_externalities(&mut ExtBuilder::default().balance_factor(10).build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 3));

			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, true, false, false], 0, 1));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true, true], 0, 2));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 4, 400, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(3), 3, 300, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(2), 2, 300, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(300, 2), (300, 3), (400, 4), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 11), (4, 11)]);

			System::set_block_number(12);
			assert_ok!(Council::retract_voter(Origin::signed(6), 0));
			assert_ok!(Council::retract_voter(Origin::signed(4), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 1));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false, false], 1, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, true, false, false], 1, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(14);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 4, 400, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(3), 3, 300 + Council::get_offset(300, 1), 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(2), 2, 300 + Council::get_offset(300, 1), 1), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(400, 4), (588, 2), (588, 3), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 19), (3, 19)]);

			System::set_block_number(20);
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(22);
			// 2 will not get re-elected with 300 + 288, instead just 300.
			// because one of 3's candidates (3) won in previous round
			// 4 on the other hand will get extra weight since it was unlucky.
			assert_eq!(Council::present_winner(Origin::signed(3), 2, 300, 2), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 4, 400 + Council::get_offset(400, 1), 2), Ok(()));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(4, 27), (2, 27)]);
		})
	}

	#[test]
	fn resubmitting_approvals_stores_pot() {
		with_externalities(&mut ExtBuilder::default()
			.voter_bond(0)
			.voting_fee(0)
			.balance_factor(10)
			.build(),
		|| { System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 2));

			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 0, 1));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![false, false, true], 0, 2));

			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());

			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 100, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (100, 1), (500, 5), (600, 6)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 11), (5, 11)]);

			System::set_block_number(12);
			assert_ok!(Council::retract_voter(Origin::signed(6), 0));
			assert_ok!(Council::retract_voter(Origin::signed(5), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true, false, false], 1, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true, false], 1, 1));
			// give 1 some new high balance
			let _ = Balances::make_free_balance_be(&1, 997);
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![false, false, true], 1, 2));
			assert_eq!(Council::voter_info(1).unwrap(),
				VoterInfo {
					stake: 1000, // 997 + 3 which is candidacy bond.
					pot: Council::get_offset(100, 1),
					last_active: 1,
					last_win: 1,
				}
			);
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(6, 11), (5, 11)]);

			System::set_block_number(14);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(5), 5, 500, 1), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(1), 1, 1000 + 96 /* pot */, 1), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (500, 5), (600, 6), (1096, 1)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(1, 19), (6, 19)]);
		})
	}

	#[test]
	fn get_offset_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Council::get_offset(100, 0), 0);
			assert_eq!(Council::get_offset(100, 1), 96);
			assert_eq!(Council::get_offset(100, 2), 96 + 93);
			assert_eq!(Council::get_offset(100, 3), 96 + 93 + 90);
			assert_eq!(Council::get_offset(100, 4), 96 + 93 + 90 + 87);
			// limit
			assert_eq!(Council::get_offset(100, 1000), 100 * 24);

			assert_eq!(Council::get_offset(50_000_000_000, 0), 0);
			assert_eq!(Council::get_offset(50_000_000_000, 1), 48_000_000_000);
			assert_eq!(Council::get_offset(50_000_000_000, 2), 48_000_000_000 + 46_080_000_000);
			assert_eq!(Council::get_offset(50_000_000_000, 3), 48_000_000_000 + 46_080_000_000 + 44_236_800_000);
			assert_eq!(
				Council::get_offset(50_000_000_000, 4),
				48_000_000_000 + 46_080_000_000 + 44_236_800_000 + 42_467_328_000
			);
			// limit
			assert_eq!(Council::get_offset(50_000_000_000, 1000), 50_000_000_000 * 24);
		})
	}

	#[test]
	fn get_offset_with_zero_decay() {
		with_externalities(&mut ExtBuilder::default().decay_ratio(0).build(), || {
			assert_eq!(Council::get_offset(100, 0), 0);
			assert_eq!(Council::get_offset(100, 1), 0);
			assert_eq!(Council::get_offset(100, 2), 0);
			assert_eq!(Council::get_offset(100, 3), 0);
			// limit
			assert_eq!(Council::get_offset(100, 1000), 0);
		})
	}

	#[test]
	fn voting_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));

			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0, 1));

			assert_eq!(Council::all_approvals_of(&1), vec![true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true]);
			assert_eq!(voter_ids(), vec![1, 4]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));

			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true, true], 0, 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, true], 0, 3));

			assert_eq!(Council::all_approvals_of(&1), vec![true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true]);
			assert_eq!(Council::all_approvals_of(&2), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&3), vec![false, true, true]);

			assert_eq!(voter_ids(), vec![1, 4, 2, 3]);
		});
	}

	#[test]
	fn proxy_voting_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));

			Democracy::force_proxy(1, 11);
			Democracy::force_proxy(2, 12);
			Democracy::force_proxy(3, 13);
			Democracy::force_proxy(4, 14);
			assert_ok!(Council::proxy_set_approvals(Origin::signed(11), vec![true], 0, 0));
			assert_ok!(Council::proxy_set_approvals(Origin::signed(14), vec![true], 0, 1));

			assert_eq!(Council::all_approvals_of(&1), vec![true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true]);
			assert_eq!(voter_ids(), vec![1, 4]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));

			assert_ok!(Council::proxy_set_approvals(Origin::signed(12), vec![false, true, true], 0, 2));
			assert_ok!(Council::proxy_set_approvals(Origin::signed(13), vec![false, true, true], 0, 3));

			assert_eq!(Council::all_approvals_of(&1), vec![true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true]);
			assert_eq!(Council::all_approvals_of(&2), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&3), vec![false, true, true]);

			assert_eq!(voter_ids(), vec![1, 4, 2, 3]);
		});
	}

	#[test]
	fn setting_any_approval_vote_count_without_any_candidate_count_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_eq!(Council::candidates().len(), 0);

			assert_noop!(
				Council::set_approvals(Origin::signed(4), vec![], 0, 0),
				"amount of candidates to receive approval votes should be non-zero"
			);
		});
	}

	#[test]
	fn setting_an_approval_vote_count_more_than_candidate_count_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_eq!(Council::candidates().len(), 1);

			assert_noop!(
				Council::set_approvals(Origin::signed(4),vec![true, true], 0, 0),
				"amount of candidate votes cannot exceed amount of candidates"
			);
		});
	}

	#[test]
	fn resubmitting_voting_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true], 0, 0));

			assert_eq!(Council::all_approvals_of(&4), vec![true]);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_eq!(Council::candidates().len(), 3);
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true, false, true], 0, 0));

			assert_eq!(Council::all_approvals_of(&4), vec![true, false, true]);
		});
	}

	#[test]
	fn retracting_voter_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);

			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_eq!(Council::candidates().len(), 3);

			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true, true], 0, 1));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, true], 0, 2));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![true, false, true], 0, 3));

			assert_eq!(voter_ids(), vec![1, 2, 3, 4]);
			assert_eq!(Council::all_approvals_of(&1), vec![true]);
			assert_eq!(Council::all_approvals_of(&2), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&3), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(1), 0));

			assert_eq!(voter_ids(), vec![0, 2, 3, 4]);
			assert_eq!(Council::all_approvals_of(&1), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&2), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&3), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(2), 1));

			assert_eq!(voter_ids(), vec![0, 0, 3, 4]);
			assert_eq!(Council::all_approvals_of(&1), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&2), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&3), vec![false, true, true]);
			assert_eq!(Council::all_approvals_of(&4), vec![true, false, true]);

			assert_ok!(Council::retract_voter(Origin::signed(3), 2));

			assert_eq!(voter_ids(), vec![0, 0, 0, 4]);
			assert_eq!(Council::all_approvals_of(&1), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&2), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&3), Vec::<bool>::new());
			assert_eq!(Council::all_approvals_of(&4), vec![true, false, true]);
		});
	}

	#[test]
	fn invalid_retraction_index_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_eq!(voter_ids(), vec![1, 2]);
			assert_noop!(Council::retract_voter(Origin::signed(1), 1), "retraction index mismatch");
		});
	}

	#[test]
	fn overflow_retraction_index_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0));
			assert_noop!(Council::retract_voter(Origin::signed(1), 1), "retraction index invalid");
		});
	}

	#[test]
	fn non_voter_retraction_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 0));
			assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0));
			assert_noop!(Council::retract_voter(Origin::signed(2), 0), "cannot retract non-voter");
		});
	}

	#[test]
	fn approval_storage_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));

			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![], 0, 0));

			assert_eq!(Council::all_approvals_of(&2), vec![true]);
			// NOTE: these two are stored in mem differently though.
			assert_eq!(Council::all_approvals_of(&3), vec![]);
			assert_eq!(Council::all_approvals_of(&4), vec![]);

			assert_eq!(Council::approvals_of((3, 0)), vec![0]);
			assert_eq!(Council::approvals_of((4, 0)), vec![]);
		});
	}

	#[test]
	fn simple_tally_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0, 0));
			assert_eq!(voter_ids(), vec![2, 5]);
			assert_eq!(Council::all_approvals_of(&2), vec![true]);
			assert_eq!(Council::all_approvals_of(&5), vec![false, true]);
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(4), 2, 20, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 5, 50, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (0, 0), (20, 2), (50, 5)]));

			assert_ok!(Council::end_block(System::block_number()));

			assert!(!Council::presentation_active());
			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);

			assert!(!Council::is_a_candidate(&2));
			assert!(!Council::is_a_candidate(&5));
			assert_eq!(Council::vote_index(), 1);
			assert_eq!(Council::voter_info(2), Some(VoterInfo { last_win: 1, last_active: 0, stake: 20, pot: 0 }));
			assert_eq!(Council::voter_info(5), Some(VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0 }));
		});
	}

	#[test]
	fn seats_should_be_released() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_eq!(Council::present_winner(Origin::signed(4), 2, 20, 0), Ok(()));
			assert_eq!(Council::present_winner(Origin::signed(4), 5, 50, 0), Ok(()));
			assert_eq!(Council::leaderboard(), Some(vec![(0, 0), (0, 0), (20, 2), (50, 5)]));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);
			let mut current = System::block_number();
			let free_block;
			loop {
				current += 1;
				System::set_block_number(current);
				assert_ok!(Council::end_block(System::block_number()));
				if Council::active_council().len() == 0 {
					free_block = current;
					break;
				}
			}
			// 11 + 2 which is the next voting period.
			assert_eq!(free_block, 14);
		});
	}

	#[test]
	fn presentations_with_zero_staked_deposit_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_noop!(
				Council::present_winner(Origin::signed(4), 2, 0, 0),
				"stake deposited to present winner and be added to leaderboard should be non-zero"
			);
		});
	}

	#[test]
	fn double_presentations_should_be_punished() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert!(Balances::can_slash(&4, 10));

			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));
			assert_eq!(Council::present_winner(Origin::signed(4), 5, 50, 0), Err("duplicate presentation"));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::active_council(), vec![(5, 11), (2, 11)]);
			assert_eq!(Balances::total_balance(&4), 38);
		});
	}

	#[test]
	fn retracting_inactive_voter_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(5),
				(voter_ids().iter().position(|&i| i == 5).unwrap() as u32).into(),
				2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2
			));

			assert_eq!(voter_ids(), vec![0, 5]);
			assert_eq!(Council::all_approvals_of(&2).len(), 0);
			assert_eq!(Balances::total_balance(&2), 20);
			assert_eq!(Balances::total_balance(&5), 50);
		});
	}

	#[test]
	fn presenting_for_double_election_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_eq!(Council::submit_candidacy(Origin::signed(2), 0), Ok(()));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			// NOTE: This is now mandatory to disable the lock
			assert_ok!(Council::retract_voter(Origin::signed(2), 0));
			assert_eq!(Council::submit_candidacy(Origin::signed(2), 0), Ok(()));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_noop!(
				Council::present_winner(Origin::signed(4), 2, 20, 1),
				"candidate must not form a duplicated member if elected"
			);
		});
	}

	#[test]
	fn retracting_inactive_voter_with_other_candidates_in_slots_should_work() {
		with_externalities(&mut ExtBuilder::default().voter_bond(2).build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(11);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(5),
				(voter_ids().iter().position(|&i| i == 5).unwrap() as u32).into(),
				2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2
			));

			assert_eq!(voter_ids(), vec![0, 5]);
			assert_eq!(Council::all_approvals_of(&2).len(), 0);
			assert_eq!(Balances::total_balance(&2), 18);
			assert_eq!(Balances::total_balance(&5), 52);
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_reporter_index_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(2),
				42,
				2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2
			), "invalid reporter index");
		});
	}

	#[test]
	fn retracting_inactive_voter_with_bad_target_index_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(2),
				(voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2, 42,
				2
			), "invalid target index");
		});
	}

	#[test]
	fn attempting_to_retract_active_voter_should_slash_reporter() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 1));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 2));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 3));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false, false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, true, false, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::set_desired_seats(3));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20 + Council::get_offset(20, 1), 1));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30 + Council::get_offset(30, 1), 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_eq!(Council::vote_index(), 2);
			assert_eq!(Council::inactivity_grace_period(), 1);
			assert_eq!(Council::voting_period(), 4);
			assert_eq!(Council::voter_info(4), Some(VoterInfo { last_win: 1, last_active: 0, stake: 40, pot: 0 }));

			assert_ok!(Council::reap_inactive_voter(Origin::signed(4),
				(voter_ids().iter().position(|&i| i == 4).unwrap() as u32).into(),
				2,
				(voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2
			));

			assert_eq!(voter_ids(), vec![2, 3, 0, 5]);
			assert_eq!(Council::all_approvals_of(&4).len(), 0);
			assert_eq!(Balances::total_balance(&4), 40);
		});
	}

	#[test]
	fn attempting_to_retract_inactive_voter_by_nonvoter_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![true], 1, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert_noop!(Council::reap_inactive_voter(Origin::signed(4),
				0,
				2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
				2
			), "reporter must be a voter");
		});
	}

	#[test]
	fn presenting_loser_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 1, 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));

			assert_eq!(Council::leaderboard(), Some(vec![
				(30, 3),
				(40, 4),
				(50, 5),
				(60, 1)
			]));

			assert_noop!(Council::present_winner(Origin::signed(4), 2, 20, 0), "candidate not worthy of leaderboard");
		});
	}

	#[test]
	fn presenting_loser_first_should_not_matter() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 2, 20, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 1, 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));

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
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_noop!(
				Council::present_winner(Origin::signed(5), 5, 1, 0),
				"cannot present outside of presentation period"
			);
		});
	}

	#[test]
	fn present_with_invalid_vote_index_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_noop!(Council::present_winner(Origin::signed(4), 2, 20, 1), "index not current");
		});
	}

	#[test]
	fn present_when_presenter_is_poor_should_not_work() {
		let test_present = |p| {
			with_externalities(&mut ExtBuilder::default()
				.voting_fee(5)
				.voter_bond(2)
				.bad_presentation_punishment(p)
				.build(),
			|| {
				System::set_block_number(4);
				let _ = Balances::make_free_balance_be(&1, 15);
				assert!(!Council::presentation_active());

				assert_ok!(Council::submit_candidacy(Origin::signed(1), 0)); // -3
				assert_eq!(Balances::free_balance(&1), 12);
				assert_ok!(Council::set_approvals(Origin::signed(1), vec![true], 0, 0)); // -2 -5
				assert_ok!(Council::end_block(System::block_number()));

				System::set_block_number(6);
				assert_eq!(Balances::free_balance(&1), 5);
				assert_eq!(Balances::reserved_balance(&1), 5);
				if p > 5 {
					assert_noop!(Council::present_winner(
						Origin::signed(1), 1, 10, 0),
						"presenter must have sufficient slashable funds"
					);
				} else {
					assert_ok!(Council::present_winner(Origin::signed(1), 1, 10, 0));
				}
			});
		};
		test_present(4);
		test_present(6);
	}

	#[test]
	fn invalid_present_tally_should_slash() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());
			assert_eq!(Balances::total_balance(&4), 40);

			assert_ok!(Council::submit_candidacy(Origin::signed(2), 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![true, false], 0, 0));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_err!(Council::present_winner(Origin::signed(4), 2, 80, 0), "incorrect total");

			assert_eq!(Balances::total_balance(&4), 38);
		});
	}

	#[test]
	fn runners_up_should_be_kept() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert!(!Council::presentation_active());

			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0));

			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Council::presentation_active());
			assert_ok!(Council::present_winner(Origin::signed(4), 1, 60, 0));
			// leaderboard length is the empty seats plus the carry count (i.e. 5 + 2), where those
			// to be carried are the lowest and stored in lowest indices
			assert_eq!(Council::leaderboard(), Some(vec![
				(0, 0),
				(0, 0),
				(0, 0),
				(60, 1)
			]));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));
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
			assert_eq!(Council::voter_info(2), Some(VoterInfo { last_win: 0, last_active: 0, stake: 20, pot: 0 }));
			assert_eq!(Council::voter_info(3), Some(VoterInfo { last_win: 0, last_active: 0, stake: 30, pot: 0 }));
			assert_eq!(Council::voter_info(4), Some(VoterInfo { last_win: 0, last_active: 0, stake: 40, pot: 0 }));
			assert_eq!(Council::voter_info(5), Some(VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0 }));
			assert_eq!(Council::voter_info(6), Some(VoterInfo { last_win: 1, last_active: 0, stake: 60, pot: 0 }));
			assert_eq!(Council::candidate_reg_info(3), Some((0, 2)));
			assert_eq!(Council::candidate_reg_info(4), Some((0, 3)));
		});
	}

	#[test]
	fn second_tally_should_use_runners_up() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(4);
			assert_ok!(Council::submit_candidacy(Origin::signed(1), 0));
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(2), 1));
			assert_ok!(Council::set_approvals(Origin::signed(2), vec![false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(3), 2));
			assert_ok!(Council::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(4), 3));
			assert_ok!(Council::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0));
			assert_ok!(Council::submit_candidacy(Origin::signed(5), 4));
			assert_ok!(Council::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(6);
			assert_ok!(Council::present_winner(Origin::signed(4), 1, 60, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40, 0));
			assert_ok!(Council::present_winner(Origin::signed(4), 5, 50, 0));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(8);
			assert_ok!(Council::set_approvals(Origin::signed(6), vec![false, false, true, false], 1, 0));
			assert_ok!(Council::set_desired_seats(3));
			assert_ok!(Council::end_block(System::block_number()));

			System::set_block_number(10);
			assert_ok!(Council::present_winner(Origin::signed(4), 3, 30 + Council::get_offset(30, 1) + 60, 1));
			assert_ok!(Council::present_winner(Origin::signed(4), 4, 40 + Council::get_offset(40, 1), 1));
			assert_ok!(Council::end_block(System::block_number()));

			assert!(!Council::presentation_active());
			assert_eq!(Council::active_council(), vec![(1, 11), (5, 11), (3, 15)]);

			assert!(!Council::is_a_candidate(&1));
			assert!(!Council::is_a_candidate(&2));
			assert!(!Council::is_a_candidate(&3));
			assert!(!Council::is_a_candidate(&5));
			assert!(Council::is_a_candidate(&4));
			assert_eq!(Council::vote_index(), 2);
			assert_eq!(Council::voter_info(2), Some( VoterInfo { last_win: 0, last_active: 0, stake: 20, pot: 0}));
			assert_eq!(Council::voter_info(3), Some( VoterInfo { last_win: 2, last_active: 0, stake: 30, pot: 0}));
			assert_eq!(Council::voter_info(4), Some( VoterInfo { last_win: 0, last_active: 0, stake: 40, pot: 0}));
			assert_eq!(Council::voter_info(5), Some( VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0}));
			assert_eq!(
				Council::voter_info(6),
				Some(VoterInfo { last_win: 2, last_active: 1, stake: 60, pot: 0})
			);

			assert_eq!(Council::candidate_reg_info(4), Some((0, 3)));
		});
	}
}
