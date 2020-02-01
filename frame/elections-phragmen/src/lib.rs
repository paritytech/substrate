// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Phragmen Election Module.
//!
//! An election module based on sequential phragmen.
//!
//! ### Term and Round
//!
//! The election happens in _rounds_: every `N` blocks, all previous members are retired and a new
//! set is elected (which may or may not have an intersection with the previous set). Each round
//! lasts for some number of blocks defined by `TermDuration` storage item. The words _term_ and
//! _round_ can be used interchangeably in this context.
//!
//! `TermDuration` might change during a round. This can shorten or extend the length of the round.
//! The next election round's block number is never stored but rather always checked on the fly.
//! Based on the current block number and `TermDuration`, the condition `BlockNumber % TermDuration
//! == 0` being satisfied will always trigger a new election round.
//!
//! ### Voting
//!
//! Voters can vote for any set of the candidates by providing a list of account ids. Invalid votes
//! (voting for non-candidates) are ignored during election. Yet, a voter _might_ vote for a future
//! candidate. Voters reserve a bond as they vote. Each vote defines a `value`. This amount is
//! locked from the account of the voter and indicates the weight of the vote. Voters can update
//! their votes at any time by calling `vote()` again. This keeps the bond untouched but can
//! optionally change the locked `value`. After a round, votes are kept and might still be valid for
//! further rounds. A voter is responsible for calling `remove_voter` once they are done to have
//! their bond back and remove the lock.
//!
//! Voters also report other voters as being defunct to earn their bond. A voter is defunct once all
//! of the candidates that they have voted for are neither a valid candidate anymore nor a member.
//! Upon reporting, if the target voter is actually defunct, the reporter will be rewarded by the
//! voting bond of the target. The target will lose their bond and get removed. If the target is not
//! defunct, the reporter is slashed and removed. To prevent being reported, voters should manually
//! submit a `remove_voter()` as soon as they are in the defunct state.
//!
//! ### Candidacy and Members
//!
//! Candidates also reserve a bond as they submit candidacy. A candidate cannot take their candidacy
//! back. A candidate can end up in one of the below situations:
//!   - **Winner**: A winner is kept as a _member_. They must still have a bond in reserve and they
//!     are automatically counted as a candidate for the next election.
//!   - **Runner-up**: Runners-up are the best candidates immediately after the winners. The number
//!     of runners_up to keep is configurable. Runners-up are used, in order that they are elected,
//!     as replacements when a candidate is kicked by `[remove_member]`, or when an active member
//!     renounces their candidacy. Runners are automatically counted as a candidate for the next
//!     election.
//!   - **Loser**: Any of the candidate who are not a winner are left as losers. A loser might be an
//!     _outgoing member or runner_, meaning that they are an active member who failed to keep their
//!     spot. An outgoing will always lose their bond.
//!
//! ##### Renouncing candidacy.
//!
//! All candidates, elected or not, can renounce their candidacy. A call to [`renounce_candidacy`]
//! will always cause the candidacy bond to be refunded.
//!
//! Note that with the members being the default candidates for the next round and votes persisting
//! in storage, the election system is entirely stable given no further input. This means that if
//! the system has a particular set of candidates `C` and voters `V` that lead to a set of members
//! `M` being elected, as long as `V` and `C` don't remove their candidacy and votes, `M` will keep
//! being re-elected at the end of each round.
//!
//! ### Module Information
//!
//! - [`election_sp_phragmen::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_runtime::{print, DispatchResult, DispatchError, traits::{Zero, StaticLookup, Convert}};
use frame_support::{
	decl_storage, decl_event, ensure, decl_module, decl_error, weights::SimpleDispatchInfo,
	traits::{
		Currency, Get, LockableCurrency, LockIdentifier, ReservableCurrency, WithdrawReasons,
		ChangeMembers, OnUnbalanced, WithdrawReason, Contains
	}
};
use sp_phragmen::ExtendedBalance;
use frame_system::{self as system, ensure_signed, ensure_root};

const MODULE_ID: LockIdentifier = *b"phrelect";

/// The maximum votes allowed per voter.
pub const MAXIMUM_VOTE: usize = 16;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.c
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The currency that people are electing with.
	type Currency:
		LockableCurrency<Self::AccountId, Moment=Self::BlockNumber> +
		ReservableCurrency<Self::AccountId>;

	/// What to do when the members change.
	type ChangeMembers: ChangeMembers<Self::AccountId>;

	/// Convert a balance into a number used for election calculation.
	/// This must fit into a `u64` but is allowed to be sensibly lossy.
	type CurrencyToVote: Convert<BalanceOf<Self>, u64> + Convert<u128, BalanceOf<Self>>;

	/// How much should be locked up in order to submit one's candidacy.
	type CandidacyBond: Get<BalanceOf<Self>>;

	/// How much should be locked up in order to be able to submit votes.
	type VotingBond: Get<BalanceOf<Self>>;

	/// Handler for the unbalanced reduction when a candidate has lost (and is not a runner-up)
	type LoserCandidate: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when a reporter has submitted a bad defunct report.
	type BadReport: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when a member has been kicked.
	type KickedMember: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Number of members to elect.
	type DesiredMembers: Get<u32>;

	/// Number of runners_up to keep.
	type DesiredRunnersUp: Get<u32>;

	/// How long each seat is kept. This defines the next block number at which an election
	/// round will happen. If set to zero, no elections are ever triggered and the module will
	/// be in passive mode.
	type TermDuration: Get<Self::BlockNumber>;
}

decl_storage! {
	trait Store for Module<T: Trait> as PhragmenElection {
		// ---- State
		/// The current elected membership. Sorted based on account id.
		pub Members get(fn members): Vec<(T::AccountId, BalanceOf<T>)>;
		/// The current runners_up. Sorted based on low to high merit (worse to best runner).
		pub RunnersUp get(fn runners_up): Vec<(T::AccountId, BalanceOf<T>)>;
		/// The total number of vote rounds that have happened, excluding the upcoming one.
		pub ElectionRounds get(fn election_rounds): u32 = Zero::zero();

		/// Votes of a particular voter, with the round index of the votes.
		pub VotesOf get(fn votes_of): linked_map hasher(blake2_256) T::AccountId => Vec<T::AccountId>;
		/// Locked stake of a voter.
		pub StakeOf get(fn stake_of): map hasher(blake2_256) T::AccountId => BalanceOf<T>;

		/// The present candidate list. Sorted based on account-id. A current member or a runner can
		/// never enter this vector and is always implicitly assumed to be a candidate.
		pub Candidates get(fn candidates): Vec<T::AccountId>;
	}
}

decl_error! {
	/// Error for the elections-phragmen module.
	pub enum Error for Module<T: Trait> {
		/// Cannot vote when no candidates or members exist.
		UnableToVote,
		/// Must vote for at least one candidate.
		NoVotes,
		/// Cannot vote more than candidates.
		TooManyVotes,
		/// Cannot vote more than maximum allowed.
		MaximumVotesExceeded,
		/// Cannot vote with stake less than minimum balance.
		LowBalance,
		/// Voter can not pay voting bond.
		UnableToPayBond,
		/// Must be a voter.
		MustBeVoter,
		/// Cannot report self.
		ReportSelf,
		/// Duplicated candidate submission.
		DuplicatedCandidate,
		/// Member cannot re-submit candidacy.
		MemberSubmit,
		/// Runner cannot re-submit candidacy.
		RunnerSubmit,
		/// Candidate does not have enough funds.
		InsufficientCandidateFunds,
		/// Origin is not a candidate, member or a runner up.
		InvalidOrigin,
		/// Not a member.
		NotMember,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		const CandidacyBond: BalanceOf<T> = T::CandidacyBond::get();
		const VotingBond: BalanceOf<T> = T::VotingBond::get();
		const DesiredMembers: u32 = T::DesiredMembers::get();
		const DesiredRunnersUp: u32 = T::DesiredRunnersUp::get();
		const TermDuration: T::BlockNumber = T::TermDuration::get();

		/// Vote for a set of candidates for the upcoming round of election.
		///
		/// The `votes` should:
		///   - not be empty.
		///   - be less than the number of candidates.
		///
		/// Upon voting, `value` units of `who`'s balance is locked and a bond amount is reserved.
		/// It is the responsibility of the caller to not place all of their balance into the lock
		/// and keep some for further transactions.
		///
		/// # <weight>
		/// #### State
		/// Reads: O(1)
		/// Writes: O(V) given `V` votes. V is bounded by 16.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn vote(origin, votes: Vec<T::AccountId>, #[compact] value: BalanceOf<T>) {
			let who = ensure_signed(origin)?;

			let candidates_count = <Candidates<T>>::decode_len().unwrap_or(0) as usize;
			let members_count = <Members<T>>::decode_len().unwrap_or(0) as usize;
			// addition is valid: candidates and members never overlap.
			let allowed_votes = candidates_count + members_count;

			ensure!(!allowed_votes.is_zero(), Error::<T>::UnableToVote);
			ensure!(votes.len() <= allowed_votes, Error::<T>::TooManyVotes);
			ensure!(votes.len() <= MAXIMUM_VOTE, Error::<T>::MaximumVotesExceeded);
			ensure!(!votes.is_empty(), Error::<T>::NoVotes);

			ensure!(
				value > T::Currency::minimum_balance(),
				Error::<T>::LowBalance,
			);

			if !Self::is_voter(&who) {
				// first time voter. Reserve bond.
				T::Currency::reserve(&who, T::VotingBond::get())
					.map_err(|_| Error::<T>::UnableToPayBond)?;
			}
			// Amount to be locked up.
			let locked_balance = value.min(T::Currency::total_balance(&who));

			// lock
			T::Currency::set_lock(
				MODULE_ID,
				&who,
				locked_balance,
				WithdrawReasons::except(WithdrawReason::TransactionPayment),
			);
			<StakeOf<T>>::insert(&who, locked_balance);
			<VotesOf<T>>::insert(&who, votes);
		}

		/// Remove `origin` as a voter. This removes the lock and returns the bond.
		///
		/// # <weight>
		/// #### State
		/// Reads: O(1)
		/// Writes: O(1)
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn remove_voter(origin) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_voter(&who), Error::<T>::MustBeVoter);

			Self::do_remove_voter(&who, true);
		}

		/// Report `target` for being an defunct voter. In case of a valid report, the reporter is
		/// rewarded by the bond amount of `target`. Otherwise, the reporter itself is removed and
		/// their bond is slashed.
		///
		/// A defunct voter is defined to be:
		///   - a voter whose current submitted votes are all invalid. i.e. all of them are no
		///     longer a candidate nor an active member.
		///
		/// # <weight>
		/// #### State
		/// Reads: O(NLogM) given M current candidates and N votes for `target`.
		/// Writes: O(1)
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn report_defunct_voter(origin, target: <T::Lookup as StaticLookup>::Source) {
			let reporter = ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;

			ensure!(reporter != target, Error::<T>::ReportSelf);
			ensure!(Self::is_voter(&reporter), Error::<T>::MustBeVoter);

			// Checking if someone is a candidate and a member here is O(LogN), making the whole
			// function O(MLonN) with N candidates in total and M of them being voted by `target`.
			// We could easily add another mapping to be able to check if someone is a candidate in
			// `O(1)` but that would make the process of removing candidates at the end of each
			// round slightly harder. Note that for now we have a bound of number of votes (`N`).
			let valid = Self::is_defunct_voter(&target);
			if valid {
				// reporter will get the voting bond of the target
				T::Currency::repatriate_reserved(&target, &reporter, T::VotingBond::get())?;
				// remove the target. They are defunct.
				Self::do_remove_voter(&target, false);
			} else {
				// slash the bond of the reporter.
				let imbalance = T::Currency::slash_reserved(&reporter, T::VotingBond::get()).0;
				T::BadReport::on_unbalanced(imbalance);
				// remove the reporter.
				Self::do_remove_voter(&reporter, false);
			}
			Self::deposit_event(RawEvent::VoterReported(target, reporter, valid));
		}


		/// Submit oneself for candidacy.
		///
		/// A candidate will either:
		///   - Lose at the end of the term and forfeit their deposit.
		///   - Win and become a member. Members will eventually get their stash back.
		///   - Become a runner-up. Runners-ups are reserved members in case one gets forcefully
		///     removed.
		///
		/// # <weight>
		/// #### State
		/// Reads: O(LogN) Given N candidates.
		/// Writes: O(1)
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn submit_candidacy(origin) {
			let who = ensure_signed(origin)?;

			let is_candidate = Self::is_candidate(&who);
			ensure!(is_candidate.is_err(), Error::<T>::DuplicatedCandidate);
			// assured to be an error, error always contains the index.
			let index = is_candidate.unwrap_err();

			ensure!(!Self::is_member(&who), Error::<T>::MemberSubmit);
			ensure!(!Self::is_runner(&who), Error::<T>::RunnerSubmit);

			T::Currency::reserve(&who, T::CandidacyBond::get())
				.map_err(|_| Error::<T>::InsufficientCandidateFunds)?;

			<Candidates<T>>::mutate(|c| c.insert(index, who));
		}

		/// Renounce one's intention to be a candidate for the next election round. 3 potential
		/// outcomes exist:
		/// - `origin` is a candidate and not elected in any set. In this case, the bond is
		///   unreserved, returned and origin is removed as a candidate.
		/// - `origin` is a current runner up. In this case, the bond is unreserved, returned and
		///   origin is removed as a runner.
		/// - `origin` is a current member. In this case, the bond is unreserved and origin is
		///   removed as a member, consequently not being a candidate for the next round anymore.
		///   Similar to [`remove_voter`], if replacement runners exists, they are immediately used.
		#[weight = SimpleDispatchInfo::FixedOperational(2_000_000)]
		fn renounce_candidacy(origin) {
			let who = ensure_signed(origin)?;

			// NOTE: this function attempts the 3 conditions (being a candidate, member, runner) and
			// fails if none are matched. Unlike other Palette functions and modules where checks
			// happen first and then execution happens, this function is written the other way
			// around. The main intention is that reading all of the candidates, members and runners
			// from storage is expensive. Furthermore, we know (soft proof) that they are always
			// mutually exclusive. Hence, we try one, and only then decode more storage.

			if let Ok(_replacement) = Self::remove_and_replace_member(&who) {
				T::Currency::unreserve(&who, T::CandidacyBond::get());
				Self::deposit_event(RawEvent::MemberRenounced(who.clone()));

				// safety guard to make sure we do only one arm. Better to read runners later.
				return Ok(());
			}

			let mut runners_up_with_stake = Self::runners_up();
			if let Some(index) = runners_up_with_stake.iter()
				.position(|(ref r, ref _s)| r == &who)
			{
				runners_up_with_stake.remove(index);
				// unreserve the bond
				T::Currency::unreserve(&who, T::CandidacyBond::get());
				// update storage.
				<RunnersUp<T>>::put(runners_up_with_stake);
				// safety guard to make sure we do only one arm. Better to read runners later.
				return Ok(());
			}

			let mut candidates = Self::candidates();
			if let Ok(index) = candidates.binary_search(&who) {
				candidates.remove(index);
				// unreserve the bond
				T::Currency::unreserve(&who, T::CandidacyBond::get());
				// update storage.
				<Candidates<T>>::put(candidates);
				// safety guard to make sure we do only one arm. Better to read runners later.
				return Ok(());
			}

			Err(Error::<T>::InvalidOrigin)?
		}

		/// Remove a particular member from the set. This is effective immediately and the bond of
		/// the outgoing member is slashed.
		///
		/// If a runner-up is available, then the best runner-up will be removed and replaces the
		/// outgoing member. Otherwise, a new phragmen round is started.
		///
		/// Note that this does not affect the designated block number of the next election.
		///
		/// # <weight>
		/// #### State
		/// Reads: O(do_phragmen)
		/// Writes: O(do_phragmen)
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedOperational(2_000_000)]
		fn remove_member(origin, who: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;

			Self::remove_and_replace_member(&who).map(|had_replacement| {
				let (imbalance, _) = T::Currency::slash_reserved(&who, T::CandidacyBond::get());
				T::KickedMember::on_unbalanced(imbalance);
				Self::deposit_event(RawEvent::MemberKicked(who.clone()));

				if !had_replacement {
					Self::do_phragmen();
				}
			})
		}

		/// What to do at the end of each block. Checks if an election needs to happen or not.
		fn on_initialize(n: T::BlockNumber) {
			if let Err(e) = Self::end_block(n) {
				print("Guru meditation");
				print(e);
			}
		}
	}
}

decl_event!(
	pub enum Event<T> where
		Balance = BalanceOf<T>,
		<T as frame_system::Trait>::AccountId,
	{
		/// A new term with new members. This indicates that enough candidates existed, not that
		/// enough have has been elected. The inner value must be examined for this purpose.
		NewTerm(Vec<(AccountId, Balance)>),
		/// No (or not enough) candidates existed for this round.
		EmptyTerm,
		/// A member has been removed. This should always be followed by either `NewTerm` ot
		/// `EmptyTerm`.
		MemberKicked(AccountId),
		/// A member has renounced their candidacy.
		MemberRenounced(AccountId),
		/// A voter (first element) was reported (byt the second element) with the the report being
		/// successful or not (third element).
		VoterReported(AccountId, AccountId, bool),
	}
);

impl<T: Trait> Module<T> {
	/// Attempts to remove a member `who`. If a runner up exists, it is used as the replacement.
	/// Otherwise, `Ok(false)` is returned to signal the caller.
	///
	/// In both cases, [`Members`], [`ElectionRounds`] and [`RunnersUp`] storage are updated
	/// accordingly. Furthermore, the membership change is reported.
	///
	/// O(phragmen) in the worse case.
	fn remove_and_replace_member(who: &T::AccountId) -> Result<bool, DispatchError> {
		let mut members_with_stake = Self::members();
		if let Ok(index) = members_with_stake.binary_search_by(|(ref m, ref _s)| m.cmp(who)) {
			members_with_stake.remove(index);

			let next_up = <RunnersUp<T>>::mutate(|runners_up| runners_up.pop());
			let maybe_replacement = next_up.and_then(|(replacement, stake)|
				members_with_stake.binary_search_by(|(ref m, ref _s)| m.cmp(&replacement))
					.err()
					.map(|index| {
						members_with_stake.insert(index, (replacement.clone(), stake));
						replacement
					})
			);

			<Members<T>>::put(&members_with_stake);
			let members = members_with_stake.into_iter().map(|m| m.0).collect::<Vec<_>>();
			let result = Ok(maybe_replacement.is_some());
			let old = [who.clone()];
			match maybe_replacement {
				Some(new) => T::ChangeMembers::change_members_sorted(&[new], &old, &members),
				None => T::ChangeMembers::change_members_sorted(&[], &old, &members),
			}
			result
		} else {
			Err(Error::<T>::NotMember)?
		}
	}

	/// Check if `who` is a candidate. It returns the insert index if the element does not exists as
	/// an error.
	///
	/// State: O(LogN) given N candidates.
	fn is_candidate(who: &T::AccountId) -> Result<(), usize> {
		Self::candidates().binary_search(who).map(|_| ())
	}

	/// Check if `who` is a voter. It may or may not be a _current_ one.
	///
	/// State: O(1).
	fn is_voter(who: &T::AccountId) -> bool {
		<StakeOf<T>>::exists(who)
	}

	/// Check if `who` is currently an active member.
	///
	/// Limited number of members. Binary search. Constant time factor. O(1)
	fn is_member(who: &T::AccountId) -> bool {
		Self::members().binary_search_by(|(a, _b)| a.cmp(who)).is_ok()
	}

	/// Check if `who` is currently an active runner.
	///
	/// Limited number of runners-up. Binary search. Constant time factor. O(1)
	fn is_runner(who: &T::AccountId) -> bool {
		Self::runners_up().iter().position(|(a, _b)| a == who).is_some()
	}

	/// Returns number of desired members.
	fn desired_members() -> u32 {
		T::DesiredMembers::get()
	}

	/// Returns number of desired runners up.
	fn desired_runners_up() -> u32 {
		T::DesiredRunnersUp::get()
	}

	/// Returns the term duration
	fn term_duration() -> T::BlockNumber {
		T::TermDuration::get()
	}

	/// Get the members' account ids.
	fn members_ids() -> Vec<T::AccountId> {
		Self::members().into_iter().map(|(m, _)| m).collect::<Vec<T::AccountId>>()
	}

	/// The the runners' up account ids.
	fn runners_up_ids() -> Vec<T::AccountId> {
		Self::runners_up().into_iter().map(|(r, _)| r).collect::<Vec<T::AccountId>>()
	}

	/// Check if `who` is a defunct voter.
	///
	/// Note that false is returned if `who` is not a voter at all.
	///
	/// O(NLogM) with M candidates and `who` having voted for `N` of them.
	fn is_defunct_voter(who: &T::AccountId) -> bool {
		if Self::is_voter(who) {
			Self::votes_of(who)
				.iter()
				.all(|v| !Self::is_member(v) && !Self::is_runner(v) && !Self::is_candidate(v).is_ok())
		} else {
			false
		}
	}

	/// Remove a certain someone as a voter.
	///
	/// This will clean always clean the storage associated with the voter, and remove the balance
	/// lock. Optionally, it would also return the reserved voting bond if indicated by `unreserve`.
	fn do_remove_voter(who: &T::AccountId, unreserve: bool) {
		// remove storage and lock.
		<VotesOf<T>>::remove(who);
		<StakeOf<T>>::remove(who);
		T::Currency::remove_lock(MODULE_ID, who);

		if unreserve {
			T::Currency::unreserve(who, T::VotingBond::get());
		}
	}

	/// The locked stake of a voter.
	fn locked_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		Self::stake_of(who)
	}

	/// Check there's nothing to do this block.
	///
	/// Runs phragmen election and cleans all the previous candidate state. The voter state is NOT
	/// cleaned and voters must themselves submit a transaction to retract.
	fn end_block(block_number: T::BlockNumber) -> DispatchResult {
		if !Self::term_duration().is_zero() {
			if (block_number % Self::term_duration()).is_zero() {
				Self::do_phragmen();
			}
		}
		Ok(())
	}

	/// Run the phragmen election with all required side processes and state updates.
	///
	/// Calls the appropriate `ChangeMembers` function variant internally.
	///
	/// # <weight>
	/// #### State
	/// Reads: O(C + V*E) where C = candidates, V voters and E votes per voter exits.
	/// Writes: O(M + R) with M desired members and R runners_up.
	/// # </weight>
	fn do_phragmen() {
		let desired_seats = Self::desired_members() as usize;
		let desired_runners_up = Self::desired_runners_up() as usize;
		let num_to_elect = desired_runners_up + desired_seats;

		let mut candidates = Self::candidates();
		// candidates who explicitly called `submit_candidacy`. Only these folks are at the risk of
		// losing their bond.
		let exposed_candidates = candidates.clone();
		// current members are always a candidate for the next round as well.
		// this is guaranteed to not create any duplicates.
		candidates.append(&mut Self::members_ids());
		// previous runners_up are also always candidates for the next round.
		candidates.append(&mut Self::runners_up_ids());

		let voters_and_votes = <VotesOf<T>>::enumerate()
			.map(|(v, i)| (v, i))
			.collect::<Vec<(T::AccountId, Vec<T::AccountId>)>>();
		let maybe_phragmen_result = sp_phragmen::elect::<_, _, _, T::CurrencyToVote>(
			num_to_elect,
			0,
			candidates,
			voters_and_votes,
			Self::locked_stake_of,
		);

		if let Some(phragmen_result) = maybe_phragmen_result {
			let old_members_ids = <Members<T>>::take().into_iter()
				.map(|(m, _)| m)
				.collect::<Vec<T::AccountId>>();
			let old_runners_up_ids = <RunnersUp<T>>::take().into_iter()
				.map(|(r, _)| r)
				.collect::<Vec<T::AccountId>>();

			// filter out those who had literally no votes at all.
			// AUDIT/NOTE: the need to do this is because all candidates, even those who have no
			// vote are still considered by phragmen and when good candidates are scarce, then these
			// cheap ones might get elected. We might actually want to remove the filter and allow
			// zero-voted candidates to also make it to the membership set.
			let new_set_with_approval = phragmen_result.winners;
			let new_set = new_set_with_approval
				.into_iter()
				.filter_map(|(m, a)| if a.is_zero() { None } else { Some(m) } )
				.collect::<Vec<T::AccountId>>();

			let support_map = sp_phragmen::build_support_map::<_, _, _, T::CurrencyToVote>(
				&new_set,
				&phragmen_result.assignments,
				Self::locked_stake_of,
			);

			let to_balance = |e: ExtendedBalance|
				<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(e);
			let new_set_with_stake = new_set
				.into_iter()
				.map(|ref m| {
					let support = support_map.get(m)
						.expect(
							"entire new_set was given to build_support_map; en entry must be \
							created for each item; qed"
						);
					(m.clone(), to_balance(support.total))
				})
				.collect::<Vec<(T::AccountId, BalanceOf<T>)>>();

			// split new set into winners and runners up.
			let split_point = desired_seats.min(new_set_with_stake.len());
			let mut new_members = (&new_set_with_stake[..split_point]).to_vec();

			// save the runners up as-is. They are sorted based on desirability.
			// sort and save the members.
			new_members.sort_by(|i, j| i.0.cmp(&j.0));

			// new_members_ids is sorted by account id.
			let new_members_ids = new_members
				.iter()
				.map(|(m, _)| m.clone())
				.collect::<Vec<T::AccountId>>();

			let new_runners_up = &new_set_with_stake[split_point..]
				.into_iter()
				.cloned()
				.rev()
				.collect::<Vec<(T::AccountId, BalanceOf<T>)>>();
			// new_runners_up remains sorted by desirability.
			let new_runners_up_ids = new_runners_up
				.iter()
				.map(|(r, _)| r.clone())
				.collect::<Vec<T::AccountId>>();

			// report member changes. We compute diff because we need the outgoing list.
			let (incoming, outgoing) = T::ChangeMembers::compute_members_diff(
				&new_members_ids,
				&old_members_ids,
			);
			T::ChangeMembers::change_members_sorted(
				&incoming,
				&outgoing.clone(),
				&new_members_ids,
			);

			// outgoing candidates lose their bond.
			let mut to_burn_bond = outgoing.to_vec();

			// compute the outgoing of runners up as well and append them to the `to_burn_bond`
			{
				let (_, outgoing) = T::ChangeMembers::compute_members_diff(
					&new_runners_up_ids,
					&old_runners_up_ids,
				);
				to_burn_bond.extend(outgoing);
			}

			// Burn loser bond. members list is sorted. O(NLogM) (N candidates, M members)
			// runner up list is not sorted. O(K*N) given K runner ups. Overall: O(NLogM + N*K)
			// both the member and runner counts are bounded.
			exposed_candidates.into_iter().for_each(|c| {
				// any candidate who is not a member and not a runner up.
				if new_members.binary_search_by_key(&c, |(m, _)| m.clone()).is_err()
					&& !new_runners_up_ids.contains(&c)
				{
					let (imbalance, _) = T::Currency::slash_reserved(&c, T::CandidacyBond::get());
					T::LoserCandidate::on_unbalanced(imbalance);
				}
			});

			// Burn outgoing bonds
			to_burn_bond.into_iter().for_each(|x| {
				let (imbalance, _) = T::Currency::slash_reserved(&x, T::CandidacyBond::get());
				T::LoserCandidate::on_unbalanced(imbalance);
			});

			<Members<T>>::put(&new_members);
			<RunnersUp<T>>::put(new_runners_up);

			Self::deposit_event(RawEvent::NewTerm(new_members.clone().to_vec()));
		} else {
			Self::deposit_event(RawEvent::EmptyTerm);
		}

		// clean candidates.
		<Candidates<T>>::kill();

		ElectionRounds::mutate(|v| *v += 1);
	}
}

impl<T: Trait> Contains<T::AccountId> for Module<T> {
	fn contains(who: &T::AccountId) -> bool {
		Self::is_member(who)
	}
	fn sorted_members() -> Vec<T::AccountId> { Self::members_ids() }
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::cell::RefCell;
	use frame_support::{assert_ok, assert_noop, parameter_types, weights::Weight};
	use substrate_test_utils::assert_eq_uvec;
	use sp_core::H256;
	use sp_runtime::{
		Perbill, testing::Header, BuildStorage,
		traits::{BlakeTwo256, IdentityLookup, Block as BlockT},
	};
	use crate as elections;
	use frame_system as system;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
		pub const CreationFee: u64 = 0;
	}

	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnNewAccount = ();
		type OnReapAccount = System;
		type Event = Event;
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type CreationFee = CreationFee;
	}

	parameter_types! {
		pub const CandidacyBond: u64 = 3;
	}

	thread_local! {
		static VOTING_BOND: RefCell<u64> = RefCell::new(2);
		static DESIRED_MEMBERS: RefCell<u32> = RefCell::new(2);
		static DESIRED_RUNNERS_UP: RefCell<u32> = RefCell::new(2);
		static TERM_DURATION: RefCell<u64> = RefCell::new(5);
	}

	pub struct VotingBond;
	impl Get<u64> for VotingBond {
		fn get() -> u64 { VOTING_BOND.with(|v| *v.borrow()) }
	}

	pub struct DesiredMembers;
	impl Get<u32> for DesiredMembers {
		fn get() -> u32 { DESIRED_MEMBERS.with(|v| *v.borrow()) }
	}

	pub struct DesiredRunnersUp;
	impl Get<u32> for DesiredRunnersUp {
		fn get() -> u32 { DESIRED_RUNNERS_UP.with(|v| *v.borrow()) }
	}

	pub struct TermDuration;
	impl Get<u64> for TermDuration {
		fn get() -> u64 { TERM_DURATION.with(|v| *v.borrow()) }
	}

	thread_local! {
		pub static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct TestChangeMembers;
	impl ChangeMembers<u64> for TestChangeMembers {
		fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
			// new, incoming, outgoing must be sorted.
			let mut new_sorted = new.to_vec();
			new_sorted.sort();
			assert_eq!(new, &new_sorted[..]);

			let mut incoming_sorted = incoming.to_vec();
			incoming_sorted.sort();
			assert_eq!(incoming, &incoming_sorted[..]);

			let mut outgoing_sorted = outgoing.to_vec();
			outgoing_sorted.sort();
			assert_eq!(outgoing, &outgoing_sorted[..]);

			// incoming and outgoing must be disjoint
			for x in incoming.iter() {
				assert!(outgoing.binary_search(x).is_err());
			}

			let mut old_plus_incoming = MEMBERS.with(|m| m.borrow().to_vec());
			old_plus_incoming.extend_from_slice(incoming);
			old_plus_incoming.sort();

			let mut new_plus_outgoing = new.to_vec();
			new_plus_outgoing.extend_from_slice(outgoing);
			new_plus_outgoing.sort();

			assert_eq!(old_plus_incoming, new_plus_outgoing);

			MEMBERS.with(|m| *m.borrow_mut() = new.to_vec());
		}
	}

	/// Simple structure that exposes how u64 currency can be represented as... u64.
	pub struct CurrencyToVoteHandler;
	impl Convert<u64, u64> for CurrencyToVoteHandler {
		fn convert(x: u64) -> u64 { x }
	}
	impl Convert<u128, u64> for CurrencyToVoteHandler {
		fn convert(x: u128) -> u64 {
			x as u64
		}
	}

	impl Trait for Test {
		type Event = Event;
		type Currency = Balances;
		type CurrencyToVote = CurrencyToVoteHandler;
		type ChangeMembers = TestChangeMembers;
		type CandidacyBond = CandidacyBond;
		type VotingBond = VotingBond;
		type TermDuration = TermDuration;
		type DesiredMembers = DesiredMembers;
		type DesiredRunnersUp = DesiredRunnersUp;
		type LoserCandidate = ();
		type KickedMember = ();
		type BadReport = ();
	}

	pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
	pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: system::{Module, Call, Event},
			Balances: pallet_balances::{Module, Call, Event<T>, Config<T>},
			Elections: elections::{Module, Call, Event<T>},
		}
	);

	pub struct ExtBuilder {
		balance_factor: u64,
		voter_bond: u64,
		term_duration: u64,
		desired_runners_up: u32,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				balance_factor: 1,
				voter_bond: 2,
				desired_runners_up: 0,
				term_duration: 5,
			}
		}
	}

	impl ExtBuilder {
		pub fn voter_bond(mut self, fee: u64) -> Self {
			self.voter_bond = fee;
			self
		}
		pub fn desired_runners_up(mut self, count: u32) -> Self {
			self.desired_runners_up = count;
			self
		}
		pub fn term_duration(mut self, duration: u64) -> Self {
			self.term_duration = duration;
			self
		}
		pub fn build(self) -> sp_io::TestExternalities {
			VOTING_BOND.with(|v| *v.borrow_mut() = self.voter_bond);
			TERM_DURATION.with(|v| *v.borrow_mut() = self.term_duration);
			DESIRED_RUNNERS_UP.with(|v| *v.borrow_mut() = self.desired_runners_up);
			GenesisConfig {
				pallet_balances: Some(pallet_balances::GenesisConfig::<Test>{
					balances: vec![
						(1, 10 * self.balance_factor),
						(2, 20 * self.balance_factor),
						(3, 30 * self.balance_factor),
						(4, 40 * self.balance_factor),
						(5, 50 * self.balance_factor),
						(6, 60 * self.balance_factor)
					],
				}),
			}.build_storage().unwrap().into()
		}
	}

	fn all_voters() -> Vec<u64> {
		<VotesOf<Test>>::enumerate().map(|(v, _)| v).collect::<Vec<u64>>()
	}

	fn balances(who: &u64) -> (u64, u64) {
		(Balances::free_balance(who), Balances::reserved_balance(who))
	}

	fn has_lock(who: &u64) -> u64 {
		let lock = Balances::locks(who)[0].clone();
		assert_eq!(lock.id, MODULE_ID);
		lock.amount
	}

	#[test]
	fn params_should_work() {
		ExtBuilder::default().build().execute_with(|| {
			System::set_block_number(1);
			assert_eq!(Elections::desired_members(), 2);
			assert_eq!(Elections::term_duration(), 5);
			assert_eq!(Elections::election_rounds(), 0);

			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::runners_up(), vec![]);

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(<Candidates<Test>>::decode_len().unwrap(), 0);
			assert!(Elections::is_candidate(&1).is_err());

			assert_eq!(all_voters(), vec![]);
			assert_eq!(Elections::votes_of(&1), vec![]);
		});
	}

	#[test]
	fn term_duration_zero_is_passive() {
		ExtBuilder::default()
			.term_duration(0)
			.build()
			.execute_with(||
		{
			System::set_block_number(1);
			assert_eq!(Elections::term_duration(), 0);
			assert_eq!(Elections::desired_members(), 2);
			assert_eq!(Elections::election_rounds(), 0);

			assert_eq!(Elections::members_ids(), vec![]);
			assert_eq!(Elections::runners_up(), vec![]);
			assert_eq!(Elections::candidates(), vec![]);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![]);
			assert_eq!(Elections::runners_up(), vec![]);
			assert_eq!(Elections::candidates(), vec![]);
		});
	}

	#[test]
	fn simple_candidate_submission_should_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert!(Elections::is_candidate(&1).is_err());
			assert!(Elections::is_candidate(&2).is_err());

			assert_eq!(balances(&1), (10, 0));
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_eq!(balances(&1), (7, 3));

			assert_eq!(Elections::candidates(), vec![1]);

			assert!(Elections::is_candidate(&1).is_ok());
			assert!(Elections::is_candidate(&2).is_err());

			assert_eq!(balances(&2), (20, 0));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_eq!(balances(&2), (17, 3));

			assert_eq!(Elections::candidates(), vec![1, 2]);

			assert!(Elections::is_candidate(&1).is_ok());
			assert!(Elections::is_candidate(&2).is_ok());
		});
	}

	#[test]
	fn simple_candidate_submission_with_no_votes_should_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());

			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert!(Elections::is_candidate(&1).is_ok());
			assert!(Elections::is_candidate(&2).is_ok());
			assert_eq!(Elections::candidates(), vec![1, 2]);

			assert_eq!(Elections::members_ids(), vec![]);
			assert_eq!(Elections::runners_up(), vec![]);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert!(Elections::is_candidate(&1).is_err());
			assert!(Elections::is_candidate(&2).is_err());
			assert_eq!(Elections::candidates(), vec![]);

			assert_eq!(Elections::members_ids(), vec![]);
			assert_eq!(Elections::runners_up(), vec![]);
		});
	}

	#[test]
	fn dupe_candidate_submission_should_not_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_eq!(Elections::candidates(), vec![1]);
			assert_noop!(
				Elections::submit_candidacy(Origin::signed(1)),
				Error::<Test>::DuplicatedCandidate,
			);
		});
	}

	#[test]
	fn member_candidacy_submission_should_not_work() {
		// critically important to make sure that outgoing candidates and losers are not mixed up.
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![5]);
			assert_eq!(Elections::runners_up(), vec![]);
			assert_eq!(Elections::candidates(), vec![]);

			assert_noop!(
				Elections::submit_candidacy(Origin::signed(5)),
				Error::<Test>::MemberSubmit,
			);
		});
	}

	#[test]
	fn runner_candidate_submission_should_not_work() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5, 4], 20));
			assert_ok!(Elections::vote(Origin::signed(1), vec![3], 10));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![3]);

			assert_noop!(
				Elections::submit_candidacy(Origin::signed(3)),
				Error::<Test>::RunnerSubmit,
			);
		});
	}

	#[test]
	fn poor_candidate_submission_should_not_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_noop!(
				Elections::submit_candidacy(Origin::signed(7)),
				Error::<Test>::InsufficientCandidateFunds,
			);
		});
	}

	#[test]
	fn simple_voting_should_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_eq!(balances(&2), (20, 0));

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_eq!(balances(&2), (18, 2));
			assert_eq!(has_lock(&2), 20);
		});
	}

	#[test]
	fn can_vote_with_custom_stake() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_eq!(balances(&2), (20, 0));

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 12));

			assert_eq!(balances(&2), (18, 2));
			assert_eq!(has_lock(&2), 12);
		});
	}

	#[test]
	fn can_update_votes_and_stake() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(balances(&2), (20, 0));

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_eq!(balances(&2), (18, 2));
			assert_eq!(has_lock(&2), 20);
			assert_eq!(Elections::stake_of(2), 20);

			// can update; different stake; different lock and reserve.
			assert_ok!(Elections::vote(Origin::signed(2), vec![5, 4], 15));
			assert_eq!(balances(&2), (18, 2));
			assert_eq!(has_lock(&2), 15);
			assert_eq!(Elections::stake_of(2), 15);
		});
	}

	#[test]
	fn cannot_vote_for_no_candidate() {
		ExtBuilder::default().build().execute_with(|| {
			assert_noop!(
				Elections::vote(Origin::signed(2), vec![], 20),
				Error::<Test>::UnableToVote,
			);
		});
	}

	#[test]
	fn can_vote_for_old_members_even_when_no_new_candidates() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![4, 5], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::candidates(), vec![]);

			assert_ok!(Elections::vote(Origin::signed(3), vec![4, 5], 10));
		});
	}

	#[test]
	fn cannot_vote_for_more_than_candidates() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_noop!(
				Elections::vote(Origin::signed(2), vec![10, 20, 30], 20),
				Error::<Test>::TooManyVotes,
			);
		});
	}

	#[test]
	fn cannot_vote_for_less_than_ed() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_noop!(
				Elections::vote(Origin::signed(2), vec![4], 1),
				Error::<Test>::LowBalance,
			);
		})
	}

	#[test]
	fn can_vote_for_more_than_total_balance_but_moot() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![4, 5], 30));
			// you can lie but won't get away with it.
			assert_eq!(Elections::stake_of(2), 20);
			assert_eq!(has_lock(&2), 20);
		});
	}

	#[test]
	fn remove_voter_should_work() {
		ExtBuilder::default().voter_bond(8).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5], 30));

			assert_eq_uvec!(all_voters(), vec![2, 3]);
			assert_eq!(Elections::stake_of(2), 20);
			assert_eq!(Elections::stake_of(3), 30);
			assert_eq!(Elections::votes_of(2), vec![5]);
			assert_eq!(Elections::votes_of(3), vec![5]);

			assert_ok!(Elections::remove_voter(Origin::signed(2)));

			assert_eq_uvec!(all_voters(), vec![3]);
			assert_eq!(Elections::votes_of(2), vec![]);
			assert_eq!(Elections::stake_of(2), 0);

			assert_eq!(balances(&2), (20, 0));
			assert_eq!(Balances::locks(&2).len(), 0);
		});
	}

	#[test]
	fn non_voter_remove_should_not_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_noop!(Elections::remove_voter(Origin::signed(3)), Error::<Test>::MustBeVoter);
		});
	}

	#[test]
	fn dupe_remove_should_fail() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_ok!(Elections::remove_voter(Origin::signed(2)));
			assert_eq!(all_voters(), vec![]);

			assert_noop!(Elections::remove_voter(Origin::signed(2)), Error::<Test>::MustBeVoter);
		});
	}

	#[test]
	fn removed_voter_should_not_be_counted() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_ok!(Elections::remove_voter(Origin::signed(4)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![3, 5]);
		});
	}

	#[test]
	fn reporter_must_be_voter() {
		ExtBuilder::default().build().execute_with(|| {
			assert_noop!(
				Elections::report_defunct_voter(Origin::signed(1), 2),
				Error::<Test>::MustBeVoter,
			);
		});
	}

	#[test]
	fn can_detect_defunct_voter() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(6)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(2), vec![4, 5], 20));
			assert_ok!(Elections::vote(Origin::signed(6), vec![6], 30));
			// will be soon a defunct voter.
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![6]);
			assert_eq!(Elections::candidates(), vec![]);

			// all of them have a member or runner-up that they voted for.
			assert_eq!(Elections::is_defunct_voter(&5), false);
			assert_eq!(Elections::is_defunct_voter(&4), false);
			assert_eq!(Elections::is_defunct_voter(&2), false);
			assert_eq!(Elections::is_defunct_voter(&6), false);

			// defunct
			assert_eq!(Elections::is_defunct_voter(&3), true);

			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_ok!(Elections::vote(Origin::signed(1), vec![1], 10));

			// has a candidate voted for.
			assert_eq!(Elections::is_defunct_voter(&1), false);

		});
	}

	#[test]
	fn report_voter_should_work_and_earn_reward() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(2), vec![4, 5], 20));
			// will be soon a defunct voter.
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::candidates(), vec![]);

			assert_eq!(balances(&3), (28, 2));
			assert_eq!(balances(&5), (45, 5));

			assert_ok!(Elections::report_defunct_voter(Origin::signed(5), 3));
			assert_eq!(
				System::events()[1].event,
				Event::elections(RawEvent::VoterReported(3, 5, true))
			);

			assert_eq!(balances(&3), (28, 0));
			assert_eq!(balances(&5), (47, 5));
		});
	}

	#[test]
	fn report_voter_should_slash_when_bad_report() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::candidates(), vec![]);

			assert_eq!(balances(&4), (35, 5));
			assert_eq!(balances(&5), (45, 5));

			assert_ok!(Elections::report_defunct_voter(Origin::signed(5), 4));
			assert_eq!(
				System::events()[1].event,
				Event::elections(RawEvent::VoterReported(4, 5, false))
			);

			assert_eq!(balances(&4), (35, 5));
			assert_eq!(balances(&5), (45, 3));
		});
	}


	#[test]
	fn simple_voting_rounds_should_work() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 15));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_eq_uvec!(all_voters(), vec![2, 3, 4]);

			assert_eq!(Elections::votes_of(2), vec![5]);
			assert_eq!(Elections::votes_of(3), vec![3]);
			assert_eq!(Elections::votes_of(4), vec![4]);

			assert_eq!(Elections::candidates(), vec![3, 4, 5]);
			assert_eq!(<Candidates<Test>>::decode_len().unwrap(), 3);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![(3, 30), (5, 20)]);
			assert_eq!(Elections::runners_up(), vec![]);
			assert_eq_uvec!(all_voters(), vec![2, 3, 4]);
			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(<Candidates<Test>>::decode_len().unwrap(), 0);

			assert_eq!(Elections::election_rounds(), 1);
		});
	}

	#[test]
	fn defunct_voter_will_be_counted() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			// This guy's vote is pointless for this round.
			assert_ok!(Elections::vote(Origin::signed(3), vec![4], 30));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![(5, 50)]);
			assert_eq!(Elections::election_rounds(), 1);

			// but now it has a valid target.
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			// candidate 4 is affected by an old vote.
			assert_eq!(Elections::members(), vec![(4, 30), (5, 50)]);
			assert_eq!(Elections::election_rounds(), 2);
			assert_eq_uvec!(all_voters(), vec![3, 5]);
		});
	}

	#[test]
	fn only_desired_seats_are_chosen() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::election_rounds(), 1);
			assert_eq!(Elections::members_ids(), vec![4, 5]);
		});
	}

	#[test]
	fn phragmen_should_not_self_vote() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::election_rounds(), 1);
			assert_eq!(Elections::members_ids(), vec![]);
		});
	}

	#[test]
	fn runners_up_should_be_kept() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![2], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![5], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![4], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			// sorted based on account id.
			assert_eq!(Elections::members_ids(), vec![4, 5]);
			// sorted based on merit (least -> most)
			assert_eq!(Elections::runners_up_ids(), vec![3, 2]);

			// runner ups are still locked.
			assert_eq!(balances(&4), (35, 5));
			assert_eq!(balances(&5), (45, 5));
			assert_eq!(balances(&3), (25, 5));
		});
	}

	#[test]
	fn runners_up_should_be_next_candidates() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![(4, 40), (5, 50)]);
			assert_eq!(Elections::runners_up(), vec![(2, 20), (3, 30)]);

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 15));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![(3, 30), (4, 40)]);
			assert_eq!(Elections::runners_up(), vec![(5, 15), (2, 20)]);
		});
	}

	#[test]
	fn runners_up_lose_bond_once_outgoing() {
		ExtBuilder::default().desired_runners_up(1).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![2]);
			assert_eq!(balances(&2), (15, 5));

			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::runners_up_ids(), vec![3]);
			assert_eq!(balances(&2), (15, 2));
		});
	}

	#[test]
	fn members_lose_bond_once_outgoing() {
		ExtBuilder::default().build().execute_with(|| {
			assert_eq!(balances(&5), (50, 0));

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_eq!(balances(&5), (47, 3));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_eq!(balances(&5), (45, 5));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![5]);

			assert_ok!(Elections::remove_voter(Origin::signed(5)));
			assert_eq!(balances(&5), (47, 3));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![]);

			assert_eq!(balances(&5), (47, 0));
		});
	}

	#[test]
	fn losers_will_lose_the_bond() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![5], 40));

			assert_eq!(balances(&5), (47, 3));
			assert_eq!(balances(&3), (27, 3));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![5]);

			// winner
			assert_eq!(balances(&5), (47, 3));
			// loser
			assert_eq!(balances(&3), (27, 0));
		});
	}

	#[test]
	fn current_members_are_always_next_candidate() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::election_rounds(), 1);

			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_ok!(Elections::remove_voter(Origin::signed(4)));

			// 5 will persist as candidates despite not being in the list.
			assert_eq!(Elections::candidates(), vec![2, 3]);

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			// 4 removed; 5 and 3 are the new best.
			assert_eq!(Elections::members_ids(), vec![3, 5]);
		});
	}

	#[test]
	fn election_state_is_uninterrupted() {
		// what I mean by uninterrupted:
		// given no input or stimulants the same members are re-elected.
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			let check_at_block = |b: u32| {
				System::set_block_number(b.into());
				assert_ok!(Elections::end_block(System::block_number()));
				// we keep re-electing the same folks.
				assert_eq!(Elections::members(), vec![(4, 40), (5, 50)]);
				assert_eq!(Elections::runners_up(), vec![(2, 20), (3, 30)]);
				// no new candidates but old members and runners-up are always added.
				assert_eq!(Elections::candidates(), vec![]);
				assert_eq!(Elections::election_rounds(), b / 5);
				assert_eq_uvec!(all_voters(), vec![2, 3, 4, 5]);
			};

			// this state will always persist when no further input is given.
			check_at_block(5);
			check_at_block(10);
			check_at_block(15);
			check_at_block(20);
		});
	}

	#[test]
	fn remove_members_triggers_election() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::election_rounds(), 1);

			// a new candidate
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_ok!(Elections::remove_member(Origin::ROOT, 4));

			assert_eq!(balances(&4), (35, 2)); // slashed
			assert_eq!(Elections::election_rounds(), 2); // new election round
			assert_eq!(Elections::members_ids(), vec![3, 5]); // new members
		});
	}

	#[test]
	fn seats_should_be_released_when_no_vote() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			assert_eq!(<Candidates<Test>>::decode_len().unwrap(), 3);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![3, 5]);
			assert_eq!(Elections::election_rounds(), 1);

			assert_ok!(Elections::remove_voter(Origin::signed(2)));
			assert_ok!(Elections::remove_voter(Origin::signed(3)));
			assert_ok!(Elections::remove_voter(Origin::signed(4)));
			assert_ok!(Elections::remove_voter(Origin::signed(5)));

			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![]);
			assert_eq!(Elections::election_rounds(), 2);
		});
	}

	#[test]
	fn incoming_outgoing_are_reported() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members_ids(), vec![4, 5]);

			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			// 5 will change their vote and becomes an `outgoing`
			assert_ok!(Elections::vote(Origin::signed(5), vec![4], 8));
			// 4 will stay in the set
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			// 3 will become a winner
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			// these two are losers.
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(1), vec![1], 10));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			// 3, 4 are new members, must still be bonded, nothing slashed.
			assert_eq!(Elections::members(), vec![(3, 30), (4, 48)]);
			assert_eq!(balances(&3), (25, 5));
			assert_eq!(balances(&4), (35, 5));

			// 1 is a loser, slashed by 3.
			assert_eq!(balances(&1), (5, 2));

			// 5 is an outgoing loser. will also get slashed.
			assert_eq!(balances(&5), (45, 2));

			assert_eq!(
				System::events()[0].event,
				Event::elections(RawEvent::NewTerm(vec![(4, 40), (5, 50)])),
			);
		})
	}

	#[test]
	fn invalid_votes_are_moot() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![10], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq_uvec!(Elections::members_ids(), vec![3, 4]);
			assert_eq!(Elections::election_rounds(), 1);
		});
	}

	#[test]
	fn members_are_sorted_based_on_id_runners_on_merit() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![2], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![5], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![4], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			// id: low -> high.
			assert_eq!(Elections::members(), vec![(4, 50), (5, 40)]);
			// merit: low -> high.
			assert_eq!(Elections::runners_up(), vec![(3, 20), (2, 30)]);
		});
	}

	#[test]
	fn candidates_are_sorted() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_eq!(Elections::candidates(), vec![3, 5]);

			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::renounce_candidacy(Origin::signed(3)));

			assert_eq!(Elections::candidates(), vec![2, 4, 5]);
		})
	}

	#[test]
	fn runner_up_replacement_maintains_members_order() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![2], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![2, 4]);
			assert_ok!(Elections::remove_member(Origin::ROOT, 2));
			assert_eq!(Elections::members_ids(), vec![4, 5]);
		});
	}

	#[test]
	fn runner_up_replacement_works_when_out_of_order() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![2], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![2, 4]);
			assert_ok!(Elections::renounce_candidacy(Origin::signed(3)));
		});
	}

	#[test]
	fn can_renounce_candidacy_member_with_runners_bond_is_refunded() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![2, 3]);

			assert_ok!(Elections::renounce_candidacy(Origin::signed(4)));
			assert_eq!(balances(&4), (38, 2)); // 2 is voting bond.

			assert_eq!(Elections::members_ids(), vec![3, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![2]);
		})
	}

	#[test]
	fn can_renounce_candidacy_member_without_runners_bond_is_refunded() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![]);
			assert_eq!(Elections::candidates(), vec![2, 3]);

			assert_ok!(Elections::renounce_candidacy(Origin::signed(4)));
			assert_eq!(balances(&4), (38, 2)); // 2 is voting bond.

			// no replacement
			assert_eq!(Elections::members_ids(), vec![5]);
			assert_eq!(Elections::runners_up_ids(), vec![]);
			// still candidate
			assert_eq!(Elections::candidates(), vec![2, 3]);
		})
	}

	#[test]
	fn can_renounce_candidacy_runner() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![4], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![5], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![2, 3]);

			assert_ok!(Elections::renounce_candidacy(Origin::signed(3)));
			assert_eq!(balances(&3), (28, 2)); // 2 is voting bond.

			assert_eq!(Elections::members_ids(), vec![4, 5]);
			assert_eq!(Elections::runners_up_ids(), vec![2]);
		})
	}

	#[test]
	fn can_renounce_candidacy_candidate() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_eq!(balances(&5), (47, 3));
			assert_eq!(Elections::candidates(), vec![5]);

			assert_ok!(Elections::renounce_candidacy(Origin::signed(5)));
			assert_eq!(balances(&5), (50, 0));
			assert_eq!(Elections::candidates(), vec![]);
		})
	}

	#[test]
	fn wrong_renounce_candidacy_should_fail() {
		ExtBuilder::default().build().execute_with(|| {
			assert_noop!(
				Elections::renounce_candidacy(Origin::signed(5)),
				Error::<Test>::InvalidOrigin,
			);
		})
	}

	#[test]
	fn behavior_with_dupe_candidate() {
		ExtBuilder::default().desired_runners_up(2).build().execute_with(|| {
			<Candidates<Test>>::put(vec![1, 1, 2, 3, 4]);

			assert_ok!(Elections::vote(Origin::signed(5), vec![1], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members_ids(), vec![1, 4]);
			assert_eq!(Elections::runners_up_ids(), vec![2, 3]);
			assert_eq!(Elections::candidates(), vec![]);
		})
	}
}
