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

//! # Society Module
//!
//! The Society module allows one or more initial accounts to create a membership society.
//!
//! An induction process can be customised for new members, allowing candidates to submit their
//! intention to become members and allowing current members to vote on candidates. Maintenance
//! or verification requirements on members can also be imposed.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use rstd::prelude::*;
use codec::{Encode, Decode};
use sr_primitives::{RandomNumberGenerator, Percent, Perbill, ModuleId, RuntimeDebug, traits::{
	EnsureOrigin, StaticLookup, AccountIdConversion, Saturating, Zero, IntegerSquareRoot,
}};
use support::{decl_error, decl_module, decl_storage, decl_event, dispatch::Result, traits::{
	Currency, ReservableCurrency, Randomness, Get, ChangeMembers,
	ExistenceRequirement::{KeepAlive, AllowDeath},
}};
use system::ensure_signed;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

const MODULE_ID: ModuleId = ModuleId(*b"py/socie");

/// The module's configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The currency type used for bidding.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// Something that provides randomness in the runtime.
	type Randomness: Randomness<Self::Hash>;

	/// The minimum amount of a deposit required for a bid to be made.
	type CandidateDeposit: Get<BalanceOf<Self>>;

	/// The proportion of the unpaid reward that gets deducted in the case that either a skeptic
	/// doesn't vote or someone votes in the wrong way.
	type WrongSideDeduction: Get<Percent>;

	/// The number of times a member may vote the wrong way (or not at all, when they are a skeptic)
	/// before they become suspended.
	type MaxStrikes: Get<u32>;

	/// The amount of incentive paid within each period. Doesn't include VoterTip.
	type PeriodSpend: Get<BalanceOf<Self>>;

	/// The receiver of the signal for when the members have changed.
	type MembershipChanged: ChangeMembers<Self::AccountId>;

	/// The number of blocks between periods.
	type Period: Get<Self::BlockNumber>;

	/// The maximum duration of the payout lock.
	type MaxLockDuration: Get<Self::BlockNumber>;
}

/// A vote by a member on a candidate application.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Vote {
	/// The member has been chosen to be skeptic and has not yet taken any action.
	Skeptic,
	/// The member has rejected the candidate's application.
	Reject,
	/// The member approves of the candidate's application.
	Approve,
}

/// Details of a payout given as a per-block linear "trickle".
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, Default)]
pub struct Payout<Balance, BlockNumber> {
	/// Total value of the payout.
	value: Balance,
	/// Block number at which the payout begins.
	begin: BlockNumber,
	/// Total number of blocks over which the payout is spread.
	duration: BlockNumber,
	/// Total value paid out so far.
	paid: Balance,
}

/// Number of strikes that a member has against them.
pub type StrikeCount = u32;

// This module's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as Fratority {
		/// The current bids.
		Bids: Vec<(BalanceOf<T>, T::AccountId)>;

		/// The current set of members, ordered.
		Members get(fn members) config(): Vec<T::AccountId>;

		/// The current set of candidates; bidders that are attempting to become members.
		Candidates: Vec<(BalanceOf<T>, T::AccountId)>;

		/// Amount of our account balance that is specifically for the next round's bid(s).
		Pot: BalanceOf<T>;

		/// The most primary from the most recently approved members.
		Head: T::AccountId;

		/// Double map from Candidate -> Voter -> (Maybe) Vote.
		Votes: double_map
			hasher(twox_64_concat) T::AccountId,
			twox_64_concat(T::AccountId)
		=> Option<Vote>;

		/// Pending payouts.
		Payouts: map T::AccountId => Option<Payout<BalanceOf<T>, T::BlockNumber>>;

		/// The ongoing number of losing votes cast by the member.
		Strikes: map T::AccountId => StrikeCount;
	}
}

// The module's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// Initializing events
		// this is needed only if you are using events in your module
		fn deposit_event() = default;

		/// Make a bid for entry.
		///
		/// Alters Bids (O(N) decode+encode, O(logN) search, <=2*O(N) write).
		///
		pub fn bid(origin, value: BalanceOf<T>) -> Result {
			const MAX_BID_COUNT: usize = 1000;

			let who = ensure_signed(origin)?;

			T::Currency::reserve(&who, T::CandidateDeposit::get())?;

			<Bids<T>>::mutate(|b| {
				match b.binary_search_by(|x| x.0.cmp(&value)) {
					Ok(pos) | Err(pos) => b.insert(pos, (value.clone(), who.clone())),
				}
				// Keep it reasonably small.
				if b.len() > MAX_BID_COUNT {
					let (_, popped) = b.pop().expect("b.len() > 1000; qed");
					let _unreserved = T::Currency::unreserve(&popped, T::CandidateDeposit::get());
					Self::deposit_event(RawEvent::AutoUnbid(popped));
				}
			});

			Self::deposit_event(RawEvent::Bid(who, value));
			Ok(())
		}

		fn unbid(origin, pos: u32) -> Result {
			let who = ensure_signed(origin)?;

			let pos = pos as usize;
			<Bids<T>>::mutate(|b|
				if pos < b.len() && b[pos].1 == who {
					b.remove(pos);
					Self::deposit_event(RawEvent::Unbid(who));
					Ok(())
				} else {
					Err("bad position")
//					Err(Error::BadPositionHint)
				}
			)
		}

		/// As a member, vote on an candidate.
		pub fn vote(origin, candidate: <T::Lookup as StaticLookup>::Source, approve: bool) {
			let voter = ensure_signed(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;
			let vote = if approve { Vote::Approve } else { Vote::Reject };
			<Votes<T>>::insert(candidate, voter, vote);
		}

		pub fn payout(origin) {
			let who = ensure_signed(origin)?;

			if let Some(payout) = <Payouts<T>>::get(&who) {
				let now = <system::Module<T>>::block_number();
				let elapsed = now.saturating_sub(payout.begin).min(payout.duration);
				let progress = Perbill::from_rational_approximation(elapsed, payout.duration);
				let new_paid = progress * payout.value;
				let payment = new_paid.saturating_sub(payout.paid);
				T::Currency::transfer(&Self::payouts(), &who, payment, KeepAlive)?;

				if payout.value == new_paid {
					// once we've paid everything, remove the record
					<Payouts<T>>::remove(who);
				} else {
					<Payouts<T>>::insert(who, Payout { paid: new_paid, .. payout });
				}
			}
		}

		fn on_initialize(n: T::BlockNumber) {
			if (n % T::Period::get()).is_zero() {
				Self::rotate_period();
			}
		}
	}
}

decl_error! {
	/// Errors for this module.
	pub enum Error {
		/// An incorrect position was provided.
		BadPositionHint,
	}
}

decl_event! {
	/// Events for this module.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
		Balance = BalanceOf<T>
	{
		/// A membership bid just happened. The given account is the candidate's ID and their offer
		/// is the second.
		Bid(AccountId, Balance),
		/// A candidate was dropped (due to an excess of bids in the system).
		AutoUnbid(AccountId),
		/// A candidate was dropped (by their request).
		Unbid(AccountId),
		/// A group of candidates have been inducted. The batch's primary is the first value, the
		/// batch in full is the second.
		Inducted(AccountId, Vec<AccountId>),
	}
}

impl<T: Trait> Module<T> {
	/// End the current period and begin a new one.
	fn rotate_period() {
		let phrase = b"fratority_rotation";

		let mut members = <Members<T>>::get();

		// we assume there's at least one member or this logic won't work.
		if members.is_empty() { return }

		let candidates = <Candidates<T>>::take();
		members.reserve(candidates.len());

		// we'll need a random seed here.
		let mut rng = <RandomNumberGenerator<T::Hashing>>::new(T::Randomness::random(phrase));

		let payout = Payout {
			begin: <system::Module<T>>::block_number(),
			duration: Self::lock_duration(members.len() as u32),
			.. Default::default()
		};

		let mut pot = <Pot<T>>::get();

		let mut rewardees = Vec::new();
		let mut total_approvals = 0;
		let mut total_slash = <BalanceOf<T>>::zero();
		let mut total_payouts = <BalanceOf<T>>::zero();

		let accepted = candidates.into_iter().filter_map(|(value, c)| {
			let mut approval_count = 0;
			let votes = members.iter()
				.filter_map(|m| <Votes<T>>::get(&c, m).map(|v| (v, m)))
				.inspect(|&(v, _)| if v == Vote::Approve { approval_count += 1 })
				.collect::<Vec<_>>();
			let accepted = rng.pick_item(&votes).map(|x| x.0) == Some(Vote::Approve);

			// collect together voters who voted the right way
			let matching_vote = if accepted { Vote::Approve } else { Vote::Reject };
			let mut bad_vote = |m: &T::AccountId| {
				// voter voted wrong way (or was just a lazy skeptic) then reduce their payout
				// and increase their strikes. after MaxStrikes then they go into suspension.
				if let Some(mut payout) = <Payouts<T>>::get(m) {
					let rest = payout.value.saturating_sub(payout.paid);
					let slash = T::WrongSideDeduction::get() * rest;
					payout.paid += slash;
					<Payouts<T>>::insert(m, &payout);
					total_slash += slash;
				}
				let strikes = <Strikes<T>>::mutate(m, |s| { *s += 1; *s });
				if strikes >= T::MaxStrikes::get() {
					Self::suspend_member(m);
				}
			};
			rewardees.extend(votes.into_iter()
				.filter_map(|(v, m)| if v == matching_vote { Some(m) } else { bad_vote(m); None })
				.cloned()
			);

			if accepted {
				total_approvals += approval_count;
				total_payouts += value;
				members.push(c.clone());
				<Payouts<T>>::insert(&c, Payout { value, .. payout });

				Some((c, total_approvals))
			} else {
				Self::suspend_candidate(&c);
				None
			}
		}).collect::<Vec<_>>();

		// Reward one of the voters who voted the right way.
		if !total_slash.is_zero() {
			if let Some(winner) = rng.pick_item(&rewardees) {
				// if we can't reward them, not much that can be done.
				Self::bump_payout(winner, total_slash);
			}
		}
		if !total_payouts.is_zero() {
			// remove payout from pot and shift needed funds to the payout account.
			pot = pot.saturating_sub(total_payouts);

			// this should never fail since we ensure the pot can afford the payouts in a previous
			// block, but there's not much we can do to recover if it fails anyway.
			let _ = T::Currency::transfer(&Self::account_id(), &Self::payouts(), total_payouts, AllowDeath);
		}

		// if at least one candidate was accepted...
		if !accepted.is_empty() {
			// select one as primary, randomly chosen from the accepted, weighted by approvals.
			let primary_point = rng.pick_usize(total_approvals - 1);
			let primary = accepted.iter().find(|e| e.1 > primary_point)
				.expect("e.1 of final item == total_approvals; \
					worst case find will always return that item; qed")
				.0.clone();
			let accounts = accepted.into_iter().map(|x| x.0).collect::<Vec<_>>();

			// then write everything back out, signal the changed membership and leave an event.
			members.sort();
			<Members<T>>::put(&members);
			<Head<T>>::put(&primary);

			T::MembershipChanged::change_members_sorted(&accounts, &[], &members);
			Self::deposit_event(RawEvent::Inducted(primary, accounts));
		}

		// Bump the pot by at most PeriodSpend, but less if there's not very much left in our
		// account.
		let unaccounted = T::Currency::free_balance(&Self::account_id()).saturating_sub(pot);
		pot += T::PeriodSpend::get().min(unaccounted / 2u8.into());

		// setup the candidates for the new intake
		let candidates = Self::take_selected(pot);
		<Candidates<T>>::put(&candidates);
		// initialise skeptics
		let pick_member = |_| rng.pick_item(&members[..]).expect("exited if members empty; qed");
		for skeptic in (0..members.len().integer_sqrt()).map(pick_member) {
			for (_, c) in candidates.iter() {
				<Votes<T>>::insert(c, skeptic, Vote::Skeptic);
			}
		}
	}

	/// Bump the payout amount of `who`, if there is any; if not, then just transfer directly.
	fn bump_payout(who: &T::AccountId, value: BalanceOf<T>) {
		if let Some(mut payout) = <Payouts<T>>::get(who) {
			payout.value += value;
			<Payouts<T>>::insert(who, payout);
		} else {
			let _ = T::Currency::transfer(&Self::payouts(), who, value, KeepAlive);
		}
	}

	fn suspend_member(who: &T::AccountId) {
		unimplemented!();
	}

	fn suspend_candidate(who: &T::AccountId) {
		unimplemented!();
	}

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		MODULE_ID.into_account()
	}

	/// The account ID of the payouts pot. This is where payouts are made from.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn payouts() -> T::AccountId {
		MODULE_ID.into_sub_account(b"payouts")
	}

	/// Return the duration of the lock, in blocks, with the given number of members.
	///
	/// This is a rather opaque calculation based on the formula here:
	/// https://www.desmos.com/calculator/9itkal1tce
	fn lock_duration(x: u32) -> T::BlockNumber {
		let lock_pc = 100 - 50_000 / (x + 500);
		Percent::from_percent(lock_pc as u8) * T::MaxLockDuration::get()
	}

	/// Get a selection of bidding accounts such that the total bids is no greater than `Pot`.
	///
	/// May be empty.
	pub fn take_selected(pot: BalanceOf<T>) -> Vec<(BalanceOf<T>, T::AccountId)> {
		// No more than 10 will be returned.
		const MAX_SELECTIONS: usize = 10;

		// Get the number of left-most bidders whose bids add up to less than `pot`.
		let mut bids = <Bids<T>>::get();
		let taken = bids.iter()
			.scan(<BalanceOf<T>>::zero(), |total, &(bid, ref who)| {
				*total = total.saturating_add(bid);
				Some((*total, who.clone()))
			})
			.take(MAX_SELECTIONS)
			.take_while(|x| pot >= x.0)
			.count();

		// No need to reset Bids if we're not taking anything.
		if taken > 0 {
			<Bids<T>>::put(&bids[taken..]);
		}
		bids.truncate(taken);
		bids
	}
}
