// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Voting Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! Pallet for managing actual voting in polls.

#![recursion_limit = "256"]
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::{
		fungible, Currency, Get, LockIdentifier, LockableCurrency, PollStatus, Polling,
		ReservableCurrency, WithdrawReasons,
	},
};
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Saturating, StaticLookup, Zero},
	ArithmeticError, Perbill,
};
use sp_std::prelude::*;

mod conviction;
mod types;
mod vote;
pub mod weights;

pub use self::{
	conviction::Conviction,
	pallet::*,
	types::{Delegations, Tally, UnvoteScope},
	vote::{AccountVote, Casting, Delegating, Vote, Voting},
	weights::WeightInfo,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

const CONVICTION_VOTING_ID: LockIdentifier = *b"pyconvot";

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;
type BalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type VotingOf<T, I = ()> = Voting<
	BalanceOf<T, I>,
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::BlockNumber,
	PollIndexOf<T, I>,
	<T as Config<I>>::MaxVotes,
>;
#[allow(dead_code)]
type DelegatingOf<T, I = ()> = Delegating<
	BalanceOf<T, I>,
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::BlockNumber,
>;
pub type TallyOf<T, I = ()> = Tally<BalanceOf<T, I>, <T as Config<I>>::MaxTurnout>;
pub type VotesOf<T, I = ()> = BalanceOf<T, I>;
type PollIndexOf<T, I = ()> = <<T as Config<I>>::Polls as Polling<TallyOf<T, I>>>::Index;
#[cfg(feature = "runtime-benchmarks")]
type IndexOf<T, I = ()> = <<T as Config<I>>::Polls as Polling<TallyOf<T, I>>>::Index;
type ClassOf<T, I = ()> = <<T as Config<I>>::Polls as Polling<TallyOf<T, I>>>::Class;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, traits::ClassCountOf};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config + Sized {
		// System level stuff.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
		/// Currency type with which voting happens.
		type Currency: ReservableCurrency<Self::AccountId>
			+ LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>
			+ fungible::Inspect<Self::AccountId>;

		/// The implementation of the logic which conducts polls.
		type Polls: Polling<
			TallyOf<Self, I>,
			Votes = BalanceOf<Self, I>,
			Moment = Self::BlockNumber,
		>;

		/// The maximum amount of tokens which may be used for voting. May just be
		/// `Currency::total_issuance`, but you might want to reduce this in order to account for
		/// funds in the system which are unable to vote (e.g. parachain auction deposits).
		type MaxTurnout: Get<BalanceOf<Self, I>>;

		/// The maximum number of concurrent votes an account may have.
		///
		/// Also used to compute weight, an overly large value can lead to extrinsics with large
		/// weight estimation: see `delegate` for instance.
		#[pallet::constant]
		type MaxVotes: Get<u32>;

		/// The minimum period of vote locking.
		///
		/// It should be no shorter than enactment period to ensure that in the case of an approval,
		/// those successful voters are locked into the consequences that their votes entail.
		#[pallet::constant]
		type VoteLockingPeriod: Get<Self::BlockNumber>;
	}

	/// All voting for a particular voter in a particular voting class. We store the balance for the
	/// number of votes that we have recorded.
	#[pallet::storage]
	pub type VotingFor<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Twox64Concat,
		T::AccountId,
		Twox64Concat,
		ClassOf<T, I>,
		VotingOf<T, I>,
		ValueQuery,
	>;

	/// The voting classes which have a non-zero lock requirement and the lock amounts which they
	/// require. The actual amount locked on behalf of this pallet should always be the maximum of
	/// this list.
	#[pallet::storage]
	pub type ClassLocksFor<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		BoundedVec<(ClassOf<T, I>, BalanceOf<T, I>), ClassCountOf<T::Polls, TallyOf<T, I>>>,
		ValueQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// An account has delegated their vote to another account. \[who, target\]
		Delegated(T::AccountId, T::AccountId),
		/// An \[account\] has cancelled a previous delegation operation.
		Undelegated(T::AccountId),
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Poll is not ongoing.
		NotOngoing,
		/// The given account did not vote on the poll.
		NotVoter,
		/// The actor has no permission to conduct the action.
		NoPermission,
		/// The actor has no permission to conduct the action right now but will do in the future.
		NoPermissionYet,
		/// The account is already delegating.
		AlreadyDelegating,
		/// The account currently has votes attached to it and the operation cannot succeed until
		/// these are removed, either through `unvote` or `reap_vote`.
		AlreadyVoting,
		/// Too high a balance was provided that the account cannot afford.
		InsufficientFunds,
		/// The account is not currently delegating.
		NotDelegating,
		/// Delegation to oneself makes no sense.
		Nonsense,
		/// Maximum number of votes reached.
		MaxVotesReached,
		/// The class must be supplied since it is not easily determinable from the state.
		ClassNeeded,
		/// The class ID supplied is invalid.
		BadClass,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Vote in a poll. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `poll_index`: The index of the poll to vote for.
		/// - `vote`: The vote configuration.
		///
		/// Weight: `O(R)` where R is the number of polls the voter has voted on.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::vote_new().max(T::WeightInfo::vote_existing()))]
		pub fn vote(
			origin: OriginFor<T>,
			#[pallet::compact] poll_index: PollIndexOf<T, I>,
			vote: AccountVote<BalanceOf<T, I>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_vote(&who, poll_index, vote)
		}

		/// Delegate the voting power (with some given conviction) of the sending account for a
		/// particular class of polls.
		///
		/// The balance delegated is locked for as long as it's delegated, and thereafter for the
		/// time appropriate for the conviction's lock period.
		///
		/// The dispatch origin of this call must be _Signed_, and the signing account must either:
		///   - be delegating already; or
		///   - have no voting activity (if there is, then it will need to be removed/consolidated
		///     through `reap_vote` or `unvote`).
		///
		/// - `to`: The account whose voting the `target` account's voting power will follow.
		/// - `class`: The class of polls to delegate. To delegate multiple classes, multiple calls
		///   to this function are required.
		/// - `conviction`: The conviction that will be attached to the delegated votes. When the
		///   account is undelegated, the funds will be locked for the corresponding period.
		/// - `balance`: The amount of the account's balance to be used in delegating. This must not
		///   be more than the account's current balance.
		///
		/// Emits `Delegated`.
		///
		/// Weight: `O(R)` where R is the number of polls the voter delegating to has
		///   voted on. Weight is initially charged as if maximum votes, but is refunded later.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::delegate(T::MaxVotes::get()))]
		pub fn delegate(
			origin: OriginFor<T>,
			class: ClassOf<T, I>,
			to: AccountIdLookupOf<T>,
			conviction: Conviction,
			balance: BalanceOf<T, I>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let to = T::Lookup::lookup(to)?;
			let votes = Self::try_delegate(who, class, to, conviction, balance)?;

			Ok(Some(T::WeightInfo::delegate(votes)).into())
		}

		/// Undelegate the voting power of the sending account for a particular class of polls.
		///
		/// Tokens may be unlocked following once an amount of time consistent with the lock period
		/// of the conviction with which the delegation was issued has passed.
		///
		/// The dispatch origin of this call must be _Signed_ and the signing account must be
		/// currently delegating.
		///
		/// - `class`: The class of polls to remove the delegation from.
		///
		/// Emits `Undelegated`.
		///
		/// Weight: `O(R)` where R is the number of polls the voter delegating to has
		///   voted on. Weight is initially charged as if maximum votes, but is refunded later.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::undelegate(T::MaxVotes::get().into()))]
		pub fn undelegate(
			origin: OriginFor<T>,
			class: ClassOf<T, I>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let votes = Self::try_undelegate(who, class)?;
			Ok(Some(T::WeightInfo::undelegate(votes)).into())
		}

		/// Remove the lock caused by prior voting/delegating which has expired within a particular
		/// class.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `class`: The class of polls to unlock.
		/// - `target`: The account to remove the lock on.
		///
		/// Weight: `O(R)` with R number of vote of target.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::unlock())]
		pub fn unlock(
			origin: OriginFor<T>,
			class: ClassOf<T, I>,
			target: AccountIdLookupOf<T>,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			Self::update_lock(&class, &target);
			Ok(())
		}

		/// Remove a vote for a poll.
		///
		/// If:
		/// - the poll was cancelled, or
		/// - the poll is ongoing, or
		/// - the poll has ended such that
		///   - the vote of the account was in opposition to the result; or
		///   - there was no conviction to the account's vote; or
		///   - the account made a split vote
		/// ...then the vote is removed cleanly and a following call to `unlock` may result in more
		/// funds being available.
		///
		/// If, however, the poll has ended and:
		/// - it finished corresponding to the vote of the account, and
		/// - the account made a standard vote with conviction, and
		/// - the lock period of the conviction is not over
		/// ...then the lock will be aggregated into the overall account's lock, which may involve
		/// *overlocking* (where the two locks are combined into a single lock that is the maximum
		/// of both the amount locked and the time is it locked for).
		///
		/// The dispatch origin of this call must be _Signed_, and the signer must have a vote
		/// registered for poll `index`.
		///
		/// - `index`: The index of poll of the vote to be removed.
		/// - `class`: Optional parameter, if given it indicates the class of the poll. For polls
		///   which have finished or are cancelled, this must be `Some`.
		///
		/// Weight: `O(R + log R)` where R is the number of polls that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::remove_vote())]
		pub fn remove_vote(
			origin: OriginFor<T>,
			class: Option<ClassOf<T, I>>,
			index: PollIndexOf<T, I>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_remove_vote(&who, index, class, UnvoteScope::Any)
		}

		/// Remove a vote for a poll.
		///
		/// If the `target` is equal to the signer, then this function is exactly equivalent to
		/// `remove_vote`. If not equal to the signer, then the vote must have expired,
		/// either because the poll was cancelled, because the voter lost the poll or
		/// because the conviction period is over.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account of the vote to be removed; this account must have voted for poll
		///   `index`.
		/// - `index`: The index of poll of the vote to be removed.
		/// - `class`: The class of the poll.
		///
		/// Weight: `O(R + log R)` where R is the number of polls that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::remove_other_vote())]
		pub fn remove_other_vote(
			origin: OriginFor<T>,
			target: AccountIdLookupOf<T>,
			class: ClassOf<T, I>,
			index: PollIndexOf<T, I>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			let scope = if target == who { UnvoteScope::Any } else { UnvoteScope::OnlyExpired };
			Self::try_remove_vote(&target, index, Some(class), scope)?;
			Ok(())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Actually enact a vote, if legit.
	fn try_vote(
		who: &T::AccountId,
		poll_index: PollIndexOf<T, I>,
		vote: AccountVote<BalanceOf<T, I>>,
	) -> DispatchResult {
		ensure!(
			vote.balance() <= T::Currency::total_balance(who),
			Error::<T, I>::InsufficientFunds
		);
		T::Polls::try_access_poll(poll_index, |poll_status| {
			let (tally, class) = poll_status.ensure_ongoing().ok_or(Error::<T, I>::NotOngoing)?;
			VotingFor::<T, I>::try_mutate(who, &class, |voting| {
				if let Voting::Casting(Casting { ref mut votes, delegations, .. }) = voting {
					match votes.binary_search_by_key(&poll_index, |i| i.0) {
						Ok(i) => {
							// Shouldn't be possible to fail, but we handle it gracefully.
							tally.remove(votes[i].1).ok_or(ArithmeticError::Underflow)?;
							if let Some(approve) = votes[i].1.as_standard() {
								tally.reduce(approve, *delegations);
							}
							votes[i].1 = vote;
						},
						Err(i) => {
							votes
								.try_insert(i, (poll_index, vote))
								.map_err(|_| Error::<T, I>::MaxVotesReached)?;
						},
					}
					// Shouldn't be possible to fail, but we handle it gracefully.
					tally.add(vote).ok_or(ArithmeticError::Overflow)?;
					if let Some(approve) = vote.as_standard() {
						tally.increase(approve, *delegations);
					}
				} else {
					return Err(Error::<T, I>::AlreadyDelegating.into())
				}
				// Extend the lock to `balance` (rather than setting it) since we don't know what
				// other votes are in place.
				Self::extend_lock(who, &class, vote.balance());
				Ok(())
			})
		})
	}

	/// Remove the account's vote for the given poll if possible. This is possible when:
	/// - The poll has not finished.
	/// - The poll has finished and the voter lost their direction.
	/// - The poll has finished and the voter's lock period is up.
	///
	/// This will generally be combined with a call to `unlock`.
	fn try_remove_vote(
		who: &T::AccountId,
		poll_index: PollIndexOf<T, I>,
		class_hint: Option<ClassOf<T, I>>,
		scope: UnvoteScope,
	) -> DispatchResult {
		let class = class_hint
			.or_else(|| Some(T::Polls::as_ongoing(poll_index)?.1))
			.ok_or(Error::<T, I>::ClassNeeded)?;
		VotingFor::<T, I>::try_mutate(who, class, |voting| {
			if let Voting::Casting(Casting { ref mut votes, delegations, ref mut prior }) = voting {
				let i = votes
					.binary_search_by_key(&poll_index, |i| i.0)
					.map_err(|_| Error::<T, I>::NotVoter)?;
				let v = votes.remove(i);

				T::Polls::try_access_poll(poll_index, |poll_status| match poll_status {
					PollStatus::Ongoing(tally, _) => {
						ensure!(matches!(scope, UnvoteScope::Any), Error::<T, I>::NoPermission);
						// Shouldn't be possible to fail, but we handle it gracefully.
						tally.remove(v.1).ok_or(ArithmeticError::Underflow)?;
						if let Some(approve) = v.1.as_standard() {
							tally.reduce(approve, *delegations);
						}
						Ok(())
					},
					PollStatus::Completed(end, approved) => {
						if let Some((lock_periods, balance)) = v.1.locked_if(approved) {
							let unlock_at = end.saturating_add(
								T::VoteLockingPeriod::get().saturating_mul(lock_periods.into()),
							);
							let now = frame_system::Pallet::<T>::block_number();
							if now < unlock_at {
								ensure!(
									matches!(scope, UnvoteScope::Any),
									Error::<T, I>::NoPermissionYet
								);
								prior.accumulate(unlock_at, balance)
							}
						}
						Ok(())
					},
					PollStatus::None => Ok(()), // Poll was cancelled.
				})
			} else {
				Ok(())
			}
		})
	}

	/// Return the number of votes for `who`.
	fn increase_upstream_delegation(
		who: &T::AccountId,
		class: &ClassOf<T, I>,
		amount: Delegations<BalanceOf<T, I>>,
	) -> u32 {
		VotingFor::<T, I>::mutate(who, class, |voting| match voting {
			Voting::Delegating(Delegating { delegations, .. }) => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_add(amount);
				1
			},
			Voting::Casting(Casting { votes, delegations, .. }) => {
				*delegations = delegations.saturating_add(amount);
				for &(poll_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						T::Polls::access_poll(poll_index, |poll_status| {
							if let PollStatus::Ongoing(tally, _) = poll_status {
								tally.increase(vote.aye, amount);
							}
						});
					}
				}
				votes.len() as u32
			},
		})
	}

	/// Return the number of votes for `who`.
	fn reduce_upstream_delegation(
		who: &T::AccountId,
		class: &ClassOf<T, I>,
		amount: Delegations<BalanceOf<T, I>>,
	) -> u32 {
		VotingFor::<T, I>::mutate(who, class, |voting| match voting {
			Voting::Delegating(Delegating { delegations, .. }) => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_sub(amount);
				1
			},
			Voting::Casting(Casting { votes, delegations, .. }) => {
				*delegations = delegations.saturating_sub(amount);
				for &(poll_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						T::Polls::access_poll(poll_index, |poll_status| {
							if let PollStatus::Ongoing(tally, _) = poll_status {
								tally.reduce(vote.aye, amount);
							}
						});
					}
				}
				votes.len() as u32
			},
		})
	}

	/// Attempt to delegate `balance` times `conviction` of voting power from `who` to `target`.
	///
	/// Return the upstream number of votes.
	fn try_delegate(
		who: T::AccountId,
		class: ClassOf<T, I>,
		target: T::AccountId,
		conviction: Conviction,
		balance: BalanceOf<T, I>,
	) -> Result<u32, DispatchError> {
		ensure!(who != target, Error::<T, I>::Nonsense);
		T::Polls::classes().binary_search(&class).map_err(|_| Error::<T, I>::BadClass)?;
		ensure!(balance <= T::Currency::total_balance(&who), Error::<T, I>::InsufficientFunds);
		let votes =
			VotingFor::<T, I>::try_mutate(&who, &class, |voting| -> Result<u32, DispatchError> {
				let old = sp_std::mem::replace(
					voting,
					Voting::Delegating(Delegating {
						balance,
						target: target.clone(),
						conviction,
						delegations: Default::default(),
						prior: Default::default(),
					}),
				);
				match old {
					Voting::Delegating(Delegating { .. }) =>
						return Err(Error::<T, I>::AlreadyDelegating.into()),
					Voting::Casting(Casting { votes, delegations, prior }) => {
						// here we just ensure that we're currently idling with no votes recorded.
						ensure!(votes.is_empty(), Error::<T, I>::AlreadyVoting);
						voting.set_common(delegations, prior);
					},
				}

				let votes =
					Self::increase_upstream_delegation(&target, &class, conviction.votes(balance));
				// Extend the lock to `balance` (rather than setting it) since we don't know what
				// other votes are in place.
				Self::extend_lock(&who, &class, balance);
				Ok(votes)
			})?;
		Self::deposit_event(Event::<T, I>::Delegated(who, target));
		Ok(votes)
	}

	/// Attempt to end the current delegation.
	///
	/// Return the number of votes of upstream.
	fn try_undelegate(who: T::AccountId, class: ClassOf<T, I>) -> Result<u32, DispatchError> {
		let votes =
			VotingFor::<T, I>::try_mutate(&who, &class, |voting| -> Result<u32, DispatchError> {
				match sp_std::mem::replace(voting, Voting::default()) {
					Voting::Delegating(Delegating {
						balance,
						target,
						conviction,
						delegations,
						mut prior,
					}) => {
						// remove any delegation votes to our current target.
						let votes = Self::reduce_upstream_delegation(
							&target,
							&class,
							conviction.votes(balance),
						);
						let now = frame_system::Pallet::<T>::block_number();
						let lock_periods = conviction.lock_periods().into();
						prior.accumulate(
							now.saturating_add(
								T::VoteLockingPeriod::get().saturating_mul(lock_periods),
							),
							balance,
						);
						voting.set_common(delegations, prior);

						Ok(votes)
					},
					Voting::Casting(_) => Err(Error::<T, I>::NotDelegating.into()),
				}
			})?;
		Self::deposit_event(Event::<T, I>::Undelegated(who));
		Ok(votes)
	}

	fn extend_lock(who: &T::AccountId, class: &ClassOf<T, I>, amount: BalanceOf<T, I>) {
		ClassLocksFor::<T, I>::mutate(who, |locks| {
			match locks.iter().position(|x| &x.0 == class) {
				Some(i) => locks[i].1 = locks[i].1.max(amount),
				None => {
					let ok = locks.try_push((class.clone(), amount)).is_ok();
					debug_assert!(
						ok,
						"Vec bounded by number of classes; \
						all items in Vec associated with a unique class; \
						qed"
					);
				},
			}
		});
		T::Currency::extend_lock(
			CONVICTION_VOTING_ID,
			who,
			amount,
			WithdrawReasons::except(WithdrawReasons::RESERVE),
		);
	}

	/// Rejig the lock on an account. It will never get more stringent (since that would indicate
	/// a security hole) but may be reduced from what they are currently.
	fn update_lock(class: &ClassOf<T, I>, who: &T::AccountId) {
		let class_lock_needed = VotingFor::<T, I>::mutate(who, class, |voting| {
			voting.rejig(frame_system::Pallet::<T>::block_number());
			voting.locked_balance()
		});
		let lock_needed = ClassLocksFor::<T, I>::mutate(who, |locks| {
			locks.retain(|x| &x.0 != class);
			if !class_lock_needed.is_zero() {
				let ok = locks.try_push((class.clone(), class_lock_needed)).is_ok();
				debug_assert!(
					ok,
					"Vec bounded by number of classes; \
					all items in Vec associated with a unique class; \
					qed"
				);
			}
			locks.iter().map(|x| x.1).max().unwrap_or(Zero::zero())
		});
		if lock_needed.is_zero() {
			T::Currency::remove_lock(CONVICTION_VOTING_ID, who);
		} else {
			T::Currency::set_lock(
				CONVICTION_VOTING_ID,
				who,
				lock_needed,
				WithdrawReasons::except(WithdrawReasons::RESERVE),
			);
		}
	}
}
