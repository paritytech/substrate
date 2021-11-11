// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0sp_runtime::{DispatchResult, traits::One}asp_runtime::{DispatchResult, traits::AtLeast32BitUnsigned} in writing, software
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
//! Pallet for managing actual voting in referenda.

#![recursion_limit = "256"]
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{ensure, traits::{
	Currency, Get, LockIdentifier, LockableCurrency, ReservableCurrency, WithdrawReasons,
	PollStatus, Referenda,
}};
use sp_runtime::{ArithmeticError, DispatchError, DispatchResult, Perbill, traits::{
	Saturating, Zero, AtLeast32BitUnsigned
}};
use sp_std::prelude::*;

mod conviction;
mod types;
mod vote;
pub mod weights;
pub use conviction::Conviction;
pub use pallet::*;
pub use types::{Delegations, Tally, UnvoteScope};
pub use vote::{AccountVote, Vote, Voting};
pub use weights::WeightInfo;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

const CONVICTION_VOTING_ID: LockIdentifier = *b"pyconvot";

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type VotingOf<T> = Voting<
	BalanceOf<T>,
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::BlockNumber,
	ReferendumIndexOf<T>,
>;
type TallyOf<T> = Tally<BalanceOf<T>, <T as Config>::MaxTurnout>;
type ReferendumIndexOf<T> = <<T as Config>::Referenda as Referenda<TallyOf<T>>>::Index;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_runtime::DispatchResult;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + Sized {
		// System level stuff.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
		/// Currency type with which voting happens.
		type Currency: ReservableCurrency<Self::AccountId>
			+ LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;

		/// The implementation of the logic which conducts referenda.
		type Referenda: Referenda<
			TallyOf<Self>,
			Votes = BalanceOf<Self>,
			Moment = Self::BlockNumber,
		>;

		/// The maximum amount of tokens which may be used for voting. May just be
		/// `Currency::total_issuance`, but you might want to reduce this in order to account for
		/// funds in the system which are unable to vote (e.g. parachain auction deposits).
		type MaxTurnout: Get<BalanceOf<Self>>;

		/// The maximum number of concurrent votes an account may have.
		///
		/// Also used to compute weight, an overly large value can
		/// lead to extrinsic with large weight estimation: see `delegate` for instance.
		#[pallet::constant]
		type MaxVotes: Get<u32>;

		/// The minimum period of vote locking.
		///
		/// It should be no shorter than enactment period to ensure that in the case of an approval,
		/// those successful voters are locked into the consequences that their votes entail.
		#[pallet::constant]
		type VoteLockingPeriod: Get<Self::BlockNumber>;
	}

	/// All votes for a particular voter. We store the balance for the number of votes that we
	/// have recorded. The second item is the total amount of delegations, that will be added.
	///
	/// TWOX-NOTE: SAFE as `AccountId`s are crypto hashes anyway.
	#[pallet::storage]
	pub type VotingFor<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		VotingOf<T>,
		ValueQuery,
	>;

	/// Accounts for which there are locks in action which may be removed at some point in the
	/// future. The value is the block number at which the lock expires and may be removed.
	///
	/// TWOX-NOTE: OK ― `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn locks)]
	pub type Locks<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, T::BlockNumber>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// An account has delegated their vote to another account. \[who, target\]
		Delegated(T::AccountId, T::AccountId),
		/// An \[account\] has cancelled a previous delegation operation.
		Undelegated(T::AccountId),
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Value too low
		ValueLow,
		/// Referendum is not ongoing.
		NotOngoing,
		/// Referendum's decision deposit is already paid.
		HaveDeposit,
		/// Proposal does not exist
		ProposalMissing,
		/// Cannot cancel the same proposal twice
		AlreadyCanceled,
		/// Proposal already made
		DuplicateProposal,
		/// Vote given for invalid referendum
		ReferendumInvalid,
		/// The given account did not vote on the referendum.
		NotVoter,
		/// The actor has no permission to conduct the action.
		NoPermission,
		/// The account is already delegating.
		AlreadyDelegating,
		/// Too high a balance was provided that the account cannot afford.
		InsufficientFunds,
		/// The account is not currently delegating.
		NotDelegating,
		/// The account currently has votes attached to it and the operation cannot succeed until
		/// these are removed, either through `unvote` or `reap_vote`.
		VotesExist,
		/// Delegation to oneself makes no sense.
		Nonsense,
		/// Invalid upper bound.
		WrongUpperBound,
		/// Maximum number of votes reached.
		MaxVotesReached,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Vote in a referendum. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `ref_index`: The index of the referendum to vote for.
		/// - `vote`: The vote configuration.
		///
		/// Weight: `O(R)` where R is the number of referenda the voter has voted on.
		#[pallet::weight(
			T::WeightInfo::vote_new(T::MaxVotes::get())
				.max(T::WeightInfo::vote_existing(T::MaxVotes::get()))
		)]
		pub fn vote(
			origin: OriginFor<T>,
			#[pallet::compact] ref_index: ReferendumIndexOf<T>,
			vote: AccountVote<BalanceOf<T>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_vote(&who, ref_index, vote)
		}

		/// Delegate the voting power (with some given conviction) of the sending account.
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
		/// - `conviction`: The conviction that will be attached to the delegated votes. When the
		///   account is undelegated, the funds will be locked for the corresponding period.
		/// - `balance`: The amount of the account's balance to be used in delegating. This must not
		///   be more than the account's current balance.
		///
		/// Emits `Delegated`.
		///
		/// Weight: `O(R)` where R is the number of referenda the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::weight(T::WeightInfo::delegate(T::MaxVotes::get()))]
		pub fn delegate(
			origin: OriginFor<T>,
			to: T::AccountId,
			conviction: Conviction,
			balance: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let votes = Self::try_delegate(who, to, conviction, balance)?;

			Ok(Some(T::WeightInfo::delegate(votes)).into())
		}

		/// Undelegate the voting power of the sending account.
		///
		/// Tokens may be unlocked following once an amount of time consistent with the lock period
		/// of the conviction with which the delegation was issued.
		///
		/// The dispatch origin of this call must be _Signed_ and the signing account must be
		/// currently delegating.
		///
		/// Emits `Undelegated`.
		///
		/// Weight: `O(R)` where R is the number of referenda the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::weight(T::WeightInfo::undelegate(T::MaxVotes::get().into()))]
		pub fn undelegate(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let votes = Self::try_undelegate(who)?;
			Ok(Some(T::WeightInfo::undelegate(votes)).into())
		}

		/// Unlock tokens that have an expired lock.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account to remove the lock on.
		///
		/// Weight: `O(R)` with R number of vote of target.
		#[pallet::weight(
			T::WeightInfo::unlock_set(T::MaxVotes::get())
				.max(T::WeightInfo::unlock_remove(T::MaxVotes::get()))
		)]
		pub fn unlock(origin: OriginFor<T>, target: T::AccountId) -> DispatchResult {
			ensure_signed(origin)?;
			Self::update_lock(&target);
			Ok(())
		}

		/// Remove a vote for a referendum.
		///
		/// If:
		/// - the referendum was cancelled, or
		/// - the referendum is ongoing, or
		/// - the referendum has ended such that
		///   - the vote of the account was in opposition to the result; or
		///   - there was no conviction to the account's vote; or
		///   - the account made a split vote
		/// ...then the vote is removed cleanly and a following call to `unlock` may result in more
		/// funds being available.
		///
		/// If, however, the referendum has ended and:
		/// - it finished corresponding to the vote of the account, and
		/// - the account made a standard vote with conviction, and
		/// - the lock period of the conviction is not over
		/// ...then the lock will be aggregated into the overall account's lock, which may involve
		/// *overlocking* (where the two locks are combined into a single lock that is the maximum
		/// of both the amount locked and the time is it locked for).
		///
		/// The dispatch origin of this call must be _Signed_, and the signer must have a vote
		/// registered for referendum `index`.
		///
		/// - `index`: The index of referendum of the vote to be removed.
		///
		/// Weight: `O(R + log R)` where R is the number of referenda that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::weight(T::WeightInfo::remove_vote(T::MaxVotes::get()))]
		pub fn remove_vote(origin: OriginFor<T>, index: ReferendumIndexOf<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_remove_vote(&who, index, UnvoteScope::Any)
		}

		/// Remove a vote for a referendum.
		///
		/// If the `target` is equal to the signer, then this function is exactly equivalent to
		/// `remove_vote`. If not equal to the signer, then the vote must have expired,
		/// either because the referendum was cancelled, because the voter lost the referendum or
		/// because the conviction period is over.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account of the vote to be removed; this account must have voted for
		///   referendum `index`.
		/// - `index`: The index of referendum of the vote to be removed.
		///
		/// Weight: `O(R + log R)` where R is the number of referenda that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::weight(T::WeightInfo::remove_other_vote(T::MaxVotes::get()))]
		pub fn remove_other_vote(
			origin: OriginFor<T>,
			target: T::AccountId,
			index: ReferendumIndexOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let scope = if target == who { UnvoteScope::Any } else { UnvoteScope::OnlyExpired };
			Self::try_remove_vote(&target, index, scope)?;
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Actually enact a vote, if legit.
	fn try_vote(
		who: &T::AccountId,
		ref_index: ReferendumIndexOf<T>,
		vote: AccountVote<BalanceOf<T>>,
	) -> DispatchResult {
		ensure!(vote.balance() <= T::Currency::free_balance(who), Error::<T>::InsufficientFunds);
		T::Referenda::try_access_poll(ref_index, |poll_status| {
			let tally = poll_status.ensure_ongoing().ok_or(Error::<T>::NotOngoing)?;
			VotingFor::<T>::try_mutate(who, |voting| {
				if let Voting::Direct { ref mut votes, delegations, .. } = voting {
					match votes.binary_search_by_key(&ref_index, |i| i.0) {
						Ok(i) => {
							// Shouldn't be possible to fail, but we handle it gracefully.
							tally.remove(votes[i].1).ok_or(ArithmeticError::Underflow)?;
							if let Some(approve) = votes[i].1.as_standard() {
								tally.reduce(approve, *delegations);
							}
							votes[i].1 = vote;
						},
						Err(i) => {
							ensure!(
								votes.len() as u32 <= T::MaxVotes::get(),
								Error::<T>::MaxVotesReached
							);
							votes.insert(i, (ref_index, vote));
						},
					}
					// Shouldn't be possible to fail, but we handle it gracefully.
					tally.add(vote).ok_or(ArithmeticError::Overflow)?;
					if let Some(approve) = vote.as_standard() {
						tally.increase(approve, *delegations);
					}
				} else {
					return Err(Error::<T>::AlreadyDelegating.into())
				}
				// Extend the lock to `balance` (rather than setting it) since we don't know what other
				// votes are in place.
				T::Currency::extend_lock(CONVICTION_VOTING_ID, who, vote.balance(), WithdrawReasons::TRANSFER);
				Ok(())
			})
		})
	}

	/// Remove the account's vote for the given referendum if possible. This is possible when:
	/// - The referendum has not finished.
	/// - The referendum has finished and the voter lost their direction.
	/// - The referendum has finished and the voter's lock period is up.
	///
	/// This will generally be combined with a call to `unlock`.
	fn try_remove_vote(
		who: &T::AccountId,
		ref_index: ReferendumIndexOf<T>,
		scope: UnvoteScope,
	) -> DispatchResult {
		VotingFor::<T>::try_mutate(who, |voting| {
			if let Voting::Direct { ref mut votes, delegations, ref mut prior } = voting {
				let i = votes
					.binary_search_by_key(&ref_index, |i| i.0)
					.map_err(|_| Error::<T>::NotVoter)?;
				let v = votes.remove(i);

				T::Referenda::try_access_poll(ref_index, |poll_status| match poll_status {
					PollStatus::Ongoing(tally) => {
						ensure!(matches!(scope, UnvoteScope::Any), Error::<T>::NoPermission);
						// Shouldn't be possible to fail, but we handle it gracefully.
						tally.remove(v.1).ok_or(ArithmeticError::Underflow)?;
						if let Some(approve) = v.1.as_standard() {
							tally.reduce(approve, *delegations);
						}
						Ok(())
					},
					PollStatus::Completed(end, approved) => {
						if let Some((lock_periods, balance)) = v.1.locked_if(approved) {
							let unlock_at = end + T::VoteLockingPeriod::get() * lock_periods.into();
							let now = frame_system::Pallet::<T>::block_number();
							if now < unlock_at {
								ensure!(
									matches!(scope, UnvoteScope::Any),
									Error::<T>::NoPermission
								);
								prior.accumulate(unlock_at, balance)
							}
						}
						Ok(())
					},
					PollStatus::None => Ok(()), // Referendum was cancelled.
				})
			} else {
				Ok(())
			}
		})
	}

	/// Return the number of votes for `who`
	fn increase_upstream_delegation(who: &T::AccountId, amount: Delegations<BalanceOf<T>>) -> u32 {
		VotingFor::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_add(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_add(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						T::Referenda::access_poll(ref_index, |poll_status| {
							if let PollStatus::Ongoing(tally) = poll_status {
								tally.increase(vote.aye, amount);
							}
						});
					}
				}
				votes.len() as u32
			},
		})
	}

	/// Return the number of votes for `who`
	fn reduce_upstream_delegation(who: &T::AccountId, amount: Delegations<BalanceOf<T>>) -> u32 {
		VotingFor::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_sub(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_sub(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						T::Referenda::access_poll(ref_index, |poll_status| {
							if let PollStatus::Ongoing(tally) = poll_status {
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
		target: T::AccountId,
		conviction: Conviction,
		balance: BalanceOf<T>,
	) -> Result<u32, DispatchError> {
		ensure!(who != target, Error::<T>::Nonsense);
		ensure!(balance <= T::Currency::free_balance(&who), Error::<T>::InsufficientFunds);
		let votes = VotingFor::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::Delegating {
				balance,
				target: target.clone(),
				conviction,
				delegations: Default::default(),
				prior: Default::default(),
			};
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating { balance, target, conviction, delegations, prior, .. } => {
					// remove any delegation votes to our current target.
					Self::reduce_upstream_delegation(&target, conviction.votes(balance));
					voting.set_common(delegations, prior);
				},
				Voting::Direct { votes, delegations, prior } => {
					// here we just ensure that we're currently idling with no votes recorded.
					ensure!(votes.is_empty(), Error::<T>::VotesExist);
					voting.set_common(delegations, prior);
				},
			}
			let votes = Self::increase_upstream_delegation(&target, conviction.votes(balance));
			// Extend the lock to `balance` (rather than setting it) since we don't know what other
			// votes are in place.
			T::Currency::extend_lock(CONVICTION_VOTING_ID, &who, balance, WithdrawReasons::TRANSFER);
			Ok(votes)
		})?;
		Self::deposit_event(Event::<T>::Delegated(who, target));
		Ok(votes)
	}

	/// Attempt to end the current delegation.
	///
	/// Return the number of votes of upstream.
	fn try_undelegate(who: T::AccountId) -> Result<u32, DispatchError> {
		let votes = VotingFor::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::default();
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating { balance, target, conviction, delegations, mut prior } => {
					// remove any delegation votes to our current target.
					let votes =
						Self::reduce_upstream_delegation(&target, conviction.votes(balance));
					let now = frame_system::Pallet::<T>::block_number();
					let lock_periods = conviction.lock_periods().into();
					prior.accumulate(now + T::VoteLockingPeriod::get() * lock_periods, balance);
					voting.set_common(delegations, prior);

					Ok(votes)
				},
				Voting::Direct { .. } => Err(Error::<T>::NotDelegating.into()),
			}
		})?;
		Self::deposit_event(Event::<T>::Undelegated(who));
		Ok(votes)
	}

	/// Rejig the lock on an account. It will never get more stringent (since that would indicate
	/// a security hole) but may be reduced from what they are currently.
	fn update_lock(who: &T::AccountId) {
		let lock_needed = VotingFor::<T>::mutate(who, |voting| {
			voting.rejig(frame_system::Pallet::<T>::block_number());
			voting.locked_balance()
		});
		if lock_needed.is_zero() {
			T::Currency::remove_lock(CONVICTION_VOTING_ID, who);
		} else {
			T::Currency::set_lock(CONVICTION_VOTING_ID, who, lock_needed, WithdrawReasons::TRANSFER);
		}
	}
}
