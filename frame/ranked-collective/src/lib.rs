// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Ranked collective system: Members of a set of account IDs can make their collective feelings
//! known through dispatched calls from one of two specialized origins.
//!
//! The membership can be provided in one of two ways: either directly, using the Root-dispatchable
//! function `set_members`, or indirectly, through implementing the `ChangeMembers`.
//! The pallet assumes that the amount of members stays at or below `MaxMembers` for its weight
//! calculations, but enforces this neither in `set_members` nor in `change_members_sorted`.
//!
//! A "prime" member may be set to help determine the default vote behavior based on chain
//! config. If `PrimeDefaultVote` is used, the prime vote acts as the default vote in case of any
//! abstentions after the voting period. If `MoreThanMajorityThenPrimeDefaultVote` is used, then
//! abstentions will first follow the majority of the collective voting, and then the prime
//! member.
//!
//! Voting happens through motions comprising a proposal (i.e. a curried dispatchable) plus a
//! number of approvals required for it to pass and be called. Motions are open for members to
//! vote on for a minimum period given by `MotionDuration`. As soon as the needed number of
//! approvals is given, the motion is closed and executed. If the number of approvals is not reached
//! during the voting period, then `close` may be called by any account in order to force the end
//! the motion explicitly. If a prime member is defined then their vote is used in place of any
//! abstentions and the proposal is executed if there are enough approvals counting the new votes.
//!
//! If there are not, or if no prime is set, then the motion is dropped without being executed.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "128"]

use scale_info::TypeInfo;
use sp_arithmetic::traits::Saturating;
use sp_runtime::{
	ArithmeticError::{Overflow, Underflow},
	Perbill, RuntimeDebug,
};
use sp_std::{marker::PhantomData, prelude::*};

use frame_support::{
	codec::{Decode, Encode, MaxEncodedLen},
	dispatch::{DispatchError, DispatchResultWithPostInfo},
	ensure,
	traits::{EnsureOrigin, Get, PollStatus, Polling, VoteTally},
	CloneNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// A number of members.
pub type MemberIndex = u32;

/// Member rank.
pub type Rank = u16;

/// Votes.
pub type Votes = u32;

/// Aggregated votes for an ongoing poll.
#[derive(
	CloneNoBound,
	DefaultNoBound,
	PartialEqNoBound,
	EqNoBound,
	RuntimeDebugNoBound,
	TypeInfo,
	Encode,
	Decode,
	MaxEncodedLen,
)]
#[scale_info(skip_type_params(M))]
pub struct Tally<M: Get<Votes>> {
	ayes: Votes,
	nays: Votes,
	dummy: PhantomData<M>,
}

impl<M: Get<Votes>> Tally<M> {
	fn from_parts(ayes: Votes, nays: Votes) -> Self {
		Tally { ayes, nays, dummy: PhantomData }
	}
}

pub type TallyOf<T, I = ()> = Tally<Pallet<T, I>>;
pub type PollIndexOf<T, I = ()> = <<T as Config<I>>::Polls as Polling<TallyOf<T, I>>>::Index;

impl<M: Get<Votes>> VoteTally<Votes> for Tally<M> {
	fn ayes(&self) -> Votes {
		self.ayes
	}
	fn support(&self) -> Perbill {
		Perbill::from_rational(self.ayes, M::get())
	}
	fn approval(&self) -> Perbill {
		Perbill::from_rational(self.ayes, 1.max(self.ayes + self.nays))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn unanimity() -> Self {
		Self { ayes: M::get(), nays: 0, dummy: PhantomData }
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn rejection() -> Self {
		Self { ayes: 0, nays: M::get(), dummy: PhantomData }
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn from_requirements(support: Perbill, approval: Perbill) -> Self {
		let c = M::get();
		let ayes = support * c;
		let nays = ((ayes as u64) * 1_000_000_000u64 / approval.deconstruct() as u64) as u32 - ayes;
		Self { ayes, nays, dummy: PhantomData }
	}
}

/// Record needed for every member.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct MemberRecord {
	/// The index of the member.
	index: MemberIndex,
	/// The rank of the member.
	rank: Rank,
}

/// Record needed for every vote.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum VoteRecord {
	/// Vote was an aye with given vote weight.
	Aye(Votes),
	/// Vote was a nay with given vote weight.
	Nay(Votes),
}

impl From<(bool, Votes)> for VoteRecord {
	fn from((aye, votes): (bool, Votes)) -> Self {
		match aye {
			true => VoteRecord::Aye(votes),
			false => VoteRecord::Nay(votes),
		}
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The outer event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// The origin required to add, promote or remove a member.
		type AdminOrigin: EnsureOrigin<Self::Origin>;

		/// The polling system used for our voting.
		type Polls: Polling<TallyOf<Self, I>, Votes = Votes, Moment = Self::BlockNumber>;
	}

	/// The number of members in the collective.
	#[pallet::storage]
	pub type MemberCount<T: Config<I>, I: 'static = ()> =
		StorageValue<_, (MemberIndex, Votes), ValueQuery>;

	/// The current members of the collective.
	#[pallet::storage]
	pub type Members<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberRecord>;

	/// The members in the collective by index. All indices in the range `0..MemberCount` will
	/// return `Some`, however a member's index is not guaranteed to remain unchanged over time.
	#[pallet::storage]
	pub type MemberByIndex<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, MemberIndex, T::AccountId>;

	/// Votes on a given proposal, if it is ongoing.
	#[pallet::storage]
	pub type Voting<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		PollIndexOf<T, I>,
		Twox64Concat,
		T::AccountId,
		VoteRecord,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A member has been added.
		MemberAdded { who: T::AccountId, rank: Rank },
		/// A member's rank has been changed.
		RankChanged { who: T::AccountId, rank: Rank },
		/// A member has been removed.
		MemberRemoved { who: T::AccountId },
		/// A motion (given hash) has been voted on by given account, leaving
		/// a tally (yes votes and no votes given respectively as `MemberIndex`).
		Voted { who: T::AccountId, poll: PollIndexOf<T, I>, vote: VoteRecord, tally: TallyOf<T, I> },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Account is already a member.
		AlreadyMember,
		/// Account is not a member.
		NotMember,
		/// The given poll index is unknown or has closed.
		NotPolling,
		/// The given poll is still ongoing.
		Ongoing,
		/// There are no further records to be removed.
		NoneRemaining,
		/// Unexpected error in state.
		Corruption,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Introduce a new member.
		///
		/// - `origin`: Must be the `AdminOrigin`.
		/// - `who`: Account of non-member which will become a member.
		/// - `rank`: The rank to give the new member.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn add_member(origin: OriginFor<T>, who: T::AccountId, rank: Rank) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;
			ensure!(!Members::<T, I>::contains_key(&who), Error::<T, I>::AlreadyMember);
			let (index, mut votes) = MemberCount::<T, I>::get();
			let count = index.checked_add(1).ok_or(Overflow)?;
			votes = votes.checked_add(Self::rank_to_votes(rank)).ok_or(Overflow)?;

			Members::<T, I>::insert(&who, MemberRecord { rank, index });
			MemberByIndex::<T, I>::insert(index, &who);
			MemberCount::<T, I>::put((count, votes));
			Self::deposit_event(Event::MemberAdded { who, rank });

			Ok(())
		}

		/// Alter the rank of an existing member.
		///
		/// - `origin`: Must be the `AdminOrigin`.
		/// - `who`: Account of existing member.
		/// - `rank`: The new rank to give the member.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn set_member_rank(
			origin: OriginFor<T>,
			who: T::AccountId,
			rank: Rank,
		) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;
			let mut record = Self::ensure_member(&who)?;
			let (count, mut votes) = MemberCount::<T, I>::get();
			votes = votes
				.checked_sub(Self::rank_to_votes(record.rank))
				.ok_or(Underflow)?
				.checked_add(Self::rank_to_votes(rank))
				.ok_or(Overflow)?;
			record.rank = rank;

			MemberCount::<T, I>::put((count, votes));
			Members::<T, I>::insert(&who, record);
			Self::deposit_event(Event::RankChanged { who, rank });

			Ok(())
		}

		/// Remove a member.
		///
		/// - `origin`: Must be the `AdminOrigin`.
		/// - `who`: Account of existing member to be removed.
		///
		/// Weight: `O(1)`, less if the member's index is highest.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn remove_member(origin: OriginFor<T>, who: T::AccountId) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;
			let record = Self::ensure_member(&who)?;
			let (count, votes) = MemberCount::<T, I>::get();
			let count = count.checked_sub(1).ok_or(Underflow)?;
			let votes = votes.checked_sub(Self::rank_to_votes(record.rank)).ok_or(Underflow)?;

			let index = record.index;
			if index != count {
				let last = MemberByIndex::<T, I>::get(count).ok_or(Error::<T, I>::Corruption)?;
				Members::<T, I>::mutate(&last, |r| {
					if let Some(ref mut r) = r {
						r.index = index
					}
				});
				MemberByIndex::<T, I>::insert(index, &last);
			}
			MemberByIndex::<T, I>::remove(count);
			Members::<T, I>::remove(&who);
			MemberCount::<T, I>::put((count, votes));
			Self::deposit_event(Event::MemberRemoved { who });

			Ok(())
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// - `origin`: Must be `Signed` by a member account.
		/// - `poll`: Index of a poll which is ongoing.
		/// - `aye`: `true` if the vote is to approve the proposal, `false` otherwise.
		///
		/// Transaction fees are be waived if the member is voting on any particular proposal
		/// for the first time and the call is successful. Subsequent vote changes will charge a
		/// fee.
		///
		/// Weight: `O(1)`, less if there was no previous vote on the poll by the member.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn vote(
			origin: OriginFor<T>,
			poll: PollIndexOf<T, I>,
			aye: bool,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let record = Self::ensure_member(&who)?;
			use VoteRecord::*;
			let votes = Self::rank_to_votes(record.rank);
			let vote = VoteRecord::from((aye, votes));
			let mut pays = Pays::Yes;

			T::Polls::try_access_poll(poll, |mut status| -> DispatchResult {
				match status {
					PollStatus::None | PollStatus::Completed(..) => Err(Error::<T, I>::NotPolling)?,
					PollStatus::Ongoing(ref mut tally, _) => {
						match Voting::<T, I>::get(&poll, &who) {
							Some(Aye(votes)) => tally.ayes.saturating_reduce(votes),
							Some(Nay(votes)) => tally.nays.saturating_reduce(votes),
							None => pays = Pays::No,
						}
						match aye {
							true => tally.ayes.saturating_accrue(votes),
							false => tally.nays.saturating_accrue(votes),
						}
						Voting::<T, I>::insert(&poll, &who, &vote);
						Self::deposit_event(Event::Voted { who, poll, vote, tally: tally.clone() });
						Ok(())
					},
				}
			})?;
			Ok(pays.into())
		}

		/// Remove votes from the given poll. It must have ended.
		///
		/// - `origin`: Must be `Signed` by any account.
		/// - `poll_index`: Index of a poll which is completed and for which votes continue to
		///   exist.
		/// - `max`: Maximum number of vote items from remove in this call.
		///
		/// Transaction fees are waived if the operation is successful.
		///
		/// Weight `O(max)` (less if there are fewer items to remove than `max`).
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn cleanup_poll(
			origin: OriginFor<T>,
			poll_index: PollIndexOf<T, I>,
			max: u32,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			ensure!(T::Polls::as_ongoing(poll_index).is_none(), Error::<T, I>::Ongoing);

			use sp_io::KillStorageResult::*;
			let _count = match Voting::<T, I>::remove_prefix(poll_index, Some(max)) {
				AllRemoved(0) => Err(Error::<T, I>::NoneRemaining)?,
				AllRemoved(n) | SomeRemaining(n) => n,
			};
			// TODO: weight from count.
			Ok(Pays::No.into())
		}
	}

	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		fn ensure_member(who: &T::AccountId) -> Result<MemberRecord, DispatchError> {
			Members::<T, I>::get(who).ok_or(Error::<T, I>::NotMember.into())
		}

		fn rank_to_votes(r: Rank) -> Votes {
			let r = r as Votes;
			r * (r + 1) / 2
		}

		pub(crate) fn member_count() -> MemberIndex {
			MemberCount::<T, I>::get().0
		}

		pub(crate) fn max_turnout() -> Votes {
			MemberCount::<T, I>::get().1
		}
	}

	impl<T: Config<I>, I: 'static> Get<Votes> for Pallet<T, I> {
		fn get() -> Votes {
			MemberCount::<T, I>::get().1
		}
	}
}
