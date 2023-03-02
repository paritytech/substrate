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

//! Additional logic for the Core Fellowship. This determines salary, registers activity/passivity
//! and handles promotion and demotion periods.
//!
//! This only handles members of non-zero rank.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "128"]

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_arithmetic::traits::{Saturating, Zero};
use sp_runtime::{traits::AtLeast32BitUnsigned};
use sp_std::{marker::PhantomData, prelude::*};

use frame_support::{
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{
		tokens::Balance as BalanceTrait,
		RankedMembers,
	},
	RuntimeDebug,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// The status of the pallet instance.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug, Default)]
pub struct ParamsType<Balance, BlockNumber> {
	/// The amounts to be paid when a given grade is active.
	active_salary: [Balance; 9],
	/// The minimum percent discount when passive.
	passive_salary: [Balance; 9],
	/// The period between which unproven members become demoted.
	demotion_period: [BlockNumber; 9],
	/// The period between which members must wait before they may proceed to this rank.
	min_promotion_period: [BlockNumber; 9],
}

/*
// move to benchmark code. No need for it here.
impl<
	Balance: BalanceTrait,
	BlockNumber: AtLeast32BitUnsigned + Copy,
> Default for ParamsType<Balance, BlockNumber> {
	fn default() -> Self {
		Self {
			active_salary: [100u32.into(); 9],
			passive_salary: [10u32.into(); 9],
			demotion_period: [100u32.into(); 9],
			min_promotion_period: [100u32.into(); 9],
		}
	}
}
*/

/// The status of a single member.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub struct MemberStatus<BlockNumber> {
	/// Are they currently active>
	is_active: bool,
	/// The block number at which we last promoted them.
	last_promotion: BlockNumber,
	/// The last time a member was demoted, promoted or proved their rank.
	last_proof: BlockNumber,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{dispatch::Pays, pallet_prelude::*, traits::{EnsureOrigin, tokens::GetSalary}};
	use frame_system::pallet_prelude::*;
	use sp_core::Get;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The runtime event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The current membership of the fellowship.
		type Members: RankedMembers<AccountId = <Self as frame_system::Config>::AccountId, Rank = u16>;

		/// The type in which salaries/budgets are measured.
		type Balance: BalanceTrait;

		/// The origin which has permission update the parameters.
		type ParamsOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin which has permission to issue a proof that a member may retain their rank.
		/// The `Success` value is the maximum rank of members it is able to prove.
		type ProofOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = RankOf<Self, I>>;

		/// The origin which has permission to promote a member. The `Success` value is the maximum
		/// rank to which it can promote.
		type PromoteOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = RankOf<Self, I>>;

		/// The period before auto-demotion that a member can be (re-)approved for their rank.
		#[pallet::constant]
		type ApprovePeriod: Get<Self::BlockNumber>;
	}

	pub type ParamsOf<T, I> =
		ParamsType<<T as Config<I>>::Balance, <T as frame_system::Config>::BlockNumber>;
	pub type MemberStatusOf<T> = MemberStatus<<T as frame_system::Config>::BlockNumber>;
	pub type RankOf<T, I> = <<T as Config<I>>::Members as RankedMembers>::Rank;

	/// The overall status of the system.
	#[pallet::storage]
	pub(super) type Params<T: Config<I>, I: 'static = ()> =
		StorageValue<_, ParamsOf<T, I>, ValueQuery>;

	/// The status of a claimant.
	#[pallet::storage]
	pub(super) type Member<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberStatusOf<T>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// Parameters for the pallet have changed.
		ParamsChanged { params: ParamsOf<T, I> },
		/// Member activity flag has been set.
		ActiveChanged { who: T::AccountId, is_active: bool },
		/// Member has begun being tracked in this pallet (i.e. because rank is now non-zero).
		Inducted { who: T::AccountId },
		/// Member has been removed from being tracked in this pallet (i.e. because rank is now
		/// zero).
		Offboarded { who: T::AccountId },
		/// Member has been promoted to the given rank.
		Promoted { who: T::AccountId, to_rank: RankOf<T, I> },
		/// Member has been demoted to the given (non-zero) rank.
		Demoted { who: T::AccountId, to_rank: RankOf<T, I> },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Member's rank is too low.
		Unranked,
		/// Member's rank is not zero.
		Ranked,
		/// Member's rank is not as expected.
		UnexpectedRank,
		/// The given rank is invalid - this generally means it's not between 1 and 9.
		InvalidRank,
		/// The account is not a member of the collective.
		NotMember,
		/// The member is not tracked by this pallet (call `prove` on member first).
		NotProved,
		/// The origin does not have enough permission to do this operation.
		NoPermission,
		/// No work needs to be done at present for this member.
		NothingDoing,
		/// The candidate has already been inducted. This should never happen since it would require
		/// a candidate (rank 0) to already be tracked in the pallet.
		AlreadyInducted,
		/// The candidate has not been inducted, so cannot be offboarded from this pallet.
		NotInducted,
		/// Operation cannot be done yet since not enough time has passed.
		TooSoon,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Bump the state of a member.
		///
		/// This will demote a member whose `last_proof` is now beyond their rank's
		/// `demotion_period`.
		///
		/// - `origin`: A `Signed` origin of an account.
		/// - `who`: A member account whose state is to be updated.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(0)]
		pub fn bump(origin: OriginFor<T>, who: T::AccountId) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			let mut member = Member::<T, I>::get(&who).ok_or(Error::<T, I>::NotProved)?;
			let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			
			let params = Params::<T, I>::get();
			let rank_index = Self::rank_to_index(rank).ok_or(Error::<T, I>::InvalidRank)?;
			let demotion_period = params.demotion_period[rank_index];
			let demotion_block = member.last_proof.saturating_add(demotion_period);
			
			// Ensure enough time has passed.
			let now = frame_system::Pallet::<T>::block_number();
			if now >= demotion_block {
				let to_rank = rank.clone().saturating_less_one();
				T::Members::demote(&who)?;
				let event = if to_rank.is_zero() {
					Member::<T, I>::remove(&who);
					Event::<T, I>::Offboarded { who }
				} else {
					member.last_proof = now;
					Member::<T, I>::insert(&who, &member);
					Event::<T, I>::Demoted { who, to_rank }
				};
				Self::deposit_event(event);
				return Ok(Pays::No.into());
			}

			Err(Error::<T, I>::NothingDoing.into())
		}

		/// Set the parameters.
		///
		/// - `origin`: A origin complying with `ParamsOrigin`.
		/// - `params`: The new parameters for the pallet.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(1)]
		pub fn set_params(origin: OriginFor<T>, params: ParamsOf<T, I>) -> DispatchResultWithPostInfo {
			T::ParamsOrigin::ensure_origin(origin)?;
			Params::<T, I>::put(&params);
			Self::deposit_event(Event::<T, I>::ParamsChanged { params });
			Ok(Pays::No.into())
		}

		/// Set whether a member is active or not.
		///
		/// - `origin`: A `Signed` origin of a member's account.
		/// - `active`: `true` iff the member is active.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(2)]
		pub fn set_active(origin: OriginFor<T>, is_active: bool) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(T::Members::rank_of(&who).map_or(false, |r| !r.is_zero()), Error::<T, I>::Unranked);
			let mut member = Member::<T, I>::get(&who).ok_or(Error::<T, I>::NotProved)?;
			member.is_active = is_active;
			Member::<T, I>::insert(&who, &member);
			Self::deposit_event(Event::<T, I>::ActiveChanged { who, is_active });
			Ok(())
		}

		/// Approve a member to continue at their rank.
		///
		/// This resets `last_proof` to the current block, thereby delaying any automatic demotion.
		///
		/// If `who` is not already tracked by this pallet, then it will become tracked.
		/// `last_promotion` will be set to zero.
		///
		/// - `origin`: An origin which satisfies `ProofOrigin`.
		/// - `who`: A member (i.e. of non-zero rank).
		/// - `at_rank`: The rank of member.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(3)]
		pub fn prove(origin: OriginFor<T>, who: T::AccountId, at_rank: RankOf<T, I>) -> DispatchResultWithPostInfo {
			let allow_rank = T::ProofOrigin::ensure_origin(origin)?;
			ensure!(allow_rank >= at_rank, Error::<T, I>::NoPermission);
			let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			ensure!(rank == at_rank, Error::<T, I>::UnexpectedRank);

			// Maybe consider requiring it be at least `ApprovePeriod` prior to the auto-demotion.
			let now = frame_system::Pallet::<T>::block_number();
			let mut member = Member::<T, I>::get(&who).unwrap_or_else(|| MemberStatus {
				is_active: true,
				last_promotion: 0u32.into(),
				last_proof: now,
			});
			member.last_proof = now;

			Ok(Pays::No.into())
		}

		/// Make a "promotion" from a candiate (rank zero) into a member (rank one).
		///
		/// - `origin`: An origin which satisfies `PromoteOrigin` with a `Success` result of 1 or
		///   more.
		/// - `who`: The account ID of the candidate to be inducted and become a member.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(4)]
		pub fn induct(origin: OriginFor<T>, who: T::AccountId) -> DispatchResultWithPostInfo {
			let allow_rank = T::PromoteOrigin::ensure_origin(origin)?;
			ensure!(allow_rank >= 1, Error::<T, I>::NoPermission);
			let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			ensure!(rank.is_zero(), Error::<T, I>::UnexpectedRank);
			ensure!(!Member::<T, I>::contains_key(&who), Error::<T, I>::AlreadyInducted);

			T::Members::promote(&who)?;
			let now = frame_system::Pallet::<T>::block_number();
			Member::<T, I>::insert(&who, MemberStatus {
				is_active: true,
				last_promotion: now,
				last_proof: now,
			});
			Self::deposit_event(Event::<T, I>::Inducted { who });
			Ok(Pays::No.into())
		}

		/// Make a promotion from a non-zero rank.
		///
		/// - `origin`: An origin which satisfies `PromoteOrigin` with a `Success` result of
		///   `to_rank` or more.
		/// - `who`: The account ID of the member to be promoted to `to_rank`.
		/// - `to_rank`: One more than the current rank of `who`.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(5)]
		pub fn promote(origin: OriginFor<T>, who: T::AccountId, to_rank: RankOf<T, I>) -> DispatchResultWithPostInfo {
			let allow_rank = T::PromoteOrigin::ensure_origin(origin)?;
			ensure!(allow_rank >= to_rank, Error::<T, I>::NoPermission);

			let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			ensure!(rank.checked_add(1).map_or(false, |i| i == to_rank), Error::<T, I>::UnexpectedRank);

			let mut member = Member::<T, I>::get(&who).ok_or(Error::<T, I>::Unranked)?;
			let now = frame_system::Pallet::<T>::block_number();

			let params = Params::<T, I>::get();
			let rank_index = Self::rank_to_index(to_rank).ok_or(Error::<T, I>::InvalidRank)?;
			let min_period = params.min_promotion_period[rank_index];
			// Ensure enough time has passed.
			ensure!(member.last_promotion.saturating_add(min_period) < now, Error::<T, I>::TooSoon);

			T::Members::promote(&who)?;
			member.last_promotion = now;
			member.last_proof = now;
			Member::<T, I>::insert(&who, &member);

			Self::deposit_event(Event::<T, I>::Promoted { who, to_rank });

			Ok(Pays::No.into())
		}

		/// Make a "promotion" from a candiate (rank zero) into a member (rank one).
		///
		/// - `origin`: An origin which satisfies `PromoteOrigin` with a `Success` result of 1 or
		///   more.
		/// - `who`: The account ID of the candidate to be inducted and become a member.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(6)]
		pub fn offboard(origin: OriginFor<T>, who: T::AccountId) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			ensure!(T::Members::rank_of(&who).map_or(true, |r| r.is_zero()), Error::<T, I>::Ranked);
			ensure!(Member::<T, I>::contains_key(&who), Error::<T, I>::NotInducted);
			Member::<T, I>::remove(&who);
			Self::deposit_event(Event::<T, I>::Offboarded { who });
			Ok(Pays::No.into())
		}
	}

	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Convert a rank into a 0..9 index suitable for the arrays in Params.
		///
		/// Rank 1 becomes index 0, rank 9 becomes index 8. Any rank not in the range 1..=9 is
		/// `None`.
		pub(crate) fn rank_to_index(rank: RankOf<T, I>) -> Option<usize> {
			match TryInto::<usize>::try_into(rank) {
				Ok(r) if r <= 9 && r > 0 => Some(r - 1),
				_ => return None,
			}
		}
	}

	impl<T: Config<I>, I: 'static> GetSalary<RankOf<T, I>, T::AccountId, T::Balance> for Pallet<T, I> {
		fn get_salary(rank: RankOf<T, I>, who: &T::AccountId) -> T::Balance {
			let index = match Self::rank_to_index(rank) { Some(i) => i, None => return Zero::zero() };
			let member = match Member::<T, I>::get(who) { Some(m) => m, None => return Zero::zero() };
			let params = Params::<T, I>::get();
			let salary = if member.is_active { params.active_salary } else { params.passive_salary };
			salary[index]
		}
	}
}
