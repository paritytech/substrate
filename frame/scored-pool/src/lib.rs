// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Scored Pool Module
//!
//! The module maintains a scored membership pool. Each entity in the
//! pool can be attributed a `Score`. From this pool a set `Members`
//! is constructed. This set contains the `MemberCount` highest
//! scoring entities. Unscored entities are never part of `Members`.
//!
//! If an entity wants to be part of the pool a deposit is required.
//! The deposit is returned when the entity withdraws or when it
//! is removed by an entity with the appropriate authority.
//!
//! Every `Period` blocks the set of `Members` is refreshed from the
//! highest scoring members in the pool and, no matter if changes
//! occurred, `T::MembershipChanged::set_members_sorted` is invoked.
//! On first load `T::MembershipInitialized::initialize_members` is
//! invoked with the initial `Members` set.
//!
//! It is possible to withdraw candidacy/resign your membership at any
//! time. If an entity is currently a member, this results in removal
//! from the `Pool` and `Members`; the entity is immediately replaced
//! by the next highest scoring candidate in the pool, if available.
//!
//! - [`scored_pool::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `submit_candidacy` - Submit candidacy to become a member. Requires a deposit.
//! - `withdraw_candidacy` - Withdraw candidacy. Deposit is returned.
//! - `score` - Attribute a quantitative score to an entity.
//! - `kick` - Remove an entity from the pool and members. Deposit is returned.
//! - `change_member_count` - Changes the amount of candidates taken into `Members`.
//!
//! ## Usage
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::ensure_signed;
//! use pallet_scored_pool::{self as scored_pool};
//!
//! pub trait Trait: scored_pool::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		#[weight = 0]
//! 		pub fn candidate(origin) -> dispatch::DispatchResult {
//! 			let who = ensure_signed(origin)?;
//!
//! 			let _ = <scored_pool::Module<T>>::submit_candidacy(
//! 				T::Origin::from(Some(who.clone()).into())
//! 			);
//! 			Ok(())
//! 		}
//! 	}
//! }
//!
//! # fn main() { }
//! ```
//!
//! ## Dependencies
//!
//! This module depends on the [System module](../frame_system/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use codec::FullCodec;
use sp_std::{
	fmt::Debug,
	prelude::*,
};
use frame_support::{
	decl_module, decl_storage, decl_event, ensure, decl_error,
	traits::{EnsureOrigin, ChangeMembers, InitializeMembers, Currency, Get, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_root, ensure_signed};
use sp_runtime::traits::{AtLeast32Bit, MaybeSerializeDeserialize, Zero, StaticLookup};

type BalanceOf<T, I> = <<T as Trait<I>>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type PoolT<T, I> = Vec<(<T as frame_system::Trait>::AccountId, Option<<T as Trait<I>>::Score>)>;

/// The enum is supplied when refreshing the members set.
/// Depending on the enum variant the corresponding associated
/// type function will be invoked.
enum ChangeReceiver {
	/// Should call `T::MembershipInitialized`.
	MembershipInitialized,
	/// Should call `T::MembershipChanged`.
	MembershipChanged,
}

pub trait Trait<I=DefaultInstance>: frame_system::Trait {
	/// The currency used for deposits.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// The score attributed to a member or candidate.
	type Score:
		AtLeast32Bit + Clone + Copy + Default + FullCodec + MaybeSerializeDeserialize + Debug;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as frame_system::Trait>::Event>;

	// The deposit which is reserved from candidates if they want to
	// start a candidacy. The deposit gets returned when the candidacy is
	// withdrawn or when the candidate is kicked.
	type CandidateDeposit: Get<BalanceOf<Self, I>>;

	/// Every `Period` blocks the `Members` are filled with the highest scoring
	/// members in the `Pool`.
	type Period: Get<Self::BlockNumber>;

	/// The receiver of the signal for when the membership has been initialized.
	/// This happens pre-genesis and will usually be the same as `MembershipChanged`.
	/// If you need to do something different on initialization, then you can change
	/// this accordingly.
	type MembershipInitialized: InitializeMembers<Self::AccountId>;

	/// The receiver of the signal for when the members have changed.
	type MembershipChanged: ChangeMembers<Self::AccountId>;

	/// Allows a configurable origin type to set a score to a candidate in the pool.
	type ScoreOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for removing a member (though can always be Root).
	/// Configurable origin which enables removing an entity. If the entity
	/// is part of the `Members` it is immediately replaced by the next
	/// highest scoring candidate, if available.
	type KickOrigin: EnsureOrigin<Self::Origin>;
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as ScoredPool {
		/// The current pool of candidates, stored as an ordered Vec
		/// (ordered descending by score, `None` last, highest first).
		Pool get(fn pool) config(): PoolT<T, I>;

		/// A Map of the candidates. The information in this Map is redundant
		/// to the information in the `Pool`. But the Map enables us to easily
		/// check if a candidate is already in the pool, without having to
		/// iterate over the entire pool (the `Pool` is not sorted by
		/// `T::AccountId`, but by `T::Score` instead).
		CandidateExists get(fn candidate_exists): map hasher(twox_64_concat) T::AccountId => bool;

		/// The current membership, stored as an ordered Vec.
		Members get(fn members): Vec<T::AccountId>;

		/// Size of the `Members` set.
		MemberCount get(fn member_count) config(): u32;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(phantom): sp_std::marker::PhantomData<I>;
		build(|config| {
			let mut pool = config.pool.clone();

			// reserve balance for each candidate in the pool.
			// panicking here is ok, since this just happens one time, pre-genesis.
			pool
				.iter()
				.for_each(|(who, _)| {
					T::Currency::reserve(&who, T::CandidateDeposit::get())
						.expect("balance too low to create candidacy");
					<CandidateExists<T, I>>::insert(who, true);
				});

			// Sorts the `Pool` by score in a descending order. Entities which
			// have a score of `None` are sorted to the beginning of the vec.
			pool.sort_by_key(|(_, maybe_score)|
				Reverse(maybe_score.unwrap_or_default())
			);

			<Pool<T, I>>::put(&pool);
			<Module<T, I>>::refresh_members(pool, ChangeReceiver::MembershipInitialized);
		})
	}
}

decl_event!(
	pub enum Event<T, I=DefaultInstance> where
		<T as frame_system::Trait>::AccountId,
	{
		/// The given member was removed. See the transaction for who.
		MemberRemoved,
		/// An entity has issued a candidacy. See the transaction for who.
		CandidateAdded,
		/// An entity withdrew candidacy. See the transaction for who.
		CandidateWithdrew,
		/// The candidacy was forcefully removed for an entity.
		/// See the transaction for who.
		CandidateKicked,
		/// A score was attributed to the candidate.
		/// See the transaction for who.
		CandidateScored,
		/// Phantom member, never used.
		Dummy(sp_std::marker::PhantomData<(AccountId, I)>),
	}
);

decl_error! {
	/// Error for the scored-pool module.
	pub enum Error for Module<T: Trait<I>, I: Instance> {
		/// Already a member.
		AlreadyInPool,
		/// Index out of bounds.
		InvalidIndex,
		/// Index does not match requested account.
		WrongAccountIndex,
	}
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		type Error = Error<T, I>;

		fn deposit_event() = default;

		/// Every `Period` blocks the `Members` set is refreshed from the
		/// highest scoring members in the pool.
		fn on_initialize(n: T::BlockNumber) -> Weight {
			if n % T::Period::get() == Zero::zero() {
				let pool = <Pool<T, I>>::get();
				<Module<T, I>>::refresh_members(pool, ChangeReceiver::MembershipChanged);
			}
			0
		}

		/// Add `origin` to the pool of candidates.
		///
		/// This results in `CandidateDeposit` being reserved from
		/// the `origin` account. The deposit is returned once
		/// candidacy is withdrawn by the candidate or the entity
		/// is kicked by `KickOrigin`.
		///
		/// The dispatch origin of this function must be signed.
		///
		/// The `index` parameter of this function must be set to
		/// the index of the transactor in the `Pool`.
		#[weight = 0]
		pub fn submit_candidacy(origin) {
			let who = ensure_signed(origin)?;
			ensure!(!<CandidateExists<T, I>>::contains_key(&who), Error::<T, I>::AlreadyInPool);

			let deposit = T::CandidateDeposit::get();
			T::Currency::reserve(&who, deposit)?;

			// can be inserted as last element in pool, since entities with
			// `None` are always sorted to the end.
			<Pool<T, I>>::append((who.clone(), Option::<<T as Trait<I>>::Score>::None));

			<CandidateExists<T, I>>::insert(&who, true);

			Self::deposit_event(RawEvent::CandidateAdded);
		}

		/// An entity withdraws candidacy and gets its deposit back.
		///
		/// If the entity is part of the `Members`, then the highest member
		/// of the `Pool` that is not currently in `Members` is immediately
		/// placed in the set instead.
		///
		/// The dispatch origin of this function must be signed.
		///
		/// The `index` parameter of this function must be set to
		/// the index of the transactor in the `Pool`.
		#[weight = 0]
		pub fn withdraw_candidacy(
			origin,
			index: u32
		) {
			let who = ensure_signed(origin)?;

			let pool = <Pool<T, I>>::get();
			Self::ensure_index(&pool, &who, index)?;

			Self::remove_member(pool, who, index)?;
			Self::deposit_event(RawEvent::CandidateWithdrew);
		}

		/// Kick a member `who` from the set.
		///
		/// May only be called from `T::KickOrigin`.
		///
		/// The `index` parameter of this function must be set to
		/// the index of `dest` in the `Pool`.
		#[weight = 0]
		pub fn kick(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			index: u32
		) {
			T::KickOrigin::ensure_origin(origin)?;

			let who = T::Lookup::lookup(dest)?;

			let pool = <Pool<T, I>>::get();
			Self::ensure_index(&pool, &who, index)?;

			Self::remove_member(pool, who, index)?;
			Self::deposit_event(RawEvent::CandidateKicked);
		}

		/// Score a member `who` with `score`.
		///
		/// May only be called from `T::ScoreOrigin`.
		///
		/// The `index` parameter of this function must be set to
		/// the index of the `dest` in the `Pool`.
		#[weight = 0]
		pub fn score(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			index: u32,
			score: T::Score
		) {
			T::ScoreOrigin::ensure_origin(origin)?;

			let who = T::Lookup::lookup(dest)?;

			let mut pool = <Pool<T, I>>::get();
			Self::ensure_index(&pool, &who, index)?;

			pool.remove(index as usize);

			// we binary search the pool (which is sorted descending by score).
			// if there is already an element with `score`, we insert
			// right before that. if not, the search returns a location
			// where we can insert while maintaining order.
			let item = (who, Some(score.clone()));
			let location = pool
				.binary_search_by_key(
					&Reverse(score),
					|(_, maybe_score)| Reverse(maybe_score.unwrap_or_default())
				)
				.unwrap_or_else(|l| l);
			pool.insert(location, item);

			<Pool<T, I>>::put(&pool);
			Self::deposit_event(RawEvent::CandidateScored);
		}

		/// Dispatchable call to change `MemberCount`.
		///
		/// This will only have an effect the next time a refresh happens
		/// (this happens each `Period`).
		///
		/// May only be called from root.
		#[weight = 0]
		pub fn change_member_count(origin, count: u32) {
			ensure_root(origin)?;
			<MemberCount<I>>::put(&count);
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {

	/// Fetches the `MemberCount` highest scoring members from
	/// `Pool` and puts them into `Members`.
	///
	/// The `notify` parameter is used to deduct which associated
	/// type function to invoke at the end of the method.
	fn refresh_members(
		pool: PoolT<T, I>,
		notify: ChangeReceiver
	) {
		let count = <MemberCount<I>>::get();

		let mut new_members: Vec<T::AccountId> = pool
			.into_iter()
			.filter(|(_, score)| score.is_some())
			.take(count as usize)
			.map(|(account_id, _)| account_id)
			.collect();
		new_members.sort();

		let old_members = <Members<T, I>>::get();
		<Members<T, I>>::put(&new_members);

		match notify {
			ChangeReceiver::MembershipInitialized =>
				T::MembershipInitialized::initialize_members(&new_members),
			ChangeReceiver::MembershipChanged =>
				T::MembershipChanged::set_members_sorted(
					&new_members[..],
					&old_members[..],
				),
		}
	}

	/// Removes an entity `remove` at `index` from the `Pool`.
	///
	/// If the entity is a member it is also removed from `Members` and
	/// the deposit is returned.
	fn remove_member(
		mut pool: PoolT<T, I>,
		remove: T::AccountId,
		index: u32
	) -> Result<(), Error<T, I>> {
		// all callers of this function in this module also check
		// the index for validity before calling this function.
		// nevertheless we check again here, to assert that there was
		// no mistake when invoking this sensible function.
		Self::ensure_index(&pool, &remove, index)?;

		pool.remove(index as usize);
		<Pool<T, I>>::put(&pool);

		// remove from set, if it was in there
		let members = <Members<T, I>>::get();
		if members.binary_search(&remove).is_ok() {
			Self::refresh_members(pool, ChangeReceiver::MembershipChanged);
		}

		<CandidateExists<T, I>>::remove(&remove);

		T::Currency::unreserve(&remove, T::CandidateDeposit::get());

		Self::deposit_event(RawEvent::MemberRemoved);
		Ok(())
	}

	/// Checks if `index` is a valid number and if the element found
	/// at `index` in `Pool` is equal to `who`.
	fn ensure_index(
		pool: &PoolT<T, I>,
		who: &T::AccountId,
		index: u32
	) -> Result<(), Error<T, I>> {
		ensure!(index < pool.len() as u32, Error::<T, I>::InvalidIndex);

		let (index_who, _index_score) = &pool[index as usize];
		ensure!(index_who == who, Error::<T, I>::WrongAccountIndex);

		Ok(())
	}
}
