// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! # Scored Pool Module
//!
//! The module maintains a scored membership pool. Each entity in the
//! pool can be attributed a `Score`. From this pool a set `Members`
//! is constructed. This set contains the `MemberCount` highest
//! scoring entities. Unscored entities are never part of `Members`.
//!
//! If an entity wants to be part of the pool a deposit is required.
//! The deposit is returned when the entity withdraws (or when it
//! is removed by an entity with the appropriate authority).
//!
//! Every `Period` blocks the set of `Members` is refreshed from the
//! highest scoring members in the pool and, no matter if changes
//! occurred, `T::MembersChanged::change_members` is invoked.
//!
//! It is possible to withdraw candidacy/resign your membership at any
//! time. If an entity is currently a member, this results in removal
//! from the `Pool` and `Members` and the entity is immediately replaced
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
//! - `issue_candidacy` - Issue candidacy to become a member. Requires a deposit.
//! - `withdraw_candidacy` - Withdraw candidacy. Deposit is returned.
//! - `score` - Attribute a quantitative score to an entity.
//! - `kick` - Remove an entity from the pool and members. Deposit is returned.
//! - `change_member_count` - Changes the amount of candidates taken into `Members`.
//!
//! ## Usage
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result, traits::ChangeMembers};
//! use system::ensure_signed;
//! use srml_scored_pool::{self as scored_pool};
//!
//! pub trait Trait: scored_pool::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn candidate(origin) -> Result {
//! 			let who = ensure_signed(origin)?;
//!
//! 			let _ = <scored_pool::Module<T>>::issue_candidacy(
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
//! This module depends on the [System module](../srml_system/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use codec::{Encode, Decode};
use sr_std::prelude::*;
use srml_support::{
	StorageValue, decl_module, decl_storage, decl_event,
	traits::{ChangeMembers, Currency, Get, ReservableCurrency},
};
use system::{self, ensure_root, ensure_signed};
use sr_primitives::{
	traits::{EnsureOrigin, SimpleArithmetic, MaybeSerializeDebug, Zero},
};

type BalanceOf<T, I> = <<T as Trait<I>>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait<I=DefaultInstance>: system::Trait {
	/// The currency used for deposits.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// The score attributed to a member or candidate.
	type Score: SimpleArithmetic + Clone + Default + Encode + Decode + MaybeSerializeDebug;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;

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
	type MembershipInitialized: ChangeMembers<Self::AccountId>;

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
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Membership {
		/// The current pool of candidates, stored as an ordered Vec
		/// (ordered ascending by score, `None` first, highest last).
		Pool get(pool) config(): Vec<(T::AccountId, Option<T::Score>)>;

		/// The current membership, stored as an ordered Vec.
		Members get(members): Vec<T::AccountId>;

		/// Size of the `Members` set.
		MemberCount get(member_count) config(): u32;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(phantom): sr_std::marker::PhantomData<I>;
		build(|
			storage: &mut (sr_primitives::StorageOverlay, sr_primitives::ChildrenStorageOverlay),
			config: &GenesisConfig<T, I>
		| {
			sr_io::with_storage(storage, || {
				let mut pool = config.pool.clone();

				// reserve balance for each candidate in the pool.
				// panicking here is ok, since this just happens one time, pre-genesis.
				pool
					.iter()
					.for_each(|(who, _)| {
						T::Currency::reserve(&who, T::CandidateDeposit::get())
							.expect("balance too low");
					});

				<Module<T, I>>::sort_pool(&mut pool);
				<Pool<T, I>>::put(&pool);
				<Module<T, I>>::refresh_members(false);

				let members = <Members<T, I>>::get();
				T::MembershipInitialized::set_members_sorted(&members[..], &[]);
			});
		})
	}
}

decl_event!(
	pub enum Event<T, I=DefaultInstance> where
		<T as system::Trait>::AccountId,
	{
		/// The given member was removed; see the transaction for who.
		MemberRemoved,
		/// An entity has issued a candidacy.
		CandidateAdded,
		/// An entity withdrew candidacy.
		CandidateWithdrew,
		/// The candidacy was forcefully removed for an entity.
		CandidateKicked,
		/// Phantom member, never used.
		Dummy(sr_std::marker::PhantomData<(AccountId, I)>),
	}
);

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		fn deposit_event<T, I>() = default;

		/// Every `Period` blocks the `Members` set is refreshed from the
		/// highest scoring members in the pool.
		fn on_initialize(n: T::BlockNumber) {
			if n % T::Period::get() == T::BlockNumber::zero() {
				<Module<T, I>>::refresh_members(true);
			}
		}

		/// Add `origin` to the pool of candidates.
		pub fn issue_candidacy(origin) {
			let who = ensure_signed(origin)?;

			let _ = Self::find_in_pool(&who)
				.ok()
				.map_or_else(
					|| Ok(()),
					|_| Err("already a member"),
				)?;

			T::Currency::reserve(&who, T::CandidateDeposit::get())
				.map_err(|_| "balance too low")?;

			let mut pool = <Pool<T, I>>::get();
			pool.push((who.clone(), None));
			Self::sort_pool(&mut pool);
			<Pool<T, I>>::put(&pool);

			Self::deposit_event(RawEvent::CandidateAdded);
		}

		/// An entity withdraws candidacy and gets its deposit back.
		///
		/// If the entity is part of the `Members`, then the highest member
		/// of the `Pool` that is not currently in `Members` is immediately
		/// placed in the set instead.
		pub fn withdraw_candidacy(origin) {
			let who = ensure_signed(origin)?;

			Self::remove_member(who)?;
			Self::deposit_event(RawEvent::CandidateWithdrew);
		}

		/// Kick a member `who` from the set.
		///
		/// May only be called from `KickOrigin` or root.
		pub fn kick(origin, who: T::AccountId) {
			T::KickOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			Self::remove_member(who)?;
			Self::deposit_event(RawEvent::CandidateKicked);
		}

		/// Score a member `who` with `score`.
		///
		/// May only be called from `ScoreOrigin` or root.
		pub fn score(origin, who: T::AccountId, score: T::Score) {
			T::ScoreOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let mut pool = <Pool<T, I>>::get();
			let location = Self::find_in_pool(&who)?;
			pool.remove(location);
			pool.push((who.clone(), Some(score.clone())));
			Self::sort_pool(&mut pool);

			<Pool<T, I>>::put(&pool);
		}

		/// Root-dispatchable call to change `MemberCount`.
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
	/// If `notify` is set to true `T::MembershipChanged::change_members_sorted`
	/// will be invoked at the end of the method.
	fn refresh_members(notify: bool) {
		let count = <MemberCount<I>>::get();

		let pool = <Pool<T, I>>::get();
		let mut new_members: Vec<T::AccountId> = pool
			.into_iter()
			.filter(|(_, score)| score.is_some())
			.rev()
			.take(count as usize)
			.map(|(account_id, _)| account_id)
			.collect();
		new_members.sort();

		let old_members = <Members<T, I>>::get();
		<Members<T, I>>::put(&new_members);

		let outgoing: Vec<T::AccountId> = old_members.clone()
			.into_iter()
			.filter(|old| new_members.binary_search(&old).is_err())
			.collect();
		let incoming: Vec<T::AccountId> = new_members.clone()
			.into_iter()
			.filter(|new| old_members.binary_search(&new).is_err())
			.collect();

		if notify {
			T::MembershipChanged::change_members_sorted(
				&incoming[..],
				&outgoing[..],
				&new_members[..]
			);
		}
	}

	/// Sorts the `Pool` by score in an ascending order. Entities which
	/// have a score of `None` are sorted to the beginning of the vec.
	fn sort_pool(pool: &mut Vec<(T::AccountId, Option<T::Score>)>) {
		pool.sort_by_key(|(_who, maybe_score)|
			Option::unwrap_or_default(maybe_score.clone())
		);
	}

	/// Find an entity in the pool.
	///
	/// Returns its position in the `Pool` vec, if found.
	fn find_in_pool(seek: &T::AccountId) -> Result<usize, &'static str> {
		let pool = <Pool<T, I>>::get();
		// we can't use binary search here since the pool is sorted by score
		pool
			.iter()
			.position(|(who, _score)| who == seek)
			.ok_or("not a member")
	}

	/// Removes an entity from the `Pool` and also from `Members`,
	/// if it's a member. In the latter case the deposit is returned.
	fn remove_member(remove: T::AccountId) -> Result<(), &'static str> {
		// remove from pool
		let mut pool = <Pool<T, I>>::get();
		let location = Self::find_in_pool(&remove)?;
		pool.remove(location);
		<Pool<T, I>>::put(&pool);

		// remove from set, if it was in there
		let members = <Members<T, I>>::get();
		let maybe_location = members.binary_search(&remove);
		if let Ok(_location) = maybe_location {
			Self::refresh_members(true);
		}

		T::Currency::unreserve(&remove, T::CandidateDeposit::get());

		Self::deposit_event(RawEvent::MemberRemoved);
		Ok(())
	}
}
