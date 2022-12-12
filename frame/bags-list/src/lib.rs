// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! # Bags-List Pallet
//!
//! A semi-sorted list, where items hold an `AccountId` based on some `Score`. The
//! `AccountId` (`id` for short) might be synonym to a `voter` or `nominator` in some context, and
//! `Score` signifies the chance of each id being included in the final
//! [`SortedListProvider::iter`].
//!
//! It implements [`frame_election_provider_support::SortedListProvider`] to provide a semi-sorted
//! list of accounts to another pallet. It needs some other pallet to give it some information about
//! the weights of accounts via [`frame_election_provider_support::ScoreProvider`].
//!
//! This pallet is not configurable at genesis. Whoever uses it should call appropriate functions of
//! the `SortedListProvider` (e.g. `on_insert`, or `unsafe_regenerate`) at their genesis.
//!
//! # Goals
//!
//! The data structure exposed by this pallet aims to be optimized for:
//!
//! - insertions and removals.
//! - iteration over the top* N items by score, where the precise ordering of items doesn't
//!   particularly matter.
//!
//! # Details
//!
//! - items are kept in bags, which are delineated by their range of score (See
//!   [`Config::BagThresholds`]).
//! - for iteration, bags are chained together from highest to lowest and elements within the bag
//!   are iterated from head to tail.
//! - items within a bag are iterated in order of insertion. Thus removing an item and re-inserting
//!   it will worsen its position in list iteration; this reduces incentives for some types of spam
//!   that involve consistently removing and inserting for better position. Further, ordering
//!   granularity is thus dictated by range between each bag threshold.
//! - if an item's score changes to a value no longer within the range of its current bag the item's
//!   position will need to be updated by an external actor with rebag (update), or removal and
//!   insertion.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::FullCodec;
use frame_election_provider_support::{ScoreProvider, SortedListProvider};
use frame_system::ensure_signed;
use sp_runtime::traits::{AtLeast32BitUnsigned, Bounded, StaticLookup};
use sp_std::prelude::*;

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarks;

mod list;
pub mod migrations;
#[cfg(any(test, feature = "fuzz"))]
pub mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

pub use list::{notional_bag_for, Bag, List, ListError, Node};
pub use pallet::*;
pub use weights::WeightInfo;

pub(crate) const LOG_TARGET: &str = "runtime::bags_list";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] 👜 [{}]", $patter),
			<frame_system::Pallet<T>>::block_number(),
			<crate::Pallet::<T, I> as frame_support::traits::PalletInfoAccess>::name()
			$(, $values)*
		)
	};
}

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		/// Something that provides the scores of ids.
		type ScoreProvider: ScoreProvider<Self::AccountId, Score = Self::Score>;

		/// The list of thresholds separating the various bags.
		///
		/// Ids are separated into unsorted bags according to their score. This specifies the
		/// thresholds separating the bags. An id's bag is the largest bag for which the id's score
		/// is less than or equal to its upper threshold.
		///
		/// When ids are iterated, higher bags are iterated completely before lower bags. This means
		/// that iteration is _semi-sorted_: ids of higher score tend to come before ids of lower
		/// score, but peer ids within a particular bag are sorted in insertion order.
		///
		/// # Expressing the constant
		///
		/// This constant must be sorted in strictly increasing order. Duplicate items are not
		/// permitted.
		///
		/// There is an implied upper limit of `Score::MAX`; that value does not need to be
		/// specified within the bag. For any two threshold lists, if one ends with
		/// `Score::MAX`, the other one does not, and they are otherwise equal, the two
		/// lists will behave identically.
		///
		/// # Calculation
		///
		/// It is recommended to generate the set of thresholds in a geometric series, such that
		/// there exists some constant ratio such that `threshold[k + 1] == (threshold[k] *
		/// constant_ratio).max(threshold[k] + 1)` for all `k`.
		///
		/// The helpers in the `/utils/frame/generate-bags` module can simplify this calculation.
		///
		/// # Examples
		///
		/// - If `BagThresholds::get().is_empty()`, then all ids are put into the same bag, and
		///   iteration is strictly in insertion order.
		/// - If `BagThresholds::get().len() == 64`, and the thresholds are determined according to
		///   the procedure given above, then the constant ratio is equal to 2.
		/// - If `BagThresholds::get().len() == 200`, and the thresholds are determined according to
		///   the procedure given above, then the constant ratio is approximately equal to 1.248.
		/// - If the threshold list begins `[1, 2, 3, ...]`, then an id with score 0 or 1 will fall
		///   into bag 0, an id with score 2 will fall into bag 1, etc.
		///
		/// # Migration
		///
		/// In the event that this list ever changes, a copy of the old bags list must be retained.
		/// With that `List::migrate` can be called, which will perform the appropriate migration.
		#[pallet::constant]
		type BagThresholds: Get<&'static [Self::Score]>;

		/// The type used to dictate a node position relative to other nodes.
		type Score: Clone
			+ Default
			+ PartialEq
			+ Eq
			+ Ord
			+ PartialOrd
			+ sp_std::fmt::Debug
			+ Copy
			+ AtLeast32BitUnsigned
			+ Bounded
			+ TypeInfo
			+ FullCodec
			+ MaxEncodedLen;
	}

	/// A single node, within some bag.
	///
	/// Nodes store links forward and back within their respective bags.
	#[pallet::storage]
	pub(crate) type ListNodes<T: Config<I>, I: 'static = ()> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, list::Node<T, I>>;

	/// A bag stored in storage.
	///
	/// Stores a `Bag` struct, which stores head and tail pointers to itself.
	#[pallet::storage]
	pub(crate) type ListBags<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::Score, list::Bag<T, I>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// Moved an account from one bag to another.
		Rebagged { who: T::AccountId, from: T::Score, to: T::Score },
		/// Updated the score of some account to the given amount.
		ScoreUpdated { who: T::AccountId, new_score: T::Score },
	}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T, I = ()> {
		/// A error in the list interface implementation.
		List(ListError),
	}

	impl<T, I> From<ListError> for Error<T, I> {
		fn from(t: ListError) -> Self {
			Error::<T, I>::List(t)
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Declare that some `dislocated` account has, through rewards or penalties, sufficiently
		/// changed its score that it should properly fall into a different bag than its current
		/// one.
		///
		/// Anyone can call this function about any potentially dislocated account.
		///
		/// Will always update the stored score of `dislocated` to the correct score, based on
		/// `ScoreProvider`.
		///
		/// If `dislocated` does not exists, it returns an error.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::rebag_non_terminal().max(T::WeightInfo::rebag_terminal()))]
		pub fn rebag(origin: OriginFor<T>, dislocated: AccountIdLookupOf<T>) -> DispatchResult {
			ensure_signed(origin)?;
			let dislocated = T::Lookup::lookup(dislocated)?;
			let current_score = T::ScoreProvider::score(&dislocated);
			let _ = Pallet::<T, I>::do_rebag(&dislocated, current_score)
				.map_err::<Error<T, I>, _>(Into::into)?;
			Ok(())
		}

		/// Move the caller's Id directly in front of `lighter`.
		///
		/// The dispatch origin for this call must be _Signed_ and can only be called by the Id of
		/// the account going in front of `lighter`.
		///
		/// Only works if
		/// - both nodes are within the same bag,
		/// - and `origin` has a greater `Score` than `lighter`.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::put_in_front_of())]
		pub fn put_in_front_of(
			origin: OriginFor<T>,
			lighter: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let heavier = ensure_signed(origin)?;
			let lighter = T::Lookup::lookup(lighter)?;
			List::<T, I>::put_in_front_of(&lighter, &heavier)
				.map_err::<Error<T, I>, _>(Into::into)
				.map_err::<DispatchError, _>(Into::into)
		}
	}

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn integrity_test() {
			// ensure they are strictly increasing, this also implies that duplicates are detected.
			assert!(
				T::BagThresholds::get().windows(2).all(|window| window[1] > window[0]),
				"thresholds must strictly increase, and have no duplicates",
			);
		}

		#[cfg(feature = "try-runtime")]
		fn try_state(_: BlockNumberFor<T>) -> Result<(), &'static str> {
			<Self as SortedListProvider<T::AccountId>>::try_state()
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Move an account from one bag to another, depositing an event on success.
	///
	/// If the account changed bags, returns `Ok(Some((from, to)))`.
	pub fn do_rebag(
		account: &T::AccountId,
		new_score: T::Score,
	) -> Result<Option<(T::Score, T::Score)>, ListError> {
		// If no voter at that node, don't do anything. the caller just wasted the fee to call this.
		let node = list::Node::<T, I>::get(&account).ok_or(ListError::NodeNotFound)?;
		let maybe_movement = List::update_position_for(node, new_score);
		if let Some((from, to)) = maybe_movement {
			Self::deposit_event(Event::<T, I>::Rebagged { who: account.clone(), from, to });
		};
		Self::deposit_event(Event::<T, I>::ScoreUpdated { who: account.clone(), new_score });
		Ok(maybe_movement)
	}

	/// Equivalent to `ListBags::get`, but public. Useful for tests in outside of this crate.
	#[cfg(feature = "std")]
	pub fn list_bags_get(score: T::Score) -> Option<list::Bag<T, I>> {
		ListBags::get(score)
	}
}

impl<T: Config<I>, I: 'static> SortedListProvider<T::AccountId> for Pallet<T, I> {
	type Error = ListError;
	type Score = T::Score;

	fn iter() -> Box<dyn Iterator<Item = T::AccountId>> {
		Box::new(List::<T, I>::iter().map(|n| n.id().clone()))
	}

	fn iter_from(
		start: &T::AccountId,
	) -> Result<Box<dyn Iterator<Item = T::AccountId>>, Self::Error> {
		let iter = List::<T, I>::iter_from(start)?;
		Ok(Box::new(iter.map(|n| n.id().clone())))
	}

	fn count() -> u32 {
		ListNodes::<T, I>::count()
	}

	fn contains(id: &T::AccountId) -> bool {
		List::<T, I>::contains(id)
	}

	fn on_insert(id: T::AccountId, score: T::Score) -> Result<(), ListError> {
		List::<T, I>::insert(id, score)
	}

	fn get_score(id: &T::AccountId) -> Result<T::Score, ListError> {
		List::<T, I>::get_score(id)
	}

	fn on_update(id: &T::AccountId, new_score: T::Score) -> Result<(), ListError> {
		Pallet::<T, I>::do_rebag(id, new_score).map(|_| ())
	}

	fn on_remove(id: &T::AccountId) -> Result<(), ListError> {
		List::<T, I>::remove(id)
	}

	fn unsafe_regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		score_of: Box<dyn Fn(&T::AccountId) -> T::Score>,
	) -> u32 {
		// NOTE: This call is unsafe for the same reason as SortedListProvider::unsafe_regenerate.
		// I.e. because it can lead to many storage accesses.
		// So it is ok to call it as caller must ensure the conditions.
		List::<T, I>::unsafe_regenerate(all, score_of)
	}

	fn try_state() -> Result<(), &'static str> {
		List::<T, I>::try_state()
	}

	fn unsafe_clear() {
		// NOTE: This call is unsafe for the same reason as SortedListProvider::unsafe_clear.
		// I.e. because it can lead to many storage accesses.
		// So it is ok to call it as caller must ensure the conditions.
		List::<T, I>::unsafe_clear()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn score_update_worst_case(who: &T::AccountId, is_increase: bool) -> Self::Score {
		use frame_support::traits::Get as _;
		let thresholds = T::BagThresholds::get();
		let node = list::Node::<T, I>::get(who).unwrap();
		let current_bag_idx = thresholds
			.iter()
			.chain(sp_std::iter::once(&T::Score::max_value()))
			.position(|w| w == &node.bag_upper())
			.unwrap();

		if is_increase {
			let next_threshold_idx = current_bag_idx + 1;
			assert!(thresholds.len() > next_threshold_idx);
			thresholds[next_threshold_idx]
		} else {
			assert!(current_bag_idx != 0);
			let prev_threshold_idx = current_bag_idx - 1;
			thresholds[prev_threshold_idx]
		}
	}
}

impl<T: Config<I>, I: 'static> ScoreProvider<T::AccountId> for Pallet<T, I> {
	type Score = <Pallet<T, I> as SortedListProvider<T::AccountId>>::Score;

	fn score(id: &T::AccountId) -> T::Score {
		Node::<T, I>::get(id).map(|node| node.score()).unwrap_or_default()
	}

	#[cfg(any(feature = "runtime-benchmarks", feature = "fuzz", test))]
	fn set_score_of(id: &T::AccountId, new_score: T::Score) {
		ListNodes::<T, I>::mutate(id, |maybe_node| {
			if let Some(node) = maybe_node.as_mut() {
				node.set_score(new_score)
			} else {
				panic!("trying to mutate {:?} which does not exists", id);
			}
		})
	}
}
