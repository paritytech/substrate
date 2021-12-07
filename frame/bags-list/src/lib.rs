// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
//! A semi-sorted list, where items hold an `AccountId` based on some `VoteWeight`. The `AccountId`
//! (`id` for short) might be synonym to a `voter` or `nominator` in some context, and `VoteWeight`
//! signifies the chance of each id being included in the final [`SortedListProvider::iter`].
//!
//! It implements [`frame_election_provider_support::SortedListProvider`] to provide a semi-sorted
//! list of accounts to another pallet. It needs some other pallet to give it some information about
//! the weights of accounts via [`frame_election_provider_support::VoteWeightProvider`].
//!
//! This pallet is not configurable at genesis. Whoever uses it should call appropriate functions of
//! the `SortedListProvider` (e.g. `on_insert`, or `unsafe_regenerate`) at their genesis.
//!
//! # Goals
//!
//! The data structure exposed by this pallet aims to be optimized for:
//!
//! - insertions and removals.
//! - iteration over the top* N items by weight, where the precise ordering of items doesn't
//!   particularly matter.
//!
//! # Details
//!
//! - items are kept in bags, which are delineated by their range of weight (See
//!   [`Config::BagThresholds`]).
//! - for iteration, bags are chained together from highest to lowest and elements within the bag
//!   are iterated from head to tail.
//! - items within a bag are iterated in order of insertion. Thus removing an item and re-inserting
//!   it will worsen its position in list iteration; this reduces incentives for some types of spam
//!   that involve consistently removing and inserting for better position. Further, ordering
//!   granularity is thus dictated by range between each bag threshold.
//! - if an item's weight changes to a value no longer within the range of its current bag the
//!   item's position will need to be updated by an external actor with rebag (update), or removal
//!   and insertion.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_election_provider_support::{SortedListProvider, VoteWeight, VoteWeightProvider};
use frame_system::ensure_signed;
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

pub use list::{notional_bag_for, Bag, Error, List, Node};
pub use pallet::*;
pub use weights::WeightInfo;

pub(crate) const LOG_TARGET: &'static str = "runtime::bags_list";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] 👜", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
		)
	};
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		/// Something that provides the weights of ids.
		type VoteWeightProvider: VoteWeightProvider<Self::AccountId>;

		/// The list of thresholds separating the various bags.
		///
		/// Ids are separated into unsorted bags according to their vote weight. This specifies the
		/// thresholds separating the bags. An id's bag is the largest bag for which the id's weight
		/// is less than or equal to its upper threshold.
		///
		/// When ids are iterated, higher bags are iterated completely before lower bags. This means
		/// that iteration is _semi-sorted_: ids of higher weight tend to come before ids of lower
		/// weight, but peer ids within a particular bag are sorted in insertion order.
		///
		/// # Expressing the constant
		///
		/// This constant must be sorted in strictly increasing order. Duplicate items are not
		/// permitted.
		///
		/// There is an implied upper limit of `VoteWeight::MAX`; that value does not need to be
		/// specified within the bag. For any two threshold lists, if one ends with
		/// `VoteWeight::MAX`, the other one does not, and they are otherwise equal, the two lists
		/// will behave identically.
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
		/// - If the threshold list begins `[1, 2, 3, ...]`, then an id with weight 0 or 1 will fall
		///   into bag 0, an id with weight 2 will fall into bag 1, etc.
		///
		/// # Migration
		///
		/// In the event that this list ever changes, a copy of the old bags list must be retained.
		/// With that `List::migrate` can be called, which will perform the appropriate migration.
		#[pallet::constant]
		type BagThresholds: Get<&'static [VoteWeight]>;
	}

	/// A single node, within some bag.
	///
	/// Nodes store links forward and back within their respective bags.
	#[pallet::storage]
	pub(crate) type ListNodes<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, list::Node<T>>;

	/// A bag stored in storage.
	///
	/// Stores a `Bag` struct, which stores head and tail pointers to itself.
	#[pallet::storage]
	pub(crate) type ListBags<T: Config> = StorageMap<_, Twox64Concat, VoteWeight, list::Bag<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Moved an account from one bag to another.
		Rebagged { who: T::AccountId, from: VoteWeight, to: VoteWeight },
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Declare that some `dislocated` account has, through rewards or penalties, sufficiently
		/// changed its weight that it should properly fall into a different bag than its current
		/// one.
		///
		/// Anyone can call this function about any potentially dislocated account.
		///
		/// Will never return an error; if `dislocated` does not exist or doesn't need a rebag, then
		/// it is a noop and fees are still collected from `origin`.
		#[pallet::weight(T::WeightInfo::rebag_non_terminal().max(T::WeightInfo::rebag_terminal()))]
		pub fn rebag(origin: OriginFor<T>, dislocated: T::AccountId) -> DispatchResult {
			ensure_signed(origin)?;
			let current_weight = T::VoteWeightProvider::vote_weight(&dislocated);
			let _ = Pallet::<T>::do_rebag(&dislocated, current_weight);
			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			// ensure they are strictly increasing, this also implies that duplicates are detected.
			assert!(
				T::BagThresholds::get().windows(2).all(|window| window[1] > window[0]),
				"thresholds must strictly increase, and have no duplicates",
			);
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Move an account from one bag to another, depositing an event on success.
	///
	/// If the account changed bags, returns `Some((from, to))`.
	pub fn do_rebag(
		account: &T::AccountId,
		new_weight: VoteWeight,
	) -> Option<(VoteWeight, VoteWeight)> {
		// if no voter at that node, don't do anything.
		// the caller just wasted the fee to call this.
		let maybe_movement = list::Node::<T>::get(&account)
			.and_then(|node| List::update_position_for(node, new_weight));
		if let Some((from, to)) = maybe_movement {
			Self::deposit_event(Event::<T>::Rebagged { who: account.clone(), from, to });
		};
		maybe_movement
	}

	/// Equivalent to `ListBags::get`, but public. Useful for tests in outside of this crate.
	#[cfg(feature = "std")]
	pub fn list_bags_get(weight: VoteWeight) -> Option<list::Bag<T>> {
		ListBags::get(weight)
	}
}

impl<T: Config> SortedListProvider<T::AccountId> for Pallet<T> {
	type Error = Error;

	fn iter() -> Box<dyn Iterator<Item = T::AccountId>> {
		Box::new(List::<T>::iter().map(|n| n.id().clone()))
	}

	fn count() -> u32 {
		ListNodes::<T>::count()
	}

	fn contains(id: &T::AccountId) -> bool {
		List::<T>::contains(id)
	}

	fn on_insert(id: T::AccountId, weight: VoteWeight) -> Result<(), Error> {
		List::<T>::insert(id, weight)
	}

	fn on_update(id: &T::AccountId, new_weight: VoteWeight) {
		Pallet::<T>::do_rebag(id, new_weight);
	}

	fn on_remove(id: &T::AccountId) {
		List::<T>::remove(id)
	}

	fn unsafe_regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		weight_of: Box<dyn Fn(&T::AccountId) -> VoteWeight>,
	) -> u32 {
		// NOTE: This call is unsafe for the same reason as SortedListProvider::unsafe_regenerate.
		// I.e. because it can lead to many storage accesses.
		// So it is ok to call it as caller must ensure the conditions.
		List::<T>::unsafe_regenerate(all, weight_of)
	}

	#[cfg(feature = "std")]
	fn sanity_check() -> Result<(), &'static str> {
		List::<T>::sanity_check()
	}

	#[cfg(not(feature = "std"))]
	fn sanity_check() -> Result<(), &'static str> {
		Ok(())
	}

	fn unsafe_clear() {
		// NOTE: This call is unsafe for the same reason as SortedListProvider::unsafe_clear.
		// I.e. because it can lead to many storage accesses.
		// So it is ok to call it as caller must ensure the conditions.
		List::<T>::unsafe_clear()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn weight_update_worst_case(who: &T::AccountId, is_increase: bool) -> VoteWeight {
		use frame_support::traits::Get as _;
		let thresholds = T::BagThresholds::get();
		let node = list::Node::<T>::get(who).unwrap();
		let current_bag_idx = thresholds
			.iter()
			.chain(sp_std::iter::once(&VoteWeight::MAX))
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
