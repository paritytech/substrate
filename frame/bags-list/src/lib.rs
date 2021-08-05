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

//! A semi-sorted list, where items hold an `AccountId` based on some `VoteWeight`. The `AccountId`
//! can be synonym to a `Voter` and `VoteWeight` signifies the chance of each voter being included
//! in the final [`VoteWeightProvider::iter`].
//!
//! It implements [`sp_election_provider_support::SortedListProvider`] to provide a semi-sorted list
//! of accounts to another pallet. It needs some other pallet to give it some information about the
//! weights of accounts via [`sp_election_provider_support::VoteWeightProvider`].
//!
//! This pallet is not configurable at genesis. Whoever uses it should call appropriate functions of
//! the `SortedListProvider` (i.e. `on_insert`) at their genesis.
//!
//! # ⚠️ WARNING ⚠️
//!
//! Do not insert an id that already exists in the list; doing so can result in catastrophic failure
//! of your blockchain, including entering into an infinite loop during block execution.
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
//! - items are kept in bags, which are delineated by their range of weight (See [`BagThresholds`]).
//! - for iteration, bags are chained together from highest to lowest and elements within the bag
//!   are iterated from head to tail.
//! - thus, items within a bag are iterated in order of insertion. Thus removing an item and
//!   re-inserting it will worsen its position in list iteration; this reduces incentives for some
//!   types of spam that involve consistently removing and inserting for better position. Further,
//!   ordering granularity is thus dictated by range between each bag threshold.
//! - if an items weight changes to a value no longer within the range of its current bag its
//!   position will need to be updated by an external actor with rebag or removal & insertion.
//
//! ### Further Plans
//!
//! *new terminology*: fully decouple this pallet from voting names, use account id instead of
//! voter and priority instead of weight.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_election_provider_support::{SortedListProvider, VoteWeight, VoteWeightProvider};
use frame_system::ensure_signed;
use sp_std::prelude::*;

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarks;
mod list;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

use list::List;

pub(crate) const LOG_TARGET: &'static str = "runtime::bags_list";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] ", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
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
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		// Something that provides the weights of voters.
		type VoteWeightProvider: VoteWeightProvider<Self::AccountId>;

		/// The list of thresholds separating the various voter bags.
		///
		/// Voters are separated into unsorted bags according to their vote weight. This specifies
		/// the thresholds separating the bags. A voter's bag is the largest bag for which the
		/// voter's weight is less than or equal to its upper threshold.
		///
		/// When voters are iterated, higher bags are iterated completely before lower bags. This
		/// means that iteration is _semi-sorted_: voters of higher weight tend to come before
		/// voters of lower weight, but peer voters within a particular bag are sorted in insertion
		/// order.
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
		/// The helpers in the `voter_bags::make_bags` module can simplify this calculation. To use
		/// them, the `make-bags` feature must be enabled.
		///
		/// # Examples
		///
		/// - If `BagThresholds::get().is_empty()`, then all voters are put into the same bag,
		///   and iteration is strictly in insertion order.
		/// - If `BagThresholds::get().len() == 64`, and the thresholds are determined
		///   according to the procedure given above, then the constant ratio is equal to 2.
		/// - If `BagThresholds::get().len() == 200`, and the thresholds are determined
		///   according to the procedure given above, then the constant ratio is approximately equal
		///   to 1.248.
		/// - If the threshold list begins `[1, 2, 3, ...]`, then a voter with weight 0 or 1 will
		///   fall into bag 0, a voter with weight 2 will fall into bag 1, etc.
		///
		/// # Migration
		///
		/// In the event that this list ever changes, a copy of the old bags list must be retained.
		/// With that `List::migrate` can be called, which will perform the appropriate
		/// migration.
		#[pallet::constant]
		type BagThresholds: Get<&'static [VoteWeight]>;
	}

	/// How many voters are registered.
	#[pallet::storage]
	pub(crate) type CounterForVoters<T> = StorageValue<_, u32, ValueQuery>;

	/// Voter nodes store links forward and back within their respective bags, the stash id, and
	/// whether the voter is a validator or nominator.
	///
	/// There is nothing in this map directly identifying to which bag a particular node belongs.
	/// However, the `Node` data structure has helpers which can provide that information.
	#[pallet::storage]
	pub(crate) type VoterNodes<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, list::Node<T>>;

	/// This storage item maps a bag (identified by its upper threshold) to the `Bag` struct, which
	/// mainly exists to store head and tail pointers to the appropriate nodes.
	#[pallet::storage]
	pub(crate) type VoterBags<T: Config> = StorageMap<_, Twox64Concat, VoteWeight, list::Bag<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	#[pallet::metadata(T::AccountId = "AccountId")]
	pub enum Event<T: Config> {
		/// Moved an account from one bag to another. \[who, from, to\].
		Rebagged(T::AccountId, VoteWeight, VoteWeight),
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Declare that some `reposition` account has, through rewards or penalties, sufficiently
		/// changed its weight that it should properly fall into a different bag than its current
		/// one.
		///
		/// Anyone can call this function about any target account.
		///
		/// Will never return an error; if `reposition` does not exist or doesn't need a rebag, then
		/// it is a noop and only fees are collected from `origin`.
		#[pallet::weight(T::WeightInfo::rebag())]
		pub fn rebag(origin: OriginFor<T>, reposition: T::AccountId) -> DispatchResult {
			ensure_signed(origin)?;
			let current_weight = T::VoteWeightProvider::vote_weight(&reposition);
			Pallet::<T>::do_rebag(&reposition, current_weight);
			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			// ensure they are strictly increasing, this also implies that duplicates are detected.
			assert!(
				T::BagThresholds::get().windows(2).all(|window| window[1] > window[0]),
				"Voter bag thresholds must strictly increase, and have no duplicates",
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
			Self::deposit_event(Event::<T>::Rebagged(account.clone(), from, to));
		};
		maybe_movement
	}
}

impl<T: Config> SortedListProvider<T::AccountId> for Pallet<T> {
	fn iter() -> Box<dyn Iterator<Item = T::AccountId>> {
		Box::new(List::<T>::iter().map(|n| n.id().clone()))
	}

	fn count() -> u32 {
		CounterForVoters::<T>::get()
	}

	fn contains(voter: &T::AccountId) -> bool {
		VoterNodes::<T>::contains_key(voter)
	}

	fn on_insert(voter: T::AccountId, weight: VoteWeight) {
		List::<T>::insert(voter, weight);
	}

	fn on_update(voter: &T::AccountId, new_weight: VoteWeight) {
		Pallet::<T>::do_rebag(voter, new_weight);
	}

	fn on_remove(voter: &T::AccountId) {
		List::<T>::remove(voter)
	}

	fn regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		weight_of: Box<dyn Fn(&T::AccountId) -> VoteWeight>,
	) -> u32 {
		List::<T>::regenerate(all, weight_of)
	}

	fn sanity_check() -> Result<(), &'static str> {
		List::<T>::sanity_check()
	}
}
