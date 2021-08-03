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

//! Implement a data structure for pallet-staking designed for the properties that:
//!
//! - It's efficient to insert or remove a voter
//! - It's efficient to iterate over the top* N voters by stake, where the precise ordering of
//!   voters doesn't particularly matter.

// use codec::{Decode, Encode};
use frame_election_provider_support::VoteWeight;
use frame_support::{
	pallet_prelude::*,
	traits::{Currency, CurrencyToVote, LockableCurrency},
};
use pallet_staking;

mod voter_list;
pub mod weights;

pub use weights::WeightInfo;

use pallet::*;

use pallet_staking::{AccountIdOf, BalanceOf, VotingDataOf};

pub(crate) const LOG_TARGET: &'static str = "runtime::voter_bags";

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

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_staking::Config {
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
		/// - If `VoterBagThresholds::get().is_empty()`, then all voters are put into the same bag,
		///   and iteration is strictly in insertion order.
		/// - If `VoterBagThresholds::get().len() == 64`, and the thresholds are determined
		///   according to the procedure given above, then the constant ratio is equal to 2.
		/// - If `VoterBagThresholds::get().len() == 200`, and the thresholds are determined
		///   according to the procedure given above, then the constant ratio is approximately equal
		///   to 1.248.
		/// - If the threshold list begins `[1, 2, 3, ...]`, then a voter with weight 0 or 1 will
		///   fall into bag 0, a voter with weight 2 will fall into bag 1, etc.
		///
		/// # Migration
		///
		/// In the event that this list ever changes, a copy of the old bags list must be retained.
		/// With that `VoterList::migrate` can be called, which will perform the appropriate
		/// migration.
		#[pallet::constant]
		type BVoterBagThresholds: Get<&'static [VoteWeight]>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
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
		StorageMap<_, Twox64Concat, AccountIdOf<T>, voter_list::Node<T>>;

	/// Which bag currently contains a particular voter.
	///
	/// This may not be the appropriate bag for the voter's weight if they have been rewarded or
	/// slashed.
	#[pallet::storage]
	pub(crate) type VoterBagFor<T: Config> =
		StorageMap<_, Twox64Concat, AccountIdOf<T>, VoteWeight>;

	/// This storage item maps a bag (identified by its upper threshold) to the `Bag` struct, which
	/// mainly exists to store head and tail pointers to the appropriate nodes.
	#[pallet::storage]
	pub(crate) type VoterBags<T: Config> =
		StorageMap<_, Twox64Concat, VoteWeight, voter_list::Bag<T>>;
}

/// Compute the existential weight for the specified configuration.
///
/// Note that this value depends on the current issuance, a quantity known to change over time.
/// This makes the project of computing a static value suitable for inclusion in a static,
/// generated file _excitingly unstable_.
#[cfg(any(feature = "std", feature = "make-bags"))]
pub fn existential_weight<T: Config>() -> VoteWeight {
	// use frame_support::traits::{Currency, CurrencyToVote};

	let existential_deposit = <T::Currency as Currency<T::AccountId>>::minimum_balance();
	let issuance = <T::Currency as Currency<T::AccountId>>::total_issuance();
	T::CurrencyToVote::to_vote(existential_deposit, issuance)
}
