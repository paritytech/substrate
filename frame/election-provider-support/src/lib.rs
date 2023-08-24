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

//! Primitive traits for providing election functionality.
//!
//! This crate provides two traits that could interact to enable extensible election functionality
//! within FRAME pallets.
//!
//! Something that will provide the functionality of election will implement
//! [`ElectionProvider`] and its parent-trait [`ElectionProviderBase`], whilst needing an
//! associated [`ElectionProviderBase::DataProvider`], which needs to be
//! fulfilled by an entity implementing [`ElectionDataProvider`]. Most often, *the data provider is*
//! the receiver of the election, resulting in a diagram as below:
//!
//! ```ignore
//!                                         ElectionDataProvider
//!                          <------------------------------------------+
//!                          |                                          |
//!                          v                                          |
//!                    +-----+----+                              +------+---+
//!                    |          |                              |          |
//! pallet-do-election |          |                              |          | pallet-needs-election
//!                    |          |                              |          |
//!                    |          |                              |          |
//!                    +-----+----+                              +------+---+
//!                          |                                          ^
//!                          |                                          |
//!                          +------------------------------------------+
//!                                         ElectionProvider
//! ```
//!
//! > It could also be possible that a third party pallet (C), provides the data of election to an
//! > election provider (B), which then passes the election result to another pallet (A).
//!
//! ## Election Types
//!
//! Typically, two types of elections exist:
//!
//! 1. **Stateless**: Election data is provided, and the election result is immediately ready.
//! 2. **Stateful**: Election data is is queried ahead of time, and the election result might be
//!    ready some number of blocks in the future.
//!
//! To accommodate both type of elections in one trait, the traits lean toward **stateful
//! election**, as it is more general than the stateless. This is why [`ElectionProvider::elect`]
//! has no parameters. All value and type parameter must be provided by the [`ElectionDataProvider`]
//! trait, even if the election happens immediately.
//!
//! ## Election Data
//!
//! The data associated with an election, essentially what the [`ElectionDataProvider`] must convey
//! is as follows:
//!
//! 1. A list of voters, with their stake.
//! 2. A list of targets (i.e. _candidates_).
//! 3. A number of desired targets to be elected (i.e. _winners_)
//!
//! In addition to that, the [`ElectionDataProvider`] must also hint [`ElectionProvider`] at when
//! the next election might happen ([`ElectionDataProvider::next_election_prediction`]). A stateless
//! election provider would probably ignore this. A stateful election provider can use this to
//! prepare the election result in advance.
//!
//! Nonetheless, an [`ElectionProvider`] shan't rely on this and should preferably provide some
//! means of fallback election as well, in case the `elect` was called immaturely early.
//!
//! ## Example
//!
//! ```rust
//! # use frame_election_provider_support::{*, data_provider};
//! # use sp_npos_elections::{Support, Assignment};
//! # use frame_support::traits::ConstU32;
//! # use sp_runtime::bounded_vec;
//!
//! type AccountId = u64;
//! type Balance = u64;
//! type BlockNumber = u32;
//!
//! mod data_provider_mod {
//!     use super::*;
//!
//!     pub trait Config: Sized {
//!         type ElectionProvider: ElectionProvider<
//!             AccountId = AccountId,
//!             BlockNumber = BlockNumber,
//!             DataProvider = Pallet<Self>,
//!         >;
//!     }
//!
//!     pub struct Pallet<T: Config>(std::marker::PhantomData<T>);
//!
//!     impl<T: Config> ElectionDataProvider for Pallet<T> {
//!         type AccountId = AccountId;
//!         type BlockNumber = BlockNumber;
//!         type MaxVotesPerVoter = ConstU32<1>;
//!
//!         fn desired_targets() -> data_provider::Result<u32> {
//!             Ok(1)
//!         }
//!         fn electing_voters(bounds: DataProviderBounds)
//!           -> data_provider::Result<Vec<VoterOf<Self>>>
//!         {
//!             Ok(Default::default())
//!         }
//!         fn electable_targets(bounds: DataProviderBounds) -> data_provider::Result<Vec<AccountId>> {
//!             Ok(vec![10, 20, 30])
//!         }
//!         fn next_election_prediction(now: BlockNumber) -> BlockNumber {
//!             0
//!         }
//!     }
//! }
//!
//!
//! mod generic_election_provider {
//!     use super::*;
//!
//!     pub struct GenericElectionProvider<T: Config>(std::marker::PhantomData<T>);
//!
//!     pub trait Config {
//!         type DataProvider: ElectionDataProvider<AccountId=AccountId, BlockNumber = BlockNumber>;
//!     }
//!
//!     impl<T: Config> ElectionProviderBase for GenericElectionProvider<T> {
//!         type AccountId = AccountId;
//!         type BlockNumber = BlockNumber;
//!         type Error = &'static str;
//!         type DataProvider = T::DataProvider;
//!         type MaxWinners = ConstU32<{ u32::MAX }>;
//!
//!     }
//!
//!     impl<T: Config> ElectionProvider for GenericElectionProvider<T> {
//!         fn ongoing() -> bool { false }
//!         fn elect() -> Result<BoundedSupportsOf<Self>, Self::Error> {
//!             Self::DataProvider::electable_targets(DataProviderBounds::default())
//!                 .map_err(|_| "failed to elect")
//!                 .map(|t| bounded_vec![(t[0], Support::default())])
//!         }
//!     }
//! }
//!
//! mod runtime {
//!     use super::generic_election_provider;
//!     use super::data_provider_mod;
//!     use super::AccountId;
//!
//!     struct Runtime;
//!     impl generic_election_provider::Config for Runtime {
//!         type DataProvider = data_provider_mod::Pallet<Runtime>;
//!     }
//!
//!     impl data_provider_mod::Config for Runtime {
//!         type ElectionProvider = generic_election_provider::GenericElectionProvider<Runtime>;
//!     }
//!
//! }
//!
//! # fn main() {}
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

pub mod bounds;
pub mod onchain;
pub mod traits;

use sp_runtime::{
	traits::{Bounded, Saturating, Zero},
	RuntimeDebug,
};
use sp_std::{fmt::Debug, prelude::*};

pub use bounds::DataProviderBounds;
pub use codec::{Decode, Encode};
/// Re-export the solution generation macro.
pub use frame_election_provider_solution_type::generate_solution_type;
pub use frame_support::{traits::Get, weights::Weight, BoundedVec};
/// Re-export some type as they are used in the interface.
pub use sp_arithmetic::PerThing;
pub use sp_npos_elections::{
	Assignment, BalancingConfig, BoundedSupports, ElectionResult, Error, ExtendedBalance,
	IdentifierT, PerThing128, Support, Supports, VoteWeight,
};
pub use traits::NposSolution;

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

// re-export for the solution macro, with the dependencies of the macro.
#[doc(hidden)]
pub mod private {
	pub use codec;
	pub use scale_info;
	pub use sp_arithmetic;
	pub use sp_std;

	// Simple Extension trait to easily convert `None` from index closures to `Err`.
	//
	// This is only generated and re-exported for the solution code to use.
	pub trait __OrInvalidIndex<T> {
		fn or_invalid_index(self) -> Result<T, crate::Error>;
	}

	impl<T> __OrInvalidIndex<T> for Option<T> {
		fn or_invalid_index(self) -> Result<T, crate::Error> {
			self.ok_or(crate::Error::SolutionInvalidIndex)
		}
	}
}

use private::__OrInvalidIndex;

pub mod weights;
pub use weights::WeightInfo;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

/// The [`IndexAssignment`] type is an intermediate between the assignments list
/// ([`&[Assignment<T>]`][Assignment]) and `SolutionOf<T>`.
///
/// The voter and target identifiers have already been replaced with appropriate indices,
/// making it fast to repeatedly encode into a `SolutionOf<T>`. This property turns out
/// to be important when trimming for solution length.
#[derive(RuntimeDebug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct IndexAssignment<VoterIndex, TargetIndex, P: PerThing> {
	/// Index of the voter among the voters list.
	pub who: VoterIndex,
	/// The distribution of the voter's stake among winning targets.
	///
	/// Targets are identified by their index in the canonical list.
	pub distribution: Vec<(TargetIndex, P)>,
}

impl<VoterIndex, TargetIndex, P: PerThing> IndexAssignment<VoterIndex, TargetIndex, P> {
	pub fn new<AccountId: IdentifierT>(
		assignment: &Assignment<AccountId, P>,
		voter_index: impl Fn(&AccountId) -> Option<VoterIndex>,
		target_index: impl Fn(&AccountId) -> Option<TargetIndex>,
	) -> Result<Self, Error> {
		Ok(Self {
			who: voter_index(&assignment.who).or_invalid_index()?,
			distribution: assignment
				.distribution
				.iter()
				.map(|(target, proportion)| Some((target_index(target)?, *proportion)))
				.collect::<Option<Vec<_>>>()
				.or_invalid_index()?,
		})
	}
}

/// A type alias for [`IndexAssignment`] made from [`NposSolution`].
pub type IndexAssignmentOf<C> = IndexAssignment<
	<C as NposSolution>::VoterIndex,
	<C as NposSolution>::TargetIndex,
	<C as NposSolution>::Accuracy,
>;

/// Types that are used by the data provider trait.
pub mod data_provider {
	/// Alias for the result type of the election data provider.
	pub type Result<T> = sp_std::result::Result<T, &'static str>;
}

/// Something that can provide the data to an [`ElectionProvider`].
pub trait ElectionDataProvider {
	/// The account identifier type.
	type AccountId: Encode;

	/// The block number type.
	type BlockNumber;

	/// Maximum number of votes per voter that this data provider is providing.
	type MaxVotesPerVoter: Get<u32>;

	/// All possible targets for the election, i.e. the targets that could become elected, thus
	/// "electable".
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	fn electable_targets(bounds: DataProviderBounds)
		-> data_provider::Result<Vec<Self::AccountId>>;

	/// All the voters that participate in the election, thus "electing".
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	fn electing_voters(bounds: DataProviderBounds) -> data_provider::Result<Vec<VoterOf<Self>>>;

	/// The number of targets to elect.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	///
	/// A sensible implementation should use the minimum between this value and
	/// [`Self::targets().len()`], since desiring a winner set larger than candidates is not
	/// feasible.
	///
	/// This is documented further in issue: <https://github.com/paritytech/substrate/issues/9478>
	fn desired_targets() -> data_provider::Result<u32>;

	/// Provide a best effort prediction about when the next election is about to happen.
	///
	/// In essence, the implementor should predict with this function when it will trigger the
	/// [`ElectionProvider::elect`].
	///
	/// This is only useful for stateful election providers.
	fn next_election_prediction(now: Self::BlockNumber) -> Self::BlockNumber;

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn put_snapshot(
		_voters: Vec<VoterOf<Self>>,
		_targets: Vec<Self::AccountId>,
		_target_stake: Option<VoteWeight>,
	) {
	}

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	///
	/// Same as `put_snapshot`, but can add a single voter one by one.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_voter(
		_voter: Self::AccountId,
		_weight: VoteWeight,
		_targets: BoundedVec<Self::AccountId, Self::MaxVotesPerVoter>,
	) {
	}

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	///
	/// Same as `put_snapshot`, but can add a single voter one by one.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_target(_target: Self::AccountId) {}

	/// Clear all voters and targets.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn clear() {}
}

/// Base trait for types that can provide election
pub trait ElectionProviderBase {
	/// The account identifier type.
	type AccountId;

	/// The block number type.
	type BlockNumber;

	/// The error type that is returned by the provider.
	type Error: Debug;

	/// The upper bound on election winners that can be returned.
	///
	/// # WARNING
	///
	/// when communicating with the data provider, one must ensure that
	/// `DataProvider::desired_targets` returns a value less than this bound. An
	/// implementation can chose to either return an error and/or sort and
	/// truncate the output to meet this bound.
	type MaxWinners: Get<u32>;

	/// The data provider of the election.
	type DataProvider: ElectionDataProvider<
		AccountId = Self::AccountId,
		BlockNumber = Self::BlockNumber,
	>;

	/// checked call to `Self::DataProvider::desired_targets()` ensuring the value never exceeds
	/// [`Self::MaxWinners`].
	fn desired_targets_checked() -> data_provider::Result<u32> {
		Self::DataProvider::desired_targets().and_then(|desired_targets| {
			if desired_targets <= Self::MaxWinners::get() {
				Ok(desired_targets)
			} else {
				Err("desired_targets must not be greater than MaxWinners.")
			}
		})
	}
}

/// Elect a new set of winners, bounded by `MaxWinners`.
///
/// It must always use [`ElectionProviderBase::DataProvider`] to fetch the data it needs.
///
/// This election provider that could function asynchronously. This implies that this election might
/// needs data ahead of time (ergo, receives no arguments to `elect`), and might be `ongoing` at
/// times.
pub trait ElectionProvider: ElectionProviderBase {
	/// Indicate if this election provider is currently ongoing an asynchronous election or not.
	fn ongoing() -> bool;

	/// Performs the election. This should be implemented as a self-weighing function. The
	/// implementor should register its appropriate weight at the end of execution with the
	/// system pallet directly.
	fn elect() -> Result<BoundedSupportsOf<Self>, Self::Error>;
}

/// A (almost) marker trait that signifies an election provider as working synchronously. i.e. being
/// *instant*.
///
/// This must still use the same data provider as with [`ElectionProviderBase::DataProvider`].
/// However, it can optionally overwrite the amount of voters and targets that are fetched from the
/// data provider at runtime via `forced_input_voters_bound` and `forced_input_target_bound`.
pub trait InstantElectionProvider: ElectionProviderBase {
	fn instant_elect(
		forced_input_voters_bound: DataProviderBounds,
		forced_input_target_bound: DataProviderBounds,
	) -> Result<BoundedSupportsOf<Self>, Self::Error>;
}

/// An election provider that does nothing whatsoever.
pub struct NoElection<X>(sp_std::marker::PhantomData<X>);

impl<AccountId, BlockNumber, DataProvider, MaxWinners> ElectionProviderBase
	for NoElection<(AccountId, BlockNumber, DataProvider, MaxWinners)>
where
	DataProvider: ElectionDataProvider<AccountId = AccountId, BlockNumber = BlockNumber>,
	MaxWinners: Get<u32>,
{
	type AccountId = AccountId;
	type BlockNumber = BlockNumber;
	type Error = &'static str;
	type MaxWinners = MaxWinners;
	type DataProvider = DataProvider;
}

impl<AccountId, BlockNumber, DataProvider, MaxWinners> ElectionProvider
	for NoElection<(AccountId, BlockNumber, DataProvider, MaxWinners)>
where
	DataProvider: ElectionDataProvider<AccountId = AccountId, BlockNumber = BlockNumber>,
	MaxWinners: Get<u32>,
{
	fn ongoing() -> bool {
		false
	}

	fn elect() -> Result<BoundedSupportsOf<Self>, Self::Error> {
		Err("`NoElection` cannot do anything.")
	}
}

impl<AccountId, BlockNumber, DataProvider, MaxWinners> InstantElectionProvider
	for NoElection<(AccountId, BlockNumber, DataProvider, MaxWinners)>
where
	DataProvider: ElectionDataProvider<AccountId = AccountId, BlockNumber = BlockNumber>,
	MaxWinners: Get<u32>,
{
	fn instant_elect(
		_: DataProviderBounds,
		_: DataProviderBounds,
	) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		Err("`NoElection` cannot do anything.")
	}
}

/// A utility trait for something to implement `ElectionDataProvider` in a sensible way.
///
/// This is generic over `AccountId` and it can represent a validator, a nominator, or any other
/// entity.
///
/// The scores (see [`Self::Score`]) are ascending, the higher, the better.
///
/// Something that implements this trait will do a best-effort sort over ids, and thus can be
/// used on the implementing side of [`ElectionDataProvider`].
pub trait SortedListProvider<AccountId> {
	/// The list's error type.
	type Error: sp_std::fmt::Debug;

	/// The type used by the list to compare nodes for ordering.
	type Score: Bounded + Saturating + Zero;

	/// An iterator over the list, which can have `take` called on it.
	fn iter() -> Box<dyn Iterator<Item = AccountId>>;

	/// Returns an iterator over the list, starting right after from the given voter.
	///
	/// May return an error if `start` is invalid.
	fn iter_from(start: &AccountId) -> Result<Box<dyn Iterator<Item = AccountId>>, Self::Error>;

	/// The current count of ids in the list.
	fn count() -> u32;

	/// Return true if the list already contains `id`.
	fn contains(id: &AccountId) -> bool;

	/// Hook for inserting a new id.
	///
	/// Implementation should return an error if duplicate item is being inserted.
	fn on_insert(id: AccountId, score: Self::Score) -> Result<(), Self::Error>;

	/// Hook for updating a single id.
	///
	/// The `new` score is given.
	///
	/// Returns `Ok(())` iff it successfully updates an item, an `Err(_)` otherwise.
	fn on_update(id: &AccountId, score: Self::Score) -> Result<(), Self::Error>;

	/// Get the score of `id`.
	fn get_score(id: &AccountId) -> Result<Self::Score, Self::Error>;

	/// Same as `on_update`, but incorporate some increased score.
	fn on_increase(id: &AccountId, additional: Self::Score) -> Result<(), Self::Error> {
		let old_score = Self::get_score(id)?;
		let new_score = old_score.saturating_add(additional);
		Self::on_update(id, new_score)
	}

	/// Same as `on_update`, but incorporate some decreased score.
	///
	/// If the new score of the item is `Zero`, it is removed.
	fn on_decrease(id: &AccountId, decreased: Self::Score) -> Result<(), Self::Error> {
		let old_score = Self::get_score(id)?;
		let new_score = old_score.saturating_sub(decreased);
		if new_score.is_zero() {
			Self::on_remove(id)
		} else {
			Self::on_update(id, new_score)
		}
	}

	/// Hook for removing am id from the list.
	///
	/// Returns `Ok(())` iff it successfully removes an item, an `Err(_)` otherwise.
	fn on_remove(id: &AccountId) -> Result<(), Self::Error>;

	/// Regenerate this list from scratch. Returns the count of items inserted.
	///
	/// This should typically only be used at a runtime upgrade.
	///
	/// ## WARNING
	///
	/// This function should be called with care, regenerate will remove the current list write the
	/// new list, which can lead to too many storage accesses, exhausting the block weight.
	fn unsafe_regenerate(
		all: impl IntoIterator<Item = AccountId>,
		score_of: Box<dyn Fn(&AccountId) -> Self::Score>,
	) -> u32;

	/// Remove all items from the list.
	///
	/// ## WARNING
	///
	/// This function should never be called in production settings because it can lead to an
	/// unbounded amount of storage accesses.
	fn unsafe_clear();

	/// Check internal state of the list. Only meant for debugging.
	#[cfg(feature = "try-runtime")]
	fn try_state() -> Result<(), TryRuntimeError>;

	/// If `who` changes by the returned amount they are guaranteed to have a worst case change
	/// in their list position.
	#[cfg(feature = "runtime-benchmarks")]
	fn score_update_worst_case(_who: &AccountId, _is_increase: bool) -> Self::Score;
}

/// Something that can provide the `Score` of an account. Similar to [`ElectionProvider`] and
/// [`ElectionDataProvider`], this should typically be implementing by whoever is supposed to *use*
/// `SortedListProvider`.
pub trait ScoreProvider<AccountId> {
	type Score;

	/// Get the current `Score` of `who`.
	fn score(who: &AccountId) -> Self::Score;

	/// For tests, benchmarks and fuzzing, set the `score`.
	#[cfg(any(feature = "runtime-benchmarks", feature = "fuzz", feature = "std"))]
	fn set_score_of(_: &AccountId, _: Self::Score) {}
}

/// Something that can compute the result to an NPoS solution.
pub trait NposSolver {
	/// The account identifier type of this solver.
	type AccountId: sp_npos_elections::IdentifierT;
	/// The accuracy of this solver. This will affect the accuracy of the output.
	type Accuracy: PerThing128;
	/// The error type of this implementation.
	type Error: sp_std::fmt::Debug + sp_std::cmp::PartialEq;

	/// Solve an NPoS solution with the given `voters`, `targets`, and select `to_elect` count
	/// of `targets`.
	fn solve(
		to_elect: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, impl IntoIterator<Item = Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error>;

	/// Measure the weight used in the calculation of the solver.
	/// - `voters` is the number of voters.
	/// - `targets` is the number of targets.
	/// - `vote_degree` is the degree ie the maximum numbers of votes per voter.
	fn weight<T: WeightInfo>(voters: u32, targets: u32, vote_degree: u32) -> Weight;
}

/// A wrapper for [`sp_npos_elections::seq_phragmen`] that implements [`NposSolver`]. See the
/// documentation of [`sp_npos_elections::seq_phragmen`] for more info.
pub struct SequentialPhragmen<AccountId, Accuracy, Balancing = ()>(
	sp_std::marker::PhantomData<(AccountId, Accuracy, Balancing)>,
);

impl<AccountId: IdentifierT, Accuracy: PerThing128, Balancing: Get<Option<BalancingConfig>>>
	NposSolver for SequentialPhragmen<AccountId, Accuracy, Balancing>
{
	type AccountId = AccountId;
	type Accuracy = Accuracy;
	type Error = sp_npos_elections::Error;
	fn solve(
		winners: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, impl IntoIterator<Item = Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error> {
		sp_npos_elections::seq_phragmen(winners, targets, voters, Balancing::get())
	}

	fn weight<T: WeightInfo>(voters: u32, targets: u32, vote_degree: u32) -> Weight {
		T::phragmen(voters, targets, vote_degree)
	}
}

/// A wrapper for [`sp_npos_elections::phragmms()`] that implements [`NposSolver`]. See the
/// documentation of [`sp_npos_elections::phragmms()`] for more info.
pub struct PhragMMS<AccountId, Accuracy, Balancing = ()>(
	sp_std::marker::PhantomData<(AccountId, Accuracy, Balancing)>,
);

impl<AccountId: IdentifierT, Accuracy: PerThing128, Balancing: Get<Option<BalancingConfig>>>
	NposSolver for PhragMMS<AccountId, Accuracy, Balancing>
{
	type AccountId = AccountId;
	type Accuracy = Accuracy;
	type Error = sp_npos_elections::Error;
	fn solve(
		winners: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, impl IntoIterator<Item = Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error> {
		sp_npos_elections::phragmms(winners, targets, voters, Balancing::get())
	}

	fn weight<T: WeightInfo>(voters: u32, targets: u32, vote_degree: u32) -> Weight {
		T::phragmms(voters, targets, vote_degree)
	}
}

/// A voter, at the level of abstraction of this crate.
pub type Voter<AccountId, Bound> = (AccountId, VoteWeight, BoundedVec<AccountId, Bound>);

/// Same as [`Voter`], but parameterized by an [`ElectionDataProvider`].
pub type VoterOf<D> =
	Voter<<D as ElectionDataProvider>::AccountId, <D as ElectionDataProvider>::MaxVotesPerVoter>;

/// Same as `BoundedSupports` but parameterized by a `ElectionProviderBase`.
pub type BoundedSupportsOf<E> = BoundedSupports<
	<E as ElectionProviderBase>::AccountId,
	<E as ElectionProviderBase>::MaxWinners,
>;

sp_core::generate_feature_enabled_macro!(
	runtime_benchmarks_enabled,
	feature = "runtime-benchmarks",
	$
);

sp_core::generate_feature_enabled_macro!(
	runtime_benchmarks_fuzz_or_std_enabled,
	any(feature = "runtime-benchmarks", feature = "fuzzing", feature = "std"),
	$
);
