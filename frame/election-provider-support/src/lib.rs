// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
//! Something that will provide the functionality of election will implement [`ElectionProvider`],
//! whilst needing an associated [`ElectionProvider::DataProvider`], which needs to be fulfilled by
//! an entity implementing [`ElectionDataProvider`]. Most often, *the data provider is* the receiver
//! of the election, resulting in a diagram as below:
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
//! # use frame_election_provider_support::{*, data_provider, PageIndex};
//! # use sp_npos_elections::{Support, Assignment};
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
//!         const MAXIMUM_VOTES_PER_VOTER: u32 = 1;
//!
//!         fn desired_targets() -> data_provider::Result<u32> {
//!             Ok(1)
//!         }
//!         fn voters(maybe_max_len: Option<usize>, _page: PageIndex)
//!           -> data_provider::Result<Vec<(AccountId, VoteWeight, Vec<AccountId>)>>
//!         {
//!             Ok(Default::default())
//!         }
//!         fn targets(maybe_max_len: Option<usize>, _page: PageIndex) -> data_provider::Result<Vec<AccountId>> {
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
//!     impl<T: Config> ElectionProvider for GenericElectionProvider<T> {
//!         type AccountId = AccountId;
//!         type BlockNumber = BlockNumber;
//!         type Error = &'static str;
//!         type DataProvider = T::DataProvider;
//!         type Pages = ();
//!
//!         fn elect(_page: PageIndex) -> Result<Supports<AccountId>, Self::Error> {
//!             Self::DataProvider::targets(None, 0)
//!                 .map_err(|_| "failed to elect")
//!                 .map(|t| vec![(t[0], Support::default())])
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

pub mod onchain;

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{traits::Get, BoundedVec, DefaultNoBound, RuntimeDebug};
use scale_info::TypeInfo;
use sp_npos_elections::EvaluateSupport;
use sp_std::{fmt::Debug, prelude::*};

/// Re-export some type as they are used in the interface.
pub use sp_arithmetic::PerThing;
pub use sp_npos_elections::{
	Assignment, ElectionResult, ExtendedBalance, IdentifierT, NposSolution, PerThing128, Support,
	VoteWeight,
};

/// Types that are used by the data provider trait.
pub mod data_provider {
	/// Alias for the result type of the election data provider.
	pub type Result<T> = sp_std::result::Result<T, &'static str>;
}

/// The index used to indicate the page number.
///
/// A u8 would have probably been enough until the end of universe, but since we use this as the
/// bound of `BoundedVec` and similar, using `u32` will save us some hassle.
pub type PageIndex = u32;

/// Something that can provide the data to an [`ElectionProvider`].
pub trait ElectionDataProvider {
	/// The account identifier type.
	type AccountId;

	/// The block number type.
	type BlockNumber;

	/// Maximum number of votes per voter that this data provider is providing.
	type MaxVotesPerVoter: Get<u32>;

	/// All possible targets for the election, i.e. the candidates.
	///
	/// If `maybe_page_size` is `Some(v)` then the resulting vector MUST NOT be longer than `v`
	/// items long.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	fn targets(
		maybe_max_len: Option<usize>,
		remaining_pages: PageIndex,
	) -> data_provider::Result<Vec<Self::AccountId>>;

	/// All possible voters for the election.
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	///
	/// If `maybe_page_size` is `Some(v)` then the resulting vector MUST NOT be longer than `v`
	/// items long.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	fn voters(
		maybe_max_len: Option<usize>,
		remaining_pages: PageIndex,
	) -> data_provider::Result<Vec<Voter<Self::AccountId, Self::MaxVotesPerVoter>>>;

	/// The number of targets to elect.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
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
		_voters: Vec<(
			Self::AccountId,
			VoteWeight,
			BoundedVec<Self::AccountId, Self::MaxVotesPerVoter>,
		)>,
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

/// An election data provider that should only be used for testing.
#[cfg(feature = "std")]
pub struct TestDataProvider<X>(sp_std::marker::PhantomData<X>);

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionDataProvider for TestDataProvider<(AccountId, BlockNumber)> {
	type AccountId = AccountId;
	type BlockNumber = BlockNumber;
	type MaxVotesPerVoter = ();

	fn targets(
		_maybe_max_len: Option<usize>,
		_: PageIndex,
	) -> data_provider::Result<Vec<AccountId>> {
		Ok(Default::default())
	}
	fn voters(
		_maybe_max_len: Option<usize>,
		_: PageIndex,
	) -> data_provider::Result<Vec<Voter<Self::AccountId, Self::MaxVotesPerVoter>>> {
		Ok(Default::default())
	}
	fn desired_targets() -> data_provider::Result<u32> {
		Ok(Default::default())
	}
	fn next_election_prediction(now: BlockNumber) -> BlockNumber {
		now
	}
}

/// Something that can compute the result of an election and pass it back to the caller.
///
/// This trait only provides an interface to _request_ an election, i.e.
/// [`ElectionProvider::elect`]. That data required for the election need to be passed to the
/// implemented of this trait through [`ElectionProvider::DataProvider`].
pub trait ElectionProvider {
	/// The account identifier type.
	type AccountId;

	/// The block number type.
	type BlockNumber;

	/// The error type that is returned by the provider.
	type Error: Debug;

	/// The data provider of the election.
	type DataProvider: ElectionDataProvider<
		AccountId = Self::AccountId,
		BlockNumber = Self::BlockNumber,
	>;

	/// Maximum number of backers that a single support may have, in the results returned from this
	/// election provider.
	type MaxBackersPerSupport: Get<u32>;

	/// Maximum number of supports that can be returned, per page (i.e. per call to `elect`).
	type MaxSupportsPerPage: Get<u32>;

	/// The number of pages of support that this election provider can return.
	///
	/// All calls to `elect` must therefore be in the range of `PAGES-1 .. 0`.
	type Pages: frame_support::traits::Get<PageIndex>;

	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as vector of supports.
	///
	/// This should be implemented as a self-weighing function. The implementor should register its
	/// appropriate weight at the end of execution with the system pallet directly.
	fn elect(remaining: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error>;

	/// The index of the most significant page of the election result that is to be returned. This
	/// is typically [`Pages`] minus one, but is left open.
	fn msp() -> PageIndex {
		Self::Pages::get().saturating_sub(1)
	}

	/// The index of the least significant page of the election result that is to be returned. This
	/// is typically 0, but is left open.
	fn lsp() -> PageIndex {
		0
	}
}

/// An election provider to be used only for testing.
#[cfg(feature = "std")]
pub struct NoElection<X>(sp_std::marker::PhantomData<X>);

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionProvider for NoElection<(AccountId, BlockNumber)> {
	type Error = &'static str;

	type AccountId = AccountId;
	type BlockNumber = BlockNumber;

	type DataProvider = TestDataProvider<(Self::AccountId, Self::BlockNumber)>;
	type Pages = frame_support::traits::ConstU32<1>;

	type MaxBackersPerSupport = ();
	type MaxSupportsPerPage = ();

	fn elect(_: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		Err("<() as ElectionProvider> cannot do anything.")
	}
}

/// A utility trait for something to implement `ElectionDataProvider` in a sensible way.
///
/// This is generic over `AccountId` and it can represent a validator, a nominator, or any other
/// entity.
///
/// To simplify the trait, the `VoteWeight` is hardcoded as the weight of each entity. The weights
/// are ascending, the higher, the better. In the long term, if this trait ends up having use cases
/// outside of the election context, it is easy enough to make it generic over the `VoteWeight`.
///
/// Something that implements this trait will do a best-effort sort over ids, and thus can be
/// used on the implementing side of [`ElectionDataProvider`].
pub trait SortedListProvider<AccountId> {
	/// The list's error type.
	type Error: sp_std::fmt::Debug;

	/// An iterator over the list, which can have `take` called on it.
	fn iter() -> Box<dyn Iterator<Item = AccountId>>;

	/// Returns an iterator over the list, starting from the given voter.
	///
	/// May return an error if `start` is invalid.
	fn iter_from(start: &AccountId) -> Result<Box<dyn Iterator<Item = AccountId>>, Self::Error>;

	/// The current count of ids in the list.
	fn count() -> u32;

	/// Return true if the list already contains `id`.
	fn contains(id: &AccountId) -> bool;

	/// Hook for inserting a new id.
	fn on_insert(id: AccountId, weight: VoteWeight) -> Result<(), Self::Error>;

	/// Hook for updating a single id.
	fn on_update(id: &AccountId, weight: VoteWeight);

	/// Hook for removing am id from the list.
	fn on_remove(id: &AccountId);

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
		weight_of: Box<dyn Fn(&AccountId) -> VoteWeight>,
	) -> u32;

	/// Remove all items from the list.
	///
	/// ## WARNING
	///
	/// This function should never be called in production settings because it can lead to an
	/// unbounded amount of storage accesses.
	fn unsafe_clear();

	/// Sanity check internal state of list. Only meant for debug compilation.
	fn sanity_check() -> Result<(), &'static str>;

	/// If `who` changes by the returned amount they are guaranteed to have a worst case change
	/// in their list position.
	#[cfg(feature = "runtime-benchmarks")]
	fn weight_update_worst_case(_who: &AccountId, _is_increase: bool) -> VoteWeight {
		VoteWeight::MAX
	}
}

/// Something that can provide the `VoteWeight` of an account. Similar to [`ElectionProvider`] and
/// [`ElectionDataProvider`], this should typically be implementing by whoever is supposed to *use*
/// `SortedListProvider`.
pub trait VoteWeightProvider<AccountId> {
	/// Get the current `VoteWeight` of `who`.
	fn vote_weight(who: &AccountId) -> VoteWeight;

	/// For tests and benchmarks, set the `VoteWeight`.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn set_vote_weight_of(_: &AccountId, _: VoteWeight) {}
}

/// Something that can compute the result to an NPoS solution.
pub trait NposSolver {
	/// The account identifier type of this solver.
	type AccountId: sp_npos_elections::IdentifierT;
	/// The accuracy of this solver. This will affect the accuracy of the output.
	type Accuracy: PerThing128;
	/// The error type of this implementation.
	type Error: sp_std::fmt::Debug + sp_std::cmp::PartialEq + Clone;

	/// Solve an NPoS solution with the given `voters`, `targets`, and select `to_elect` count
	/// of `targets`.
	fn solve(
		to_elect: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, Vec<Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error>;
}

/// A wrapper for [`sp_npos_elections::seq_phragmen`] that implements [`NposSolver`]. See the
/// documentation of [`sp_npos_elections::seq_phragmen`] for more info.
pub struct SequentialPhragmen<AccountId, Accuracy, Balancing = ()>(
	sp_std::marker::PhantomData<(AccountId, Accuracy, Balancing)>,
);

impl<
		AccountId: IdentifierT,
		Accuracy: PerThing128,
		Balancing: Get<Option<(usize, ExtendedBalance)>>,
	> NposSolver for SequentialPhragmen<AccountId, Accuracy, Balancing>
{
	type AccountId = AccountId;
	type Accuracy = Accuracy;
	type Error = sp_npos_elections::Error;
	fn solve(
		winners: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, Vec<Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error> {
		sp_npos_elections::seq_phragmen(winners, targets, voters, Balancing::get())
	}
}

/// A wrapper for [`sp_npos_elections::phragmms()`] that implements [`NposSolver`]. See the
/// documentation of [`sp_npos_elections::phragmms()`] for more info.
pub struct PhragMMS<AccountId, Accuracy, Balancing = ()>(
	sp_std::marker::PhantomData<(AccountId, Accuracy, Balancing)>,
);

impl<
		AccountId: IdentifierT,
		Accuracy: PerThing128,
		Balancing: Get<Option<(usize, ExtendedBalance)>>,
	> NposSolver for PhragMMS<AccountId, Accuracy, Balancing>
{
	type AccountId = AccountId;
	type Accuracy = Accuracy;
	type Error = sp_npos_elections::Error;
	fn solve(
		winners: usize,
		targets: Vec<Self::AccountId>,
		voters: Vec<(Self::AccountId, VoteWeight, Vec<Self::AccountId>)>,
	) -> Result<ElectionResult<Self::AccountId, Self::Accuracy>, Self::Error> {
		sp_npos_elections::phragmms(winners, targets, voters, Balancing::get())
	}
}

/// A voter, at the level of abstraction of this crate.
pub type Voter<AccountId, Bound> = (AccountId, VoteWeight, BoundedVec<AccountId, Bound>);

/// A bounded equivalent to [`sp_npos_elections::Support`].
#[derive(Default, RuntimeDebug, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
pub struct BoundedSupport<AccountId, Bound: Get<u32>> {
	/// Total support.
	pub total: ExtendedBalance,
	/// Support from voters.
	pub voters: BoundedVec<(AccountId, ExtendedBalance), Bound>,
}

impl<AccountId, Bound: Get<u32>> sp_npos_elections::Backings for &BoundedSupport<AccountId, Bound> {
	fn total(&self) -> ExtendedBalance {
		self.total
	}
}

impl<AccountId: PartialEq, Bound: Get<u32>> PartialEq for BoundedSupport<AccountId, Bound> {
	fn eq(&self, other: &Self) -> bool {
		self.total == other.total && self.voters == other.voters
	}
}
impl<AccountId: PartialEq, Bound: Get<u32>> Eq for BoundedSupport<AccountId, Bound> {}

impl<AccountId: Clone, Bound: Get<u32>> Clone for BoundedSupport<AccountId, Bound> {
	fn clone(&self) -> Self {
		Self { voters: self.voters.clone(), total: self.total }
	}
}

impl<AccountId, Bound: Get<u32>> Into<sp_npos_elections::Support<AccountId>>
	for BoundedSupport<AccountId, Bound>
{
	fn into(self) -> sp_npos_elections::Support<AccountId> {
		sp_npos_elections::Support { voters: self.voters.into_inner(), total: self.total }
	}
}

impl<AccountId, Bound: Get<u32>> TryFrom<sp_npos_elections::Support<AccountId>>
	for BoundedSupport<AccountId, Bound>
{
	type Error = &'static str;
	fn try_from(s: sp_npos_elections::Support<AccountId>) -> Result<Self, Self::Error> {
		let voters = s.voters.try_into().map_err(|_| "voters bound not respected")?;
		Ok(Self { voters, total: s.total })
	}
}

/// A vector of [`BoundedSupport`].
///
/// This is a newtype rather than an alias so that we can implement certain foreign traits for it.
///
/// Note the order of generic bounds, first comes the outer bound and then the inner. When possible,
/// use [`BoundedSupportsOf`] to avoid mistakes.
#[derive(Debug, Clone, Encode, Decode, TypeInfo, MaxEncodedLen, DefaultNoBound)]
pub struct BoundedSupports<AccountId, BOuter: Get<u32>, BInner: Get<u32>>(
	pub BoundedVec<(AccountId, BoundedSupport<AccountId, BInner>), BOuter>,
);

impl<AccountId: PartialEq, BOuter: Get<u32>, BInner: Get<u32>> PartialEq
	for BoundedSupports<AccountId, BOuter, BInner>
{
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}
impl<AccountId: PartialEq, BOuter: Get<u32>, BInner: Get<u32>> Eq
	for BoundedSupports<AccountId, BOuter, BInner>
{
}

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>> sp_std::ops::Deref
	for BoundedSupports<AccountId, BOuter, BInner>
{
	type Target = BoundedVec<(AccountId, BoundedSupport<AccountId, BInner>), BOuter>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>>
	From<BoundedVec<(AccountId, BoundedSupport<AccountId, BInner>), BOuter>>
	for BoundedSupports<AccountId, BOuter, BInner>
{
	fn from(t: BoundedVec<(AccountId, BoundedSupport<AccountId, BInner>), BOuter>) -> Self {
		Self(t)
	}
}

/// A [`BoundedSupports`] parameterized by something that implements [`ElectionProvider`].
pub type BoundedSupportsOf<E> = BoundedSupports<
	<E as ElectionProvider>::AccountId,
	<E as ElectionProvider>::MaxSupportsPerPage,
	<E as ElectionProvider>::MaxBackersPerSupport,
>;

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>> EvaluateSupport
	for BoundedSupports<AccountId, BOuter, BInner>
{
	fn evaluate(&self) -> sp_npos_elections::ElectionScore {
		sp_npos_elections::evaluate_support_core(self.0.iter().map(|(_, s)| s))
	}
}

/// Extension trait to convert from [`sp_npos_elections::Supports<AccountId>`] to `BoundedSupports`.
pub trait TryIntoBoundedSupports<AccountId, BOuter: Get<u32>, BInner: Get<u32>> {
	/// Perform the conversion.
	fn try_into_bounded_supports(self) -> Result<BoundedSupports<AccountId, BOuter, BInner>, ()>;
}

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>>
	TryIntoBoundedSupports<AccountId, BOuter, BInner> for sp_npos_elections::Supports<AccountId>
{
	fn try_into_bounded_supports(self) -> Result<BoundedSupports<AccountId, BOuter, BInner>, ()> {
		let inner_bounded_supports = self
			.into_iter()
			.map(|(a, s)| s.try_into().map(|s| (a, s)))
			.collect::<Result<Vec<_>, _>>()
			.map_err(|_| ())?;
		let outer_bounded_supports: BoundedVec<_, BOuter> =
			inner_bounded_supports.try_into().map_err(|_| ())?;
		Ok(outer_bounded_supports.into())
	}
}

// TODO: most of these conversion traits are doing allocations, but no other way other than unsafe
// code as it seems.

/// Extension trait to convert an unbounded [`sp_npos_elections::Supports`]
// NOTE: someday we can have an expensive `SortIntoBoundedSupports` as well.
pub trait TruncateIntoBoundedSupports<AccountId, BOuter: Get<u32>, BInner: Get<u32>> {
	fn truncate_into_bounded_supports(self) -> BoundedSupports<AccountId, BOuter, BInner>;
}

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>>
	TruncateIntoBoundedSupports<AccountId, BOuter, BInner> for sp_npos_elections::Supports<AccountId>
{
	fn truncate_into_bounded_supports(mut self) -> BoundedSupports<AccountId, BOuter, BInner> {
		// truncate the inner stuff.
		self.iter_mut().for_each(|(_, s)| s.voters.truncate(BInner::get() as usize));
		// truncate the outer stuff.
		self.truncate(BOuter::get() as usize);
		self.try_into_bounded_supports().expect("truncated self to proper bounds; qed")
	}
}

/// Same as [`TryIntoBoundedSupports`], but wrapped in another vector as well.
///
/// The vector can represent a [`PageIndex`].
pub trait TryIntoBoundedSupportsVec<AccountId, BOuter: Get<u32>, BInner: Get<u32>> {
	/// Perform the conversion.
	fn try_into_bounded_supports_vec(
		self,
	) -> Result<Vec<BoundedSupports<AccountId, BOuter, BInner>>, ()>;
}

impl<AccountId, BOuter: Get<u32>, BInner: Get<u32>>
	TryIntoBoundedSupportsVec<AccountId, BOuter, BInner>
	for Vec<sp_npos_elections::Supports<AccountId>>
{
	fn try_into_bounded_supports_vec(
		self,
	) -> Result<Vec<BoundedSupports<AccountId, BOuter, BInner>>, ()> {
		self.into_iter()
			.map(|s| s.try_into_bounded_supports())
			.collect::<Result<Vec<_>, ()>>()
	}
}

/// Extension trait to easily convert from unbounded voters to bounded ones.
pub trait TryIntoBoundedVoters<AccountId, MaxVotesPerVoter: Get<u32>> {
	/// Perform the conversion.
	fn try_into_bounded_voters(self) -> Result<Vec<Voter<AccountId, MaxVotesPerVoter>>, ()>;
}

impl<AccountId, MaxVotesPerVoter: Get<u32>> TryIntoBoundedVoters<AccountId, MaxVotesPerVoter>
	for Vec<(AccountId, VoteWeight, Vec<AccountId>)>
{
	fn try_into_bounded_voters(self) -> Result<Vec<Voter<AccountId, MaxVotesPerVoter>>, ()> {
		self.into_iter()
			.map(|(x, y, z)| z.try_into().map(|z| (x, y, z)))
			.collect::<Result<Vec<_>, _>>()
			.map_err(|_| ())
	}
}

/// Extension trait to easily convert from bounded voters to unbounded ones.
pub trait IntoUnboundedVoters<AccountId> {
	fn into_unbounded_voters(self) -> Vec<(AccountId, VoteWeight, Vec<AccountId>)>;
}

impl<AccountId, Bound: Get<u32>> IntoUnboundedVoters<AccountId> for Vec<Voter<AccountId, Bound>> {
	fn into_unbounded_voters(self) -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
		self.into_iter().map(|(x, y, z)| (x, y, z.into_inner())).collect::<Vec<_>>()
	}
}
