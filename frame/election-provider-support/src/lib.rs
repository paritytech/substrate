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
//! # use frame_election_provider_support::{*, data_provider};
//! # use sp_npos_elections::{Support, Assignment};
//! # use frame_support::weights::Weight;
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
//!             AccountId,
//!             BlockNumber,
//!             DataProvider = Module<Self>,
//!         >;
//!     }
//!
//!     pub struct Module<T: Config>(std::marker::PhantomData<T>);
//!
//!     impl<T: Config> ElectionDataProvider<AccountId, BlockNumber> for Module<T> {
//!         const MAXIMUM_VOTES_PER_VOTER: u32 = 1;
//!         fn desired_targets() -> data_provider::Result<(u32, Weight)> {
//!             Ok((1, 0))
//!         }
//!         fn voters(maybe_max_len: Option<usize>)
//!         -> data_provider::Result<(Vec<(AccountId, VoteWeight, Vec<AccountId>)>, Weight)>
//!         {
//!             Ok((Default::default(), 0))
//!         }
//!         fn targets(maybe_max_len: Option<usize>) -> data_provider::Result<(Vec<AccountId>, Weight)> {
//!             Ok((vec![10, 20, 30], 0))
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
//!         type DataProvider: ElectionDataProvider<AccountId, BlockNumber>;
//!     }
//!
//!     impl<T: Config> ElectionProvider<AccountId, BlockNumber> for GenericElectionProvider<T> {
//!         type Error = &'static str;
//!         type DataProvider = T::DataProvider;
//!
//!         fn elect() -> Result<(Supports<AccountId>, Weight), Self::Error> {
//!             Self::DataProvider::targets(None)
//!                 .map_err(|_| "failed to elect")
//!                 .map(|(t, weight)| {
//! 						(vec![(t[0], Support::default())], weight)
//! 				})
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
//!         type DataProvider = data_provider_mod::Module<Runtime>;
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
use frame_support::weights::Weight;
use sp_std::{fmt::Debug, prelude::*};

/// Re-export some type as they are used in the interface.
pub use sp_arithmetic::PerThing;
pub use sp_npos_elections::{
	Assignment, ExtendedBalance, PerThing128, Support, Supports, VoteWeight,
};

/// Types that are used by the data provider trait.
pub mod data_provider {
	/// Alias for the result type of the election data provider.
	pub type Result<T> = sp_std::result::Result<T, &'static str>;
}

pub type PageIndex = u8;

/// Something that can provide the data to an [`ElectionProvider`].
pub trait ElectionDataProvider<AccountId, BlockNumber> {
	/// Maximum number of votes per voter that this data provider is providing.
	const MAXIMUM_VOTES_PER_VOTER: u32;

	/// All possible targets for the election, i.e. the candidates.
	///
	/// If `maybe_page_size` is `Some(v)` then the resulting vector MUST NOT be longer than `v` items
	/// long.
	///
	/// It is assumed that this function will only consume a notable amount of weight, when it
	/// returns `Ok(_)`.
	// TODO: remove the weight from the interface.
	fn targets(
		maybe_page_size: Option<usize>,
		remaining_pages: PageIndex,
	) -> data_provider::Result<(Vec<AccountId>, Weight)>;

	/// All possible voters for the election.
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	///
	/// If `maybe_page_size` is `Some(v)` then the resulting vector MUST NOT be longer than `v` items
	/// long.
	///
	/// It is assumed that this function will only consume a notable amount of weight, when it
	/// returns `Ok(_)`.
	fn voters(
		maybe_page_size: Option<usize>,
		remaining_pages: PageIndex,
	) -> data_provider::Result<(Vec<(AccountId, VoteWeight, Vec<AccountId>)>, Weight)>;

	/// The number of targets to elect.
	fn desired_targets() -> data_provider::Result<(u32, Weight)>;

	/// Provide a best effort prediction about when the next election is about to happen.
	///
	/// In essence, the implementor should predict with this function when it will trigger the
	/// [`ElectionProvider::elect`].
	///
	/// This is only useful for stateful election providers.
	fn next_election_prediction(now: BlockNumber) -> BlockNumber;

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn put_snapshot(
		_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
		_targets: Vec<AccountId>,
		_target_stake: Option<VoteWeight>,
	) {
	}

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	///
	/// Same as `put_snapshot`, but can add a single voter one by one.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_voter(_voter: AccountId, _weight: VoteWeight, _targets: Vec<AccountId>) {}

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	///
	/// Same as `put_snapshot`, but can add a single voter one by one.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_target(_target: AccountId) {}

	/// Clear all voters and targets.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn clear() {}
}

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionDataProvider<AccountId, BlockNumber> for () {
	const MAXIMUM_VOTES_PER_VOTER: u32 = 0;
	fn targets(_: Option<usize>, _: PageIndex) -> data_provider::Result<(Vec<AccountId>, Weight)> {
		Ok(Default::default())
	}
	fn voters(
		_: Option<usize>,
		_: PageIndex,
	) -> data_provider::Result<(Vec<(AccountId, VoteWeight, Vec<AccountId>)>, Weight)> {
		Ok(Default::default())
	}
	fn desired_targets() -> data_provider::Result<(u32, Weight)> {
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
pub trait ElectionProvider<AccountId, BlockNumber> {
	/// The error type that is returned by the provider.
	type Error: Debug;

	/// The data provider of the election.
	type DataProvider: ElectionDataProvider<AccountId, BlockNumber>;

	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as vector of supports.
	fn elect() -> Result<(Supports<AccountId>, Weight), Self::Error>;
}

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionProvider<AccountId, BlockNumber> for () {
	type Error = &'static str;
	type DataProvider = ();

	fn elect() -> Result<(Supports<AccountId>, Weight), Self::Error> {
		Err("<() as ElectionProvider> cannot do anything.")
	}
}

/// A utility trait for something to implement `ElectionDataProvider` in a sensible way.
///
/// This is generic over the `AccountId`'d sole, and it can represent a validator, a nominator, or
/// any other entity.
///
/// On the contrary, to simplify the trait, the `VoteWeight` is hardcoded as the weight of each
/// entity. The weights are scending, the higher, the better. In the long term, if this trait ends
/// up having use cases outside of the election context, it is easy enough to make it generic over
/// the `VoteWeight`.
///
/// Something that implements this trait will do a best-effort sort over ids, and thus can be
/// used on the implementing side of [`ElectionDataProvider`].
pub trait SortedListProvider<AccountId> {
	type Error: sp_std::fmt::Debug;

	/// Returns an iterator over the list, which can have `take` called on it.
	fn iter() -> Box<dyn Iterator<Item = AccountId>>;
	/// Returns an iterator over the list, starting from the given voter.
	///
	/// May return an error if `start` is invalid.
	fn iter_from(start: &AccountId) -> Result<Box<dyn Iterator<Item = AccountId>>, Self::Error>;
	/// get the current count of ids in the list.
	fn count() -> u32;
	/// Return true if the list already contains `id`.
	fn contains(id: &AccountId) -> bool;
	// Hook for inserting a new id.
	fn on_insert(id: AccountId, weight: VoteWeight) -> Result<(), Self::Error>;
	/// Hook for updating a single id.
	fn on_update(id: &AccountId, weight: VoteWeight);
	/// Hook for removing am id from the list.
	fn on_remove(id: &AccountId);
	/// Regenerate this list from scratch. Returns the count of items inserted.
	///
	/// This should typically only be used to enable this flag at a runtime upgrade.
	fn regenerate(
		all: impl IntoIterator<Item = AccountId>,
		weight_of: Box<dyn Fn(&AccountId) -> VoteWeight>,
	) -> u32;
	/// Remove everything.
	fn clear();
	/// Sanity check internal state of list. Only meant for debug compilation.
	fn sanity_check() -> Result<(), &'static str>;
}

/// Something that can provide the `VoteWeight` of an account. Similar to [`ElectionProvider`] and
/// [`ElectionDataProvider`], this should typically be implementing by whoever is supposed to *use*
/// `SortedListProvider`.
pub trait VoteWeightProvider<AccountId> {
	fn vote_weight(who: &AccountId) -> VoteWeight;

	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn set_vote_weight_of(_: &AccountId, _: VoteWeight) {}
}
