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
//! # use sp_election_providers::*;
//! # use sp_npos_elections::{Support, Assignment};
//!
//! type AccountId = u64;
//! type Balance = u64;
//! type BlockNumber = u32;
//!
//! mod data_provider {
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
//!         fn desired_targets() -> u32 {
//!             1
//!         }
//!         fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
//!             Default::default()
//!         }
//!         fn targets() -> Vec<AccountId> {
//!             vec![10, 20, 30]
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
//!         type Error = ();
//!         type DataProvider = T::DataProvider;
//!
//!         fn elect() -> Result<Supports<AccountId>, Self::Error> {
//!             Self::DataProvider::targets()
//!                 .first()
//!                 .map(|winner| vec![(*winner, Support::default())])
//!                 .ok_or(())
//!         }
//!     }
//! }
//!
//! mod runtime {
//!     use super::generic_election_provider;
//!     use super::data_provider;
//!     use super::AccountId;
//!
//!     struct Runtime;
//!     impl generic_election_provider::Config for Runtime {
//!         type DataProvider = data_provider::Module<Runtime>;
//!     }
//!
//!     impl data_provider::Config for Runtime {
//!         type ElectionProvider = generic_election_provider::GenericElectionProvider<Runtime>;
//!     }
//!
//! }
//!
//! # fn main() {}
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

pub mod onchain;
use sp_std::{prelude::*, fmt::Debug};

/// Re-export some type as they are used in the interface.
pub use sp_arithmetic::PerThing;
pub use sp_npos_elections::{Assignment, ExtendedBalance, PerThing128, Supports, VoteWeight};

/// Something that can provide the data to an [`ElectionProvider`].
pub trait ElectionDataProvider<AccountId, BlockNumber> {
	/// All possible targets for the election, i.e. the candidates.
	fn targets() -> Vec<AccountId>;

	/// All possible voters for the election.
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)>;

	/// The number of targets to elect.
	fn desired_targets() -> u32;

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
	) {
	}
}

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionDataProvider<AccountId, BlockNumber> for () {
	fn targets() -> Vec<AccountId> {
		Default::default()
	}
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
		Default::default()
	}
	fn desired_targets() -> u32 {
		Default::default()
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
	/// The result is returned in a target major format, namely as vector of  supports.
	fn elect() -> Result<Supports<AccountId>, Self::Error>;
}

#[cfg(feature = "std")]
impl<AccountId, BlockNumber> ElectionProvider<AccountId, BlockNumber> for () {
	type Error = &'static str;
	type DataProvider = ();

	fn elect() -> Result<Supports<AccountId>, Self::Error> {
		Err("<() as ElectionProvider> cannot do anything.")
	}
}
