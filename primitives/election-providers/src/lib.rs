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
//! This crate provides two traits that could potentially be implemented by two struct. The struct
//! receiving the functionality election could potentially implement [`ElectionDataProvider`] and
//! the struct providing the election functionality implements [`ElectionProvider`].

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{fmt::Debug, prelude::*};

use sp_arithmetic::PerThing;
use sp_npos_elections::{CompactSolution, ExtendedBalance, PerThing128, Supports, VoteWeight};

/// Something that can provide the data to something else that implements [`ElectionProvider`], such
/// as the [`two_phase`] module.
///
/// The underlying purpose of this is to provide auxillary data to long-lasting election providers.
/// For example, the [`two_phase`] election provider needs to know the voters/targets list well in
/// advance and before a call to [`ElectionProvider::elect`].
///
/// For example, if pallet A wants to use the two-phase election:
///
/// ```rust,ignore
/// pub trait TraitA {
///     type ElectionProvider: ElectionProvider<_, _>;
/// }
///
/// // these function will be called by `Self::ElectionProvider` whenever needed.
/// impl ElectionDataProvider for PalletA { /* ..  */ }
///
/// impl<T: TraitA> Module<T> {
///     fn do_election() {
///         // finalize the election.
///         T::ElectionProvider::elect( /* .. */ );
///     }
/// }
/// ```
pub trait ElectionDataProvider<AccountId, B> {
	/// The compact solution type.
	///
	/// This should encode the entire solution with the least possible space usage.
	type CompactSolution: codec::Codec + Default + PartialEq + Eq + Clone + Debug + CompactSolution;

	/// All possible targets for the election, i.e. the candidates.
	fn targets() -> Vec<AccountId>;

	/// All possible voters for the election.
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)>;

	/// The number of targets to elect.
	fn desired_targets() -> u32;

	/// Check the feasibility of a single assignment for the underlying `ElectionProvider`. In other
	/// words, check if `who` having a weight distribution described as `distribution` is correct or
	/// not.
	///
	/// This might be called by the [`ElectionProvider`] upon processing solutions.
	fn feasibility_check_assignment<P: PerThing>(
		who: &AccountId,
		distribution: &[(AccountId, P)],
	) -> bool;

	/// Provide a best effort prediction about when the next election is about to happen.
	///
	/// In essence, `Self` should predict with this function when it will trigger the
	/// `ElectionDataProvider::elect`.
	fn next_election_prediction(now: B) -> B;
}

/// Something that can compute the result of an election and pass it back to the caller.
pub trait ElectionProvider<AccountId> {
	/// Indicate weather this election provider needs data when calling [`elect`] or not. If
	/// `false`, then the call site can ignore all parameters of [`elect`]
	const NEEDS_ELECT_DATA: bool;

	/// The error type that is returned by the provider.
	type Error;

	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as a support map.
	///
	/// Note that based on the logic of the type that will implement this trait, the input data may
	/// or may not be used. To hint about this to the call site, [`NEEDS_ELECT_DATA`] should be
	/// properly set.
	///
	/// The implementation should, if possible, use the accuracy `P` to compute the election result.
	fn elect<P: PerThing128>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<Supports<AccountId>, Self::Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>;

	/// Returns true if an election is still ongoing.
	///
	/// This can be used by the call site to dynamically check of a long-lasting election (such as
	/// [`two_phase`]) is still on-going or not.
	fn ongoing() -> bool;
}
