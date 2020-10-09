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

//! Reusable Election Providers.
//!
//! The core functionality of this crate is around [`ElectionProvider`]. An election provider is a
//! struct, module, or anything else that implements [`ElectionProvider`]. Such types can then be
//! passed around to other crates and pallets that need election functionality.
//!
//! Two main election providers are implemented in this crate.
//!
//! 1.  [`onchain`]: A `struct` that perform the election onchain (i.e. in the fly). This type is
//!     likely to be expensive for most chains and damage the block time. Only use when you are sure
//!     that the inputs are bounded and small enough.
//! 2. [`two_phase`]: An individual `pallet` that performs the election in two phases, signed and
//!    unsigned. Needless to say, the pallet needs to be included in the final runtime.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
/// The onchain module.
pub mod onchain;
/// The two-phase module.
pub mod two_phase;

use sp_arithmetic::PerThing;
use sp_npos_elections::{ExtendedBalance, Support, SupportMap};

// for the helper macros
#[doc(hidden)]
pub use sp_npos_elections::VoteWeight;
#[doc(hidden)]
pub use sp_std::convert::TryInto;

/// A flat variant of [`sp_npos_elections::SupportMap`].
///
/// The main advantage of this is that it is encodable.
pub type FlatSupportMap<A> = Vec<(A, Support<A>)>;

/// Helper trait to convert from a support map to a flat support vector.
pub trait FlattenSupportMap<A> {
	fn flatten(self) -> FlatSupportMap<A>;
}

impl<A> FlattenSupportMap<A> for SupportMap<A> {
	fn flatten(self) -> FlatSupportMap<A> {
		self.into_iter().map(|(k, v)| (k, v)).collect::<Vec<_>>()
	}
}

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
	type CompactSolution: codec::Codec + Default + PartialEq + Eq;
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

#[cfg(feature = "std")]
impl<AccountId, B: Default> ElectionDataProvider<AccountId, B> for () {
	fn targets() -> Vec<AccountId> {
		Default::default()
	}
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
		Default::default()
	}
	fn desired_targets() -> u32 {
		Default::default()
	}
	fn feasibility_check_assignment<P: PerThing>(_: &AccountId, _: &[(AccountId, P)]) -> bool {
		Default::default()
	}
	fn next_election_prediction(_: B) -> B {
		Default::default()
	}
}

/// Something that can compute the result of an election and pass it back to the caller.
pub trait ElectionProvider<AccountId> {
	/// Indicate weather this election provider needs data when calling [`elect`] or not.
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
	fn elect<P: PerThing>(
		to_elect: usize, // TODO: consider making this u32
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<FlatSupportMap<AccountId>, Self::Error>
	where
		// TODO: Okay about these two, I get that we probably need the first one, but can't we
		// alleviate the latter one? I think we can say that all PerThing are Mul of some types.
		// Perhaps it is time to move the PerBill macros to something better? Yeah I think then we
		// can get rid of both of these types everywhere.
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>;

	/// Returns true if an election is still ongoing. This can be used by the call site to
	/// dynamically check of a long-lasting election (such as [`two_phase`]) is still on-going or
	/// not.
	fn ongoing() -> bool;
}
