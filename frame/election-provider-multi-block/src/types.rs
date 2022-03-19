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

use frame_support::{
	BoundedVec, CloneNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use sp_std::{collections::btree_set::BTreeSet, fmt::Debug, prelude::*};

use crate::Verifier;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::{BoundedSupports, ElectionProvider};
pub use frame_election_provider_support::{NposSolution, PageIndex};
use scale_info::TypeInfo;
pub use sp_npos_elections::{ElectionResult, ElectionScore};
use sp_runtime::{
	traits::{One, Saturating, Zero},
	SaturatedConversion,
};

/// The supports that's returned from a given [`Verifier`]. TODO: rename this
pub type SupportsOf<V> = BoundedSupports<
	<V as Verifier>::AccountId,
	<V as Verifier>::MaxWinnersPerPage,
	<V as Verifier>::MaxBackersPerWinner,
>;

/// The solution type used by this crate.
pub type SolutionOf<T> = <T as crate::Config>::Solution;

/// The voter index. Derived from [`SolutionOf`].
pub type SolutionVoterIndexOf<T> = <SolutionOf<T> as NposSolution>::VoterIndex;
/// The target index. Derived from [`SolutionOf`].
pub type SolutionTargetIndexOf<T> = <SolutionOf<T> as NposSolution>::TargetIndex;
/// The accuracy of the election, when submitted from offchain. Derived from [`SolutionOf`].
pub type SolutionAccuracyOf<T> = <SolutionOf<T> as NposSolution>::Accuracy;
/// The fallback election type.
pub type FallbackErrorOf<T> = <<T as crate::Config>::Fallback as ElectionProvider>::Error;

/// The relative distribution of a voter's stake among the winning targets.
pub type AssignmentOf<T> =
	sp_npos_elections::Assignment<<T as frame_system::Config>::AccountId, SolutionAccuracyOf<T>>;

#[derive(
	TypeInfo,
	Encode,
	Decode,
	RuntimeDebugNoBound,
	CloneNoBound,
	EqNoBound,
	PartialEqNoBound,
	MaxEncodedLen,
	DefaultNoBound,
)]
#[codec(mel_bound(T: crate::Config))]
#[scale_info(skip_type_params(T))]
pub struct PagedRawSolution<T: crate::Config> {
	pub solution_pages: BoundedVec<SolutionOf<T>, T::Pages>,
	pub score: ElectionScore,
	pub round: u32,
}

/// A helper trait to deal with the page index of partial solutions.
///
/// This should only be called on the `Vec<Solution>` or similar types. If the solution is *full*,
/// then it returns a normal iterator that is just mapping the index (usize) to `PageIndex`.
///
/// if the solution is partial, it shifts the indices sufficiently so that the most significant page
/// of the solution matches with the most significant page of the snapshot onchain.
pub trait Pagify<T> {
	fn pagify(&self, bound: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, &T)> + '_>;
	fn into_pagify(self, bound: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, T)>>;
}

impl<T> Pagify<T> for Vec<T> {
	fn pagify(&self, desired_pages: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, &T)> + '_> {
		Box::new(
			self.into_iter()
				.enumerate()
				.map(|(p, s)| (p.saturated_into::<PageIndex>(), s))
				.map(move |(p, s)| {
					let desired_pages_usize = desired_pages as usize;
					// TODO: this could be an error.
					debug_assert!(self.len() <= desired_pages_usize);
					let padding = desired_pages_usize.saturating_sub(self.len());
					let new_page = p.saturating_add(padding.saturated_into::<PageIndex>());
					(new_page, s)
				}),
		)
	}

	fn into_pagify(self, _: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, T)>> {
		todo!()
	}
}

pub trait PadSolutionPages: Sized {
	fn pad_solution_pages(self, desired_pages: PageIndex) -> Self;
}

impl<T: Default + Clone, Bound: frame_support::traits::Get<u32>> PadSolutionPages
	for BoundedVec<T, Bound>
{
	fn pad_solution_pages(self, desired_pages: PageIndex) -> Self {
		let desired_pages_usize = (desired_pages).min(Bound::get()) as usize;
		debug_assert!(self.len() <= desired_pages_usize);
		if self.len() == desired_pages_usize {
			return self
		}

		// we basically need to prepend the list with this many items.
		let empty_slots = desired_pages_usize.saturating_sub(self.len());
		let self_as_vec = sp_std::iter::repeat(Default::default())
			.take(empty_slots)
			.chain(self.into_iter())
			.collect::<Vec<_>>();
		self_as_vec.try_into().expect("sum of both iterators has at most `desired_pages_usize` items; `desired_pages_usize` is `min`-ed by `Bound`; conversion cannot fail; qed")
	}
}

impl<T: crate::Config> PagedRawSolution<T> {
	/// Get the total number of voters, assuming that voters in each page are unique.
	pub fn voter_count(&self) -> usize {
		self.solution_pages
			.iter()
			.map(|page| page.voter_count())
			.fold(0usize, |acc, x| acc.saturating_add(x))
	}

	/// Get the total number of winners, assuming that there's only a single page of targets.
	pub fn winner_count_single_page_target_snapshot(&self) -> usize {
		self.solution_pages
			.iter()
			.map(|page| page.unique_targets())
			.into_iter()
			.flatten()
			.collect::<BTreeSet<_>>()
			.len()
	}

	/// Get the total number of edges.
	pub fn edge_count(&self) -> usize {
		self.solution_pages
			.iter()
			.map(|page| page.edge_count())
			.fold(0usize, |acc, x| acc.saturating_add(x))
	}
}

// NOTE on naming conventions: type aliases that end with `Of` should always be `Of<T: Config>`.

/// Alias for a voter, parameterized by this crate's config.
pub(crate) type VoterOf<T> =
	frame_election_provider_support::VoterOf<<T as crate::Config>::DataProvider>;

/// Alias for a page of voters, parameterized by this crate's config.
pub(crate) type VoterPageOf<T> =
	BoundedVec<VoterOf<T>, <T as crate::Config>::VoterSnapshotPerBlock>;

/// Alias for all pages of voters, parameterized by this crate's config.
pub(crate) type AllVoterPagesOf<T> = BoundedVec<VoterPageOf<T>, <T as crate::Config>::Pages>;

/// Maximum number of items that [`AllVoterPagesOf`] can contain, when flattened.
pub(crate) struct MaxFlattenedVoters<T: crate::Config>(sp_std::marker::PhantomData<T>);
impl<T: crate::Config> frame_support::traits::Get<u32> for MaxFlattenedVoters<T> {
	fn get() -> u32 {
		T::VoterSnapshotPerBlock::get().saturating_mul(T::Pages::get())
	}
}

/// Same as [`AllVoterPagesOf`], but instead of being a nested bounded vec, the entire voters are
/// flattened into one outer, unbounded `Vec` type.
///
/// This is bounded by [`MaxFlattenedVoters`].
pub(crate) type AllVoterPagesFlattenedOf<T> = BoundedVec<VoterOf<T>, MaxFlattenedVoters<T>>;

/// Encodes the length of a solution or a snapshot.
///
/// This is stored automatically on-chain, and it contains the **size of the entire snapshot**.
/// This is also used in dispatchables as weight witness data and should **only contain the size of
/// the presented solution**, not the entire snapshot.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, Debug, Default, TypeInfo, MaxEncodedLen)]
pub struct SolutionOrSnapshotSize {
	/// The length of voters.
	#[codec(compact)]
	pub voters: u32,
	/// The length of targets.
	#[codec(compact)]
	pub targets: u32,
}

/// The type of `Computation` that provided this election data.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
pub enum ElectionCompute {
	/// Election was computed on-chain.
	OnChain,
	/// Election was computed with a signed submission.
	Signed,
	/// Election was computed with an unsigned submission.
	Unsigned,
	/// Election was computed with emergency status.
	Emergency,
}

impl Default for ElectionCompute {
	fn default() -> Self {
		ElectionCompute::OnChain
	}
}

#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, MaxEncodedLen, Debug, TypeInfo)]
pub enum PhaseExperimental<BlockNumber> {
	Off,
	Snapshot(BlockNumber),
	Signed(BlockNumber),
	SignedValidation(BlockNumber),
	Unsigned(BlockNumber),
	Emergency,
}

impl<BlockNumber: Saturating + Zero + One> PhaseExperimental<BlockNumber> {
	pub fn tick(self, next_phase_len: BlockNumber) -> Self {
		use PhaseExperimental::*;
		match self {
			Off => Snapshot(next_phase_len),
			Snapshot(x) =>
				if x.is_zero() {
					Signed(next_phase_len)
				} else {
					Snapshot(x.saturating_sub(One::one()))
				},
			Signed(x) =>
				if x.is_zero() {
					SignedValidation(next_phase_len)
				} else {
					Signed(x.saturating_sub(One::one()))
				},
			SignedValidation(x) =>
				if x.is_zero() {
					Unsigned(next_phase_len)
				} else {
					SignedValidation(x.saturating_sub(One::one()))
				},

			Unsigned(x) =>
				if x.is_zero() {
					// note this: unsigned phase does not really end, only elect can end it.
					Unsigned(Zero::zero())
				} else {
					Unsigned(x.saturating_sub(One::one()))
				},
			Emergency => Emergency,
		}
	}
}

/// Current phase of the pallet.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, MaxEncodedLen, Debug, TypeInfo)]
pub enum Phase<Bn> {
	/// Nothing is happening, and nothing will happen.
	Halted,
	/// Nothing is happening, but it might.
	Off,
	/// Signed phase is open.
	Signed,
	/// We are validating results.
	///
	/// The inner value is the block number at which this phase started. This helps with
	/// synchronizing different sub-systems.
	///
	/// This always follows the signed phase, and is a window of time in which we try to validate
	/// our signed results.
	SignedValidation(Bn),
	/// Unsigned phase. First element is whether it is active or not, second the starting block
	/// number.
	///
	/// We do not yet check whether the unsigned phase is active or passive. The intent is for the
	/// blockchain to be able to declare: "I believe that there exists an adequate signed
	/// solution," advising validators not to bother running the unsigned offchain worker.
	///
	/// As validator nodes are free to edit their OCW code, they could simply ignore this advisory
	/// and always compute their own solution. However, by default, when the unsigned phase is
	/// passive, the offchain workers will not bother running.
	Unsigned(Bn),
	/// Snapshot is being created. No other operation is allowed. This can be one or more blocks.
	/// The inner value should be read as "`remaining` number of pages are left to be fetched".
	/// Thus, if inner value is `0` if the snapshot is complete and we are ready to move on.
	///
	/// This value should be interpreted after `on_initialize` of this pallet has already been
	/// called.
	Snapshot(PageIndex),
	/// Exporting has begun.
	///
	/// Once this is active, no more signed or solutions will be accepted.
	Export,
	/// The emergency phase. This is enabled upon a failing call to `T::ElectionProvider::elect`.
	/// After that, the only way to leave this phase is through a successful
	/// `T::ElectionProvider::elect`.
	Emergency,
}

impl<Bn> Default for Phase<Bn> {
	fn default() -> Self {
		Phase::Off
	}
}

impl<Bn: PartialEq + Eq> Phase<Bn> {
	/// Whether the phase is emergency or not.
	pub fn is_emergency(&self) -> bool {
		matches!(self, Phase::Emergency)
	}

	/// Whether the phase is signed or not.
	pub fn is_signed(&self) -> bool {
		matches!(self, Phase::Signed)
	}

	/// Whether the phase is unsigned or not.
	pub fn is_unsigned(&self) -> bool {
		matches!(self, Phase::Unsigned(_))
	}

	/// Whether the phase is unsigned and open or not, with specific start.
	pub fn is_unsigned_open_at(&self, at: Bn) -> bool {
		matches!(self, Phase::Unsigned(real) if *real == at)
	}

	/// Whether the phase is off or not.
	pub fn is_off(&self) -> bool {
		matches!(self, Phase::Off)
	}

	/// Whether the phase is export or not.
	pub fn is_export(&self) -> bool {
		matches!(self, Phase::Export)
	}

	/// Whether the phase is halted or not.
	pub fn is_halted(&self) -> bool {
		matches!(self, Phase::Halted)
	}

	/// Whether the phase is signed validation or not.
	pub fn is_signed_validation(&self) -> bool {
		matches!(self, Phase::SignedValidation(_))
	}

	/// Whether the phase is signed validation or not, with specific start.
	pub fn is_signed_validation_open_at(&self, at: Bn) -> bool {
		matches!(self, Phase::SignedValidation(real) if *real == at)
	}
}

#[cfg(test)]
mod pagify {
	use frame_support::{bounded_vec, traits::ConstU32, BoundedVec};

	use super::{PadSolutionPages, Pagify};

	#[test]
	fn pagify_works() {
		// is a noop when you have the same length
		assert_eq!(
			vec![10, 11, 12].pagify(3).collect::<Vec<_>>(),
			vec![(0, &10), (1, &11), (2, &12)]
		);

		// pads the values otherwise
		assert_eq!(vec![10, 11].pagify(3).collect::<Vec<_>>(), vec![(1, &10), (2, &11)]);
		assert_eq!(vec![10].pagify(3).collect::<Vec<_>>(), vec![(2, &10)]);
	}

	#[test]
	fn pad_solution_pages_works() {
		// noop if the solution is complete, as with pagify.
		let solution: BoundedVec<_, ConstU32<3>> = bounded_vec![1u32, 2, 3];
		assert_eq!(solution.pad_solution_pages(3).into_inner(), vec![1, 2, 3]);

		// pads the solution with default if partial..
		let solution: BoundedVec<_, ConstU32<3>> = bounded_vec![2, 3];
		assert_eq!(solution.pad_solution_pages(3).into_inner(), vec![0, 2, 3]);

		// behaves the same as `pad_solution_pages(3)`.
		let solution: BoundedVec<_, ConstU32<3>> = bounded_vec![2, 3];
		assert_eq!(solution.pad_solution_pages(4).into_inner(), vec![0, 2, 3]);
	}
}
