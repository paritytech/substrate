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

//! # The verifier pallet
//!
//! TODO

mod impls;

// internal imports
use crate::{SolutionOf, SupportsOf};
use frame_election_provider_support::PageIndex;
use frame_support::RuntimeDebug;
use sp_npos_elections::ElectionScore;
use std::fmt::Debug;

pub use impls::{
	pallet::{Call, Config, Error, Event, Pallet, QueuedSolution, __substrate_event_check},
	Status,
};

/// Errors that can happen in the feasibility check.
#[derive(Debug, Eq, PartialEq, codec::Encode, codec::Decode, scale_info::TypeInfo, Clone)]
pub enum FeasibilityError {
	/// Wrong number of winners presented.
	WrongWinnerCount,
	/// The snapshot is not available.
	///
	/// Kinda defensive: The pallet should technically never attempt to do a feasibility check
	/// when no snapshot is present.
	SnapshotUnavailable,
	/// A vote is invalid.
	InvalidVote,
	/// A voter is invalid.
	InvalidVoter,
	/// A winner is invalid.
	InvalidWinner,
	/// The given score was invalid.
	InvalidScore,
	/// The provided round is incorrect.
	InvalidRound,
	/// Solution does not have a good enough score.
	ScoreTooLow,
	/// A single target has too many backings
	TooManyBackings,
	/// Internal error from the election crate.
	#[codec(skip)]
	NposElection(sp_npos_elections::Error),
	/// The solution is incomplete, it has too few pages.
	///
	/// This is (somewhat) synonym to `WrongPageCount` in other places.
	Incomplete,
}

impl From<sp_npos_elections::Error> for FeasibilityError {
	fn from(e: sp_npos_elections::Error) -> Self {
		FeasibilityError::NposElection(e)
	}
}

/// The interface of something that can verify solutions for other sub-pallets.
pub trait Verifier {
	/// The solution type.
	type Solution;
	/// The account if type.
	type AccountId;

	type MaxBackersPerWinner: frame_support::traits::Get<u32>;
	// NOTE: This one is a tricky, we can't know this in advance. This is determined by the
	// validator count of staking. We should not set this to be too high, since it would mean that
	// all of our worse cases are actually worse, but ideally it should follow
	// staking::validator_count closely.
	type MaxWinnersPerPage: frame_support::traits::Get<u32>;

	/// The score of the current best solution. `None` if there is no best solution.
	fn queued_solution() -> Option<ElectionScore>;

	/// Check if the claimed score is sufficient.
	fn ensure_claimed_score_improves(claimed_score: ElectionScore) -> bool;

	/// Get the current stage of the verification process.
	fn status() -> Status;

	/// Clear everything, there's nothing else for you to do until further notice.
	fn kill();

	/// Get the best verified solution, if any.
	///
	/// It is the responsibility of the call site to call this function with all appropriate
	/// `page` arguments.
	fn get_queued_solution_page(page: PageIndex) -> Option<SupportsOf<Self>>;

	/// Perform the feasibility check of the given solution page.
	///
	/// This will not check the score or winner-count, since they can only be checked in
	/// context.
	///
	/// Corresponding snapshots are assumed to be available.
	///
	/// A page that is `None` must always be valid.
	fn feasibility_check_page(
		partial_solution: Self::Solution,
		page: PageIndex,
	) -> Result<SupportsOf<Self>, FeasibilityError>;

	/// Forcibly write this solution into the current valid variant.
	///
	/// This typically should only be called when you know that this solution is better than we
	/// we have currently queued. The provided score is assumed to be correct.
	///
	/// For now this is only needed for single page solution, thus the api will only support
	/// that.
	fn force_set_single_page_verified_solution(
		single_page_solution: SupportsOf<Self>,
		verified_score: ElectionScore,
	);
}

/// Simple enum to encapsulate the result of the verification of a candidate solution.
#[derive(Clone, Copy, RuntimeDebug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum VerificationResult {
	/// Solution is valid.
	Valid,
	/// Solution is invalid.
	Invalid,
}

/// Something that can provide candidate solutions to the verifier.
///
/// In reality, this can be implemented by the [`crate::signed::Pallet`], where signed solutions are
/// queued and sorted based on claimed score, and they are put forth one by one, from best to worse.
pub trait SolutionDataProvider {
	/// The opaque solution type.
	type Solution;

	/// Return the `page`th page of the current best solution that the data provider has in store.
	///
	/// If no candidate solutions are available, then None is returned.
	fn get_page(page: PageIndex) -> Option<Self::Solution>;

	/// Get the claimed score of the current best solution.
	fn get_score() -> Option<ElectionScore>;

	/// Hook to report back the results of the verification of the current candidate solution that
	/// is being exposed via [`get_page`] and [`get_score`].
	///
	/// Every time that this is called, the verifier [`SignedVerifier`] goes back to the
	/// [`Status::Nothing`] state, and it is the responsibility of [`Self`] to call `start` again,
	/// if desired.
	fn report_result(result: VerificationResult);
}

/// Something that can do the verification, with the flavour that is suitable for the signed phase.
pub trait SignedVerifier: Verifier {
	/// The data provider that can provide the candidate solution, and to whom we report back the
	/// results.
	type SolutionDataProvider: SolutionDataProvider;

	/// Start a verification process.
	///
	/// From the coming block onwards, the verifier will start and fetch the relevant information
	/// and solution pages from [`SolutionDataProvider`]. It is expected that the
	/// [`SolutionDataProvider`] is ready before calling [`start`].
	///
	/// Pages of the solution are fetched sequentially and in order from [`SolutionDataProvider`],
	/// from `msp` to `lsp`.
	///
	/// This ends in either of the two:
	///
	/// 1. All pages, including the final checks (like score and other facts that can only be
	///    derived from a full solution) are valid and the solution is verified. The solution is
	///    queued and is ready for further export.
	/// 2. The solution checks verification at one of the steps. Nothing is stored inside the
	///    verifier pallet and all intermediary data is removed.
	///
	/// In both cases, the [`SolutionDataProvider`] is informed via
	/// [`SolutionDataProvider::report_result`]. It is sensible for the data provide to call `start`
	/// again if the verification has failed, and nothing otherwise. Indeed, the
	/// [`SolutionDataProvider`] must adjust its internal state such that it returns a new candidate
	/// solution after each failure.
	fn start();

	/// Stop the verification.
	///
	/// This is a force-stop operation, and should only be used in extreme cases where the
	/// [`SolutionDataProvider`] wants to suddenly bail-out.
	///
	/// An implementation should make sure that no loose ends remain state-wise, and everything is
	/// cleaned.
	fn stop();
}

// TODO: we can probably simply this quite a lot, maybe even merge the two traits.
impl<T: Config> Verifier for Pallet<T> {
	type AccountId = T::AccountId;
	type Solution = SolutionOf<T>;
	type MaxBackersPerWinner = T::MaxBackersPerWinner;
	type MaxWinnersPerPage = T::MaxWinnersPerPage;

	fn ensure_claimed_score_improves(claimed_score: ElectionScore) -> bool {
		Self::ensure_score_quality(claimed_score).is_ok()
	}

	fn queued_solution() -> Option<ElectionScore> {
		QueuedSolution::<T>::queued_solution()
	}

	fn status() -> Status {
		Pallet::<T>::status_storage()
	}

	fn kill() {
		// TODO: shan't we clear anything else here?
		QueuedSolution::<T>::kill();
	}

	fn get_queued_solution_page(page: PageIndex) -> Option<SupportsOf<Self>> {
		QueuedSolution::<T>::get_queued_solution_page(page)
	}

	fn feasibility_check_page(
		partial_solution: Self::Solution,
		page: PageIndex,
	) -> Result<SupportsOf<Self>, FeasibilityError> {
		Self::feasibility_check_page_inner(partial_solution, page)
	}

	fn force_set_single_page_verified_solution(
		partial_supports: SupportsOf<Self>,
		verified_score: ElectionScore,
	) {
		QueuedSolution::<T>::force_set_single_page_valid(0, partial_supports, verified_score);
	}
}
