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
use impls::pallet::QueuedSolution;
use sp_npos_elections::ElectionScore;
use std::fmt::Debug;

pub use impls::{
	pallet::{Call, Config, Error, Event, Pallet, __substrate_event_check},
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

#[derive(Clone, Copy, RuntimeDebug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum VerificationResult {
	Valid,
	Invalid,
}

pub trait SolutionDataProvider {
	type Solution;
	fn get_page(page: PageIndex) -> Self::Solution;
	fn get_score() -> ElectionScore;
	fn report_result(result: VerificationResult);
}

/// Something that can do the verification, with the flavour that is suitable for the signed phase.
pub trait SignedVerifier: Verifier {
	type SolutionDataProvider: SolutionDataProvider;
	fn start();
}

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
