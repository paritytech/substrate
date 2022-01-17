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

//! # Multi-phase, multi-block, offchain-capable election provider pallet.
//!
//! ## Overall idea
//!
//! [`pallet_election_provider_multi_phase`] provides the basic ability for NPoS solutions to be
//! computed offchain (essentially anywhere) and submitted back to the chain as signed or unsigned
//! transaction, with sensible configurations and fail-safe mechanisms to ensure system safety.
//! Nonetheless, it has a limited capacity in terms of number of voters it can process in a **single
//! block**.
//!
//! This pallet takes [`pallet_election_provider_multi_phase`], keeps most of its ideas and core
//! premises, and extends it to support paginated, multi-block operations. The final goal of this
//! pallet is scale linearly with the number of blocks allocated to the elections. In principle,
//! with large enough blocks (in a dedicated parachain), the number of voters included in the NPoS
//! system can grow significantly (yet, obviously not indefinitely).
//!
//! Note that this pallet does not consider how the recipient is processing the results. To ensure
//! scalability, of course, the recipient of this pallet's data (i.e. `pallet-staking`) must also be
//! capable of pagination and multi-block processing.
//!
//! ## Companion pallets
//!
//! This pallet is essentially hiererichal. This particular one is the top level one. It contains
//! the shared information that all child pallets use. All child pallets can depend on on the top
//! level pallet, or each other, but not the other way around. For those cases, traits are used.
//!
//! This pallet will only function in a sensible way if it is peered with its companion pallets.
//!
//! - The [`verifier`] pallet provides a standard implementation of the [`verifier::Verifier`]. This
//!   pallet is mandatory.
//! - The [`unsigned`] module provides the implementation of unsigned submission by validators. If
//!   this pallet is included, then [`Config::UnsignedPhase`] will determine its duration.
//! - TODO: signed phase
//! - TODO: emergency phase.
//!
//! ## Pagination
//!
//! Most of the external APIs of this pallet are paginated. All pagination follow a patter where if
//! `N` pages exist, the first paginated call is `function(N-1)` and the last one is `function(0)`.
//! For example, with 3 pages, the `elect` of [`ElectionProvider`] is expected to be called as
//! `elect(2) -> elect(1) -> elect(0)`. In essence, calling a paginated function with index 0 is
//! always a signal of termination, meaning that no further calls will follow.
//!
//! ## Phases
//!
//! The timeline of pallet is as follows. At each block,
//! [`frame_election_provider_support::ElectionDataProvider::next_election_prediction`] is used to
//! estimate the time remaining to the next call to
//! [`frame_election_provider_support::ElectionProvider::elect`]. Based on this, a phase is chosen.
//! An example timeline is as follows:
//!
//! ```ignore
//!                                                                    elect()
//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
//!   +-------------------------------------------------------------------+
//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
//! ```
//!
//! The duration of both phases are configurable, and their existence is optional.
//!
//! Note that the prediction of the election is assume to be the **first call** to elect. For
//! example, with 3 pages, the prediction must point to the `elect(2)`. Note that this pallet could
//! be configured to always keep itself prepare for an election a number of blocks ahead of time.
//! This will make sure that the data needed for the first call to `elect` is always ready a number
//! of blocks ahead of time, potentially compensating for erronenous predictions.
//!
//! Note that the unsigned phase starts [`pallet::Config::UnsignedPhase`] blocks before the
//! `next_election_prediction`, but only ends when a call to [`ElectionProvider::elect`] happens. If
//! no `elect` happens, the signed phase is extended.
//!
//! > Given this, it is rather important for the user of this pallet to ensure it always terminates
//! election via `elect` before requesting a new one.
//!
//! Each of the phases can be disabled by essentially setting their length to zero. If both phases
//! have length zero, then the pallet essentially runs only the fallback strategy, denoted by
//! [`Config::Fallback`].
//!
//! ## Feasible Solution (correct solution)
//!
//! All submissions must undergo a feasibility check. Signed solutions are checked on by one at the
//! end of the signed phase, and the unsigned solutions are checked on the spot. A feasible solution
//! is as follows:
//!
//! 0. **all** of the used indices must be correct.
//! 1. present *exactly* correct number of winners.
//! 2. any assignment is checked to match with [`RoundSnapshot::voters`].
//! 3. the claimed score is valid, based on the fixed point arithmetic accuracy.
//!
//! ### Signed Phase
//!
//! In the signed phase, solutions (of type [`RawSolution`]) are submitted and queued on chain. A
//! deposit is reserved, based on the size of the solution, for the cost of keeping this solution
//! on-chain for a number of blocks, and the potential weight of the solution upon being checked. A
//! maximum of `pallet::Config::MaxSignedSubmissions` solutions are stored. The queue is always
//! sorted based on score (worse to best).
//!
//! Upon arrival of a new solution:
//!
//! 1. If the queue is not full, it is stored in the appropriate sorted index.
//! 2. If the queue is full but the submitted solution is better than one of the queued ones, the
//!    worse solution is discarded, the bond of the outgoing solution is returned, and the new
//!    solution is stored in the correct index.
//! 3. If the queue is full and the solution is not an improvement compared to any of the queued
//!    ones, it is instantly rejected and no additional bond is reserved.
//!
//! A signed solution cannot be reversed, taken back, updated, or retracted. In other words, the
//! origin can not bail out in any way, if their solution is queued.
//!
//! Upon the end of the signed phase, the solutions are examined from best to worse (i.e. `pop()`ed
//! until drained). Each solution undergoes an expensive `Pallet::feasibility_check`, which ensures
//! the score claimed by this score was correct, and it is valid based on the election data (i.e.
//! votes and candidates). At each step, if the current best solution passes the feasibility check,
//! it is considered to be the best one. The sender of the origin is rewarded, and the rest of the
//! queued solutions get their deposit back and are discarded, without being checked.
//!
//! The following example covers all of the cases at the end of the signed phase:
//!
//! ```ignore
//! Queue
//! +-------------------------------+
//! |Solution(score=20, valid=false)| +-->  Slashed
//! +-------------------------------+
//! |Solution(score=15, valid=true )| +-->  Rewarded, Saved
//! +-------------------------------+
//! |Solution(score=10, valid=true )| +-->  Discarded
//! +-------------------------------+
//! |Solution(score=05, valid=false)| +-->  Discarded
//! +-------------------------------+
//! |             None              |
//! +-------------------------------+
//! ```
//!
//! Note that both of the bottom solutions end up being discarded and get their deposit back,
//! despite one of them being *invalid*.
//!
//! ## Unsigned Phase
//!
//! The unsigned phase will always follow the signed phase, with the specified duration. In this
//! phase, only validator nodes can submit solutions. A validator node who has offchain workers
//! enabled will start to mine a solution in this phase and submits it back to the chain as an
//! unsigned transaction, thus the name _unsigned_ phase. This unsigned transaction can never be
//! valid if propagated, and it acts similar to an inherent.
//!
//! Validators will only submit solutions if the one that they have computed is sufficiently better
//! than the best queued one (see [`pallet::Config::SolutionImprovementThreshold`]) and will limit
//! the weigh of the solution to [`pallet::Config::MinerMaxWeight`].
//!
//! The unsigned phase can be made passive depending on how the previous signed phase went, by
//! setting the first inner value of [`Phase`] to `false`. For now, the signed phase is always
//! active.
//!
//! ### Emergency Phase and Fallback
//!
//! TODO:
//!
//! ## Accuracy
//!
//! TODO
//!
//! ## Error types
//!
//! TODO:
//!
//! ## Future Plans
//!
//! **Challenge Phase**. We plan on adding a third phase to the pallet, called the challenge phase.
//! This is a phase in which no further solutions are processed, and the current best solution might
//! be challenged by anyone (signed or unsigned). The main plan here is to enforce the solution to
//! be PJR. Checking PJR on-chain is quite expensive, yet proving that a solution is **not** PJR is
//! rather cheap. If a queued solution is successfully proven bad:
//!
//! 1. We must surely slash whoever submitted that solution (might be a challenge for unsigned
//!    solutions).
//! 2. We will fallback to the emergency strategy (likely extending the current era).
//!
//! **Bailing out**. The functionality of bailing out of a queued solution is nice. A miner can
//! submit a solution as soon as they _think_ it is high probability feasible, and do the checks
//! afterwards, and remove their solution (for a small cost of probably just transaction fees, or a
//! portion of the bond).
//!
//! **Conditionally open unsigned phase**: Currently, the unsigned phase is always opened. This is
//! useful because an honest validator will run substrate OCW code, which should be good enough to
//! trump a mediocre or malicious signed submission (assuming in the absence of honest signed bots).
//! If there are signed submissions, they can be checked against an absolute measure (e.g. PJR),
//! then we can only open the unsigned phase in extreme conditions (i.e. "no good signed solution
//! received") to spare some work for the active validators.
//!
//! **Allow smaller solutions and build up**: For now we only allow solutions that are exactly
//! [`DesiredTargets`], no more, no less. Over time, we can change this to a [min, max] where any
//! solution within this range is acceptable, where bigger solutions are prioritized.
//!
//! **Score based on (byte) size**: We should always prioritize small solutions over bigger ones, if
//! there is a tie. Even more harsh should be to enforce the bound of the `reduce` algorithm.

// Implementation notes:
//
// - Naming convention is: `${singular}_page` for singular, e.g. `voter_page` for `Vec<Voter>`.
//   `paged_${plural}` for plural, e.g. `paged_voters` for `Vec<Vec<Voter>>`.
//
// - Since this crate has multiple `Pallet` and `Configs`, in each sub-pallet, we only reference the
//   local `Pallet` without a prefix and allow it to be imported via `use`. Avoid `super::Pallet`
//   except for the case of a modules that want to reference their local `Pallet` . The
//   `crate::Pallet` is always reserved for the parent pallet. Other sibling pallets must be
//   referenced with full path, e.g. `crate::Verifier::Pallet`. Do NOT write something like `use
//   unsigned::Pallet as UnsignedPallet`.
//
// - Respecting private storage items with wrapper We move all implementations out of the `mod
//   pallet` as much as possible to ensure we NEVER access the internal storage items directly. All
//   operations should happen with the wrapper types.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_election_provider_support::{
	onchain, BoundedSupportsOf, ElectionDataProvider, ElectionProvider, PageIndex,
};
use frame_support::{
	dispatch::Weight,
	ensure,
	traits::{ConstU32, Get},
	BoundedVec,
};
use sp_arithmetic::traits::Zero;
use sp_npos_elections::VoteWeight;
use sp_runtime::SaturatedConversion;
use sp_std::prelude::*;
use verifier::Verifier;

#[cfg(test)]
mod mock;
#[macro_use]
pub mod helpers;

const LOG_PREFIX: &'static str = "runtime::multiblock-election";

// pub mod signed;
pub mod signed;
pub mod types;
pub mod unsigned;
pub mod verifier;
pub mod weights;

pub use pallet::*;
pub use types::*;
pub use weights::WeightInfo;

/// Configuration for the benchmarks of the pallet.
pub trait BenchmarkingConfig {
	/// Range of voters.
	const VOTERS: [u32; 2];
	/// Range of targets.
	const TARGETS: [u32; 2];
	/// Range of active voters.
	const ACTIVE_VOTERS: [u32; 2];
	/// Range of desired targets.
	const DESIRED_TARGETS: [u32; 2];
	/// Maximum number of voters expected. This is used only for memory-benchmarking of snapshot.
	const SNAPSHOT_MAXIMUM_VOTERS: u32;
	/// Maximum number of voters expected. This is used only for memory-benchmarking of miner.
	const MINER_MAXIMUM_VOTERS: u32;
	/// Maximum number of targets expected. This is used only for memory-benchmarking.
	const MAXIMUM_TARGETS: u32;
}

impl BenchmarkingConfig for () {
	const VOTERS: [u32; 2] = [4000, 6000];
	const TARGETS: [u32; 2] = [1000, 1600];
	const ACTIVE_VOTERS: [u32; 2] = [1000, 3000];
	const DESIRED_TARGETS: [u32; 2] = [400, 800];
	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 10_000;
	const MINER_MAXIMUM_VOTERS: u32 = 10_000;
	const MAXIMUM_TARGETS: u32 = 2_000;
}

/// A fallback implementation that transitions the pallet to the emergency phase.
pub struct InitiateEmergencyPhase<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> ElectionProvider for InitiateEmergencyPhase<T> {
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type DataProvider = T::DataProvider;
	type Error = &'static str;
	type Pages = ConstU32<1>;
	type MaxBackersPerWinner = ();
	type MaxWinnersPerPage = ();

	fn elect(remaining: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		ensure!(remaining == 0, "fallback should only have 1 page");
		log!(warn, "Entering emergency phase.");
		Err("Emergency phase started.")
	}
}

/// Internal errors of the pallet.
///
/// Note that this is different from [`pallet::Error`].
#[derive(frame_support::DebugNoBound)]
pub enum ElectionError<T: Config> {
	/// An error happened in the feasibility check sub-system.
	Feasibility(verifier::FeasibilityError),
	/// An error in the fallback.
	Fallback(FallbackErrorOf<T>),
	/// An error in the onchain seq-phragmen implementation
	OnChain(onchain::Error),
	/// An error happened in the data provider.
	DataProvider(&'static str),
	/// the corresponding page in the queued supports is not available.
	SupportPageNotAvailable,
}

#[cfg(test)]
impl<T: Config> PartialEq for ElectionError<T> {
	fn eq(&self, other: &Self) -> bool {
		matches!(self, other)
	}
}

impl<T: Config> From<onchain::Error> for ElectionError<T> {
	fn from(e: onchain::Error) -> Self {
		ElectionError::OnChain(e)
	}
}

impl<T: Config> From<verifier::FeasibilityError> for ElectionError<T> {
	fn from(e: verifier::FeasibilityError) -> Self {
		ElectionError::Feasibility(e)
	}
}

#[frame_support::pallet]
pub mod pallet {
	use crate::{
		types::*,
		verifier::{self},
		BenchmarkingConfig, WeightInfo,
	};
	use frame_election_provider_support::{
		ElectionDataProvider, ElectionProvider, NposSolution, PageIndex,
	};
	use frame_support::{pallet_prelude::*, Twox64Concat};
	use frame_system::pallet_prelude::*;
	use sp_arithmetic::{traits::CheckedAdd, PerThing, UpperOf};
	use sp_runtime::traits::{Hash, Saturating, Zero};
	use sp_std::convert::TryInto;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::Event>
			+ TryInto<Event<Self>>;

		/// Duration of the unsigned phase.
		#[pallet::constant]
		type UnsignedPhase: Get<Self::BlockNumber>;
		/// Duration of the signed phase.
		#[pallet::constant]
		type SignedPhase: Get<Self::BlockNumber>;
		/// Duration of the singed validation phase.
		///
		/// The duration of this should not be less than `T::Pages`, and there is no point in it
		/// being more than `SignedPhase::MaxSubmission::get() * T::Pages`. TODO: integrity test for
		/// it.
		type SignedValidationPhase: Get<Self::BlockNumber>;

		/// The number of snapshot voters to fetch per block.
		#[pallet::constant]
		type VoterSnapshotPerBlock: Get<u32>;

		/// The number of snapshot targets to fetch per block.
		#[pallet::constant]
		type TargetSnapshotPerBlock: Get<u32>;

		/// The number of pages.
		///
		/// The snapshot is created with this many keys in the storage map.
		///
		/// The solutions may contain at MOST this many pages, but less pages are acceptable as
		/// well.
		#[pallet::constant]
		type Pages: Get<PageIndex>;

		/// Something that will provide the election data.
		type DataProvider: ElectionDataProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
		>;

		/// The solution type.
		type Solution: codec::FullCodec
			+ Default
			+ PartialEq
			+ Eq
			+ Clone
			+ sp_std::fmt::Debug
			+ Ord
			+ NposSolution
			+ TypeInfo
			+ MaxEncodedLen;

		/// The fallback type used for the election.
		///
		/// This type is only used on the last page of the election, therefore it may at most have
		/// 1 pages.
		type Fallback: ElectionProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
			DataProvider = Self::DataProvider,
			Pages = ConstU32<1>,
		>;

		/// The verifier pallet's interface.
		type Verifier: verifier::Verifier<Solution = SolutionOf<Self>, AccountId = Self::AccountId>
			+ verifier::SignedVerifier;

		/// The number of blocks ahead of time to try and have the election results ready by.
		type Lookahead: Get<Self::BlockNumber>;

		/// The configuration of benchmarking.
		type BenchmarkingConfig: BenchmarkingConfig;

		/// The weight of the pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn manage(
			_origin: OriginFor<T>,
			_maybe_force_phase: Option<Phase<T::BlockNumber>>,
			_kill_verifier: bool,
		) -> DispatchResultWithPostInfo {
			// TODO: reset everything, this should only be called in emergencies. Can also be
			// back-ported to master earlier.
			todo!();
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			// first, calculate the main phase switches thresholds.
			let unsigned_deadline = T::UnsignedPhase::get();
			let signed_validation_deadline =
				T::SignedValidationPhase::get().saturating_add(unsigned_deadline);
			let signed_deadline = T::SignedPhase::get().saturating_add(signed_validation_deadline);
			let snapshot_deadline = signed_deadline.saturating_add(T::Pages::get().into());

			let next_election = T::DataProvider::next_election_prediction(now)
				.max(now)
				.saturating_sub(T::Lookahead::get());
			let remaining_blocks = next_election - now;
			let current_phase = Self::current_phase();

			log!(
				trace,
				"current phase {:?}, next election {:?}, metadata: {:?}",
				current_phase,
				next_election,
				Snapshot::<T>::metadata()
			);

			match current_phase {
				// start and continue snapshot.
				Phase::Off
					if remaining_blocks <= snapshot_deadline &&
						remaining_blocks > signed_deadline =>
				{
					let remaining_pages = Self::msp();
					log!(info, "starting snapshot creation, remaining block: {}", remaining_pages);
					let _ = Self::create_targets_snapshot().unwrap();
					let _ = Self::create_voters_snapshot_paged(remaining_pages).unwrap();
					CurrentPhase::<T>::put(Phase::Snapshot(remaining_pages));
					0
				},
				Phase::Snapshot(x) if x > 0 => {
					// we don't check block numbers here, snapshot creation is mandatory.
					let remaining_pages = x.saturating_sub(1);
					log!(info, "continuing voter snapshot creation [{}]", remaining_pages);
					CurrentPhase::<T>::put(Phase::Snapshot(remaining_pages));
					Self::create_voters_snapshot_paged(remaining_pages).unwrap();
					0
				},

				// start signed.
				Phase::Snapshot(0)
					if remaining_blocks <= signed_deadline &&
						remaining_blocks > signed_validation_deadline =>
				{
					// NOTE: if signed-phase length is zero, second part of the if-condition fails.
					// TODO: even though we have the integrity test, what if we open the signed
					// phase, and there's not enough blocks to finalize it? that can happen under
					// any circumstance and we should deal with it.

					// snapshot must be fully created here.
					if cfg!(debug_assertions) {
						Snapshot::<T>::assert_snapshot(true, T::Pages::get());
					}

					<CurrentPhase<T>>::put(Phase::Signed);
					Self::deposit_event(Event::SignedPhaseStarted(Self::round()));
					0
				},

				// start signed verification.
				Phase::Signed
					if remaining_blocks <= signed_validation_deadline &&
						remaining_blocks > unsigned_deadline =>
				{
					// Start verification of the signed stuff.
					<CurrentPhase<T>>::put(Phase::SignedValidation(now));
					Self::deposit_event(Event::SignedValidationPhaseStarted(Self::round()));
					// we don't do anything else here. We expect the signed sub-pallet to handle
					// whatever else needs to be done.
					// TODO: this notification system based on block numbers is 100% based on the
					// on_initialize of the parent pallet is called before the rest of them.
					0
				},

				// start unsigned
				Phase::Signed | Phase::SignedValidation(_) | Phase::Snapshot(0)
					if remaining_blocks <= unsigned_deadline && remaining_blocks > Zero::zero() =>
				{
					<CurrentPhase<T>>::put(Phase::Unsigned((true, now)));
					Self::deposit_event(Event::UnsignedPhaseStarted(Self::round()));
					0
				},
				_ => T::WeightInfo::on_initialize_nothing(),
			}
		}

		fn integrity_test() {
			use sp_std::mem::size_of;
			// The index type of both voters and targets need to be smaller than that of usize (very
			// unlikely to be the case, but anyhow).
			assert!(size_of::<SolutionVoterIndexOf<T>>() <= size_of::<usize>());
			assert!(size_of::<SolutionTargetIndexOf<T>>() <= size_of::<usize>());

			// also, because `VoterSnapshotPerBlock` and `TargetSnapshotPerBlock` are in u32, we
			// assert that both of these types are smaller than u32 as well.
			assert!(size_of::<SolutionVoterIndexOf<T>>() <= size_of::<u32>());
			assert!(size_of::<SolutionTargetIndexOf<T>>() <= size_of::<u32>());

			let pages_bn: T::BlockNumber = T::Pages::get().into();
			// pages must be at least 1.
			assert!(T::Pages::get() > 0);

			// pages + the amount of Lookahead that we expect shall not be more than the length of
			// any phase.
			let lookahead = T::Lookahead::get();
			assert!(pages_bn + lookahead < T::SignedPhase::get());
			assert!(pages_bn + lookahead < T::UnsignedPhase::get());

			// Based on the requirements of [`sp_npos_elections::Assignment::try_normalize`].
			let max_vote: usize = <SolutionOf<T> as NposSolution>::LIMIT;

			// 2. Maximum sum of [SolutionAccuracy; 16] must fit into `UpperOf<OffchainAccuracy>`.
			let maximum_chain_accuracy: Vec<UpperOf<SolutionAccuracyOf<T>>> = (0..max_vote)
				.map(|_| {
					<UpperOf<SolutionAccuracyOf<T>>>::from(
						<SolutionAccuracyOf<T>>::one().deconstruct(),
					)
				})
				.collect();
			let _: UpperOf<SolutionAccuracyOf<T>> = maximum_chain_accuracy
				.iter()
				.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());

			// We only accept data provider who's maximum votes per voter matches our
			// `T::Solution`'s `LIMIT`.
			//
			// NOTE that this pallet does not really need to enforce this in runtime. The
			// solution cannot represent any voters more than `LIMIT` anyhow.
			assert_eq!(
				<T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get(),
				<SolutionOf<T> as NposSolution>::LIMIT as u32,
			);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The signed phase of the given round has started.
		SignedPhaseStarted(u32),
		/// The unsigned validation phase of the given round has started.
		SignedValidationPhaseStarted(u32),
		/// The unsigned phase of the given round has started.
		UnsignedPhaseStarted(u32),
	}

	/// Error of the pallet that can be returned in response to dispatches.
	#[pallet::error]
	pub enum Error<T> {
		/// Submission is too early (or too late, depending on your point of reference).
		EarlySubmission,
		/// The round counter is wrong.
		WrongRound,
		/// Submission is too weak to be considered an improvement.
		WeakSubmission,
		/// Wrong number of pages in the solution.
		WrongPageCount,
		/// Wrong number of winners presented.
		WrongWinnerCount,
		/// The snapshot fingerprint is not a match. The solution is likely outdated.
		WrongFingerprint,
	}

	impl<T: Config> PartialEq for Error<T> {
		fn eq(&self, other: &Self) -> bool {
			use Error::*;
			match (self, other) {
				(EarlySubmission, EarlySubmission) |
				(WrongRound, WrongRound) |
				(WeakSubmission, WeakSubmission) |
				(WrongWinnerCount, WrongWinnerCount) |
				(WrongPageCount, WrongPageCount) => true,
				_ => false,
			}
		}
	}

	/// Internal counter for the number of rounds.
	///
	/// This is useful for de-duplication of transactions submitted to the pool, and general
	/// diagnostics of the pallet.
	///
	/// This is merely incremented once per every time that an upstream `elect` is called.
	#[pallet::storage]
	#[pallet::getter(fn round)]
	pub type Round<T: Config> = StorageValue<_, u32, ValueQuery>;

	/// Current phase.
	#[pallet::storage]
	#[pallet::getter(fn current_phase)]
	pub type CurrentPhase<T: Config> = StorageValue<_, Phase<T::BlockNumber>, ValueQuery>;

	/// Wrapper struct for working with the snapshot.
	pub(crate) struct Snapshot<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> Snapshot<T> {
		// ----------- mutable methods

		pub(crate) fn set_desired_targets(d: u32) {
			DesiredTargets::<T>::put(d);
		}

		pub(crate) fn set_targets(targets: BoundedVec<T::AccountId, T::TargetSnapshotPerBlock>) {
			let hash = Self::write_storage_with_pre_allocate(
				&PagedTargetSnapshot::<T>::hashed_key_for(Pallet::<T>::lsp()),
				targets,
			);
			PagedTargetSnapshotHash::<T>::insert(Pallet::<T>::lsp(), hash);
		}

		pub(crate) fn set_voters(page: PageIndex, voters: VoterPageOf<T>) {
			let hash = Self::write_storage_with_pre_allocate(
				&PagedVoterSnapshot::<T>::hashed_key_for(page),
				voters,
			);
			PagedVoterSnapshotHash::<T>::insert(page, hash);
		}

		pub(crate) fn update_metadata(
			maybe_new_voters: Option<u32>,
			maybe_new_targets: Option<u32>,
		) {
			if maybe_new_targets.is_none() && maybe_new_voters.is_none() {
				return
			}

			SnapshotMetadata::<T>::mutate(|maybe_metadata| {
				let mut metadata = maybe_metadata.unwrap_or_default();
				if let Some(new_voters) = maybe_new_voters {
					metadata.voters = metadata.voters.saturating_add(new_voters);
				}
				if let Some(new_targets) = maybe_new_targets {
					metadata.targets = metadata.targets.saturating_add(new_targets);
				}
				*maybe_metadata = Some(metadata);
			});
		}

		/// Destroy the entire snapshot.
		///
		/// Should be called only once we transition to [`Phase::Off`].
		pub(crate) fn kill() {
			DesiredTargets::<T>::kill();
			SnapshotMetadata::<T>::kill();
			PagedVoterSnapshot::<T>::remove_all(None);
			PagedVoterSnapshotHash::<T>::remove_all(None);
			PagedTargetSnapshot::<T>::remove_all(None);
			PagedTargetSnapshotHash::<T>::remove_all(None);
		}

		// ----------- non-mutables
		pub(crate) fn desired_targets() -> Option<u32> {
			DesiredTargets::<T>::get()
		}

		pub(crate) fn voters(page: PageIndex) -> Option<VoterPageOf<T>> {
			PagedVoterSnapshot::<T>::get(page)
		}

		pub(crate) fn voters_hash(page: PageIndex) -> Option<T::Hash> {
			PagedVoterSnapshotHash::<T>::get(page)
		}

		pub(crate) fn voters_decode_len(page: PageIndex) -> Option<usize> {
			PagedVoterSnapshot::<T>::decode_len(page)
		}

		pub(crate) fn targets_decode_len() -> Option<usize> {
			PagedVoterSnapshot::<T>::decode_len(Pallet::<T>::msp())
		}

		pub(crate) fn targets() -> Option<BoundedVec<T::AccountId, T::TargetSnapshotPerBlock>> {
			// NOTE: targets always have one index, which is 0, aka lsp.
			PagedTargetSnapshot::<T>::get(Pallet::<T>::lsp())
		}

		pub(crate) fn targets_hash() -> Option<T::Hash> {
			PagedTargetSnapshotHash::<T>::get(Pallet::<T>::lsp())
		}

		pub(crate) fn metadata() -> Option<SolutionOrSnapshotSize> {
			SnapshotMetadata::<T>::get()
		}

		/// Get a fingerprint of the snapshot, from all the hashes that are stored for each page of
		/// the snapshot.
		///
		/// This is computed as: `(target_hash, voter_hash_n, voter_hash_(n-1), ..., voter_hash_0)`
		/// where `n` is `T::Pages - 1`. In other words, it is the concatenated hash of targets, and
		/// voters, from `msp` to `lsp`.
		pub fn fingerprint() -> T::Hash {
			let mut targets = PagedTargetSnapshotHash::<T>::get(Pallet::<T>::lsp())
				.unwrap_or_default()
				.as_ref()
				.to_vec();
			let voters = (Pallet::<T>::msp()..=Pallet::<T>::lsp())
				.map(|i| PagedVoterSnapshotHash::<T>::get(i).unwrap_or_default())
				.map(|hash| <T::Hash as AsRef<[u8]>>::as_ref(&hash).to_owned())
				.flatten()
				.collect::<Vec<u8>>();
			targets.extend(voters);
			T::Hashing::hash(&targets)
		}

		fn write_storage_with_pre_allocate<E: Encode>(key: &[u8], data: E) -> T::Hash {
			let size = data.encoded_size();
			let mut buffer = Vec::with_capacity(size);
			data.encode_to(&mut buffer);

			let hash = T::Hashing::hash(&buffer);

			// do some checks.
			debug_assert_eq!(buffer, data.encode());
			// buffer should have not re-allocated since.
			debug_assert!(buffer.len() == size && size == buffer.capacity());
			sp_io::storage::set(key, &buffer);

			hash
		}

		#[cfg(any(test, debug_assertions))]
		pub(crate) fn assert_snapshot(exists: bool, up_to_page: PageIndex) {
			assert!(up_to_page > 0, "can't check snapshot up to page 0");

			assert!(
				exists ^ !Self::desired_targets().is_some(),
				"desired target snapshot mismatch: phase: {:?}, exists: {}",
				Pallet::<T>::current_phase(),
				exists,
			);
			assert!(exists ^ !Self::metadata().is_some(), "metadata mismatch");
			assert!(exists ^ !Self::targets().is_some(), "targets mismatch");
			assert!(exists ^ !Self::targets_hash().is_some(), "targets hash mismatch");

			(crate::Pallet::<T>::msp()..=crate::Pallet::<T>::lsp())
				.take(up_to_page as usize)
				.for_each(|p| {
					assert!(
						(exists ^ !Self::voters(p).is_some()) &&
							(exists ^ !Self::voters_hash(p).is_some()),
						"voter page {} mismatch {}",
						p,
						exists
					);
				});
		}
	}

	#[cfg(test)]
	impl<T: Config> Snapshot<T> {
		pub fn voter_pages() -> PageIndex {
			use sp_runtime::SaturatedConversion;
			PagedVoterSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub fn target_pages() -> PageIndex {
			use sp_runtime::SaturatedConversion;
			PagedTargetSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub fn voters_iter(
		) -> impl Iterator<Item = (PageIndex, BoundedVec<VoterOf<T>, T::VoterSnapshotPerBlock>)> {
			PagedVoterSnapshot::<T>::iter()
		}

		pub fn voters_iter_flattened() -> impl Iterator<Item = VoterOf<T>> {
			let key_range =
				(crate::Pallet::<T>::lsp()..=crate::Pallet::<T>::msp()).collect::<Vec<_>>();
			key_range
				.into_iter()
				.map(|k| PagedVoterSnapshot::<T>::get(k).unwrap_or_default())
				.flatten()
		}

		pub fn remove_voter_page(page: PageIndex) {
			PagedVoterSnapshot::<T>::remove(page);
		}

		pub fn kill_desired_targets() {
			DesiredTargets::<T>::kill();
		}

		pub fn remove_target_page(page: PageIndex) {
			PagedTargetSnapshot::<T>::remove(page);
		}

		pub fn remove_target(at: usize) {
			PagedTargetSnapshot::<T>::mutate(crate::Pallet::<T>::lsp(), |maybe_targets| {
				if let Some(targets) = maybe_targets {
					targets.remove(at);
					// and update the hash.
					PagedTargetSnapshotHash::<T>::insert(
						crate::Pallet::<T>::lsp(),
						T::Hashing::hash(&targets.encode()),
					)
				}
			})
		}
	}

	/// The metadata of the [`RoundSnapshot`]
	#[pallet::storage]
	type SnapshotMetadata<T: Config> = StorageValue<_, SolutionOrSnapshotSize>;

	/// Desired number of targets to elect for this round.
	#[pallet::storage]
	type DesiredTargets<T> = StorageValue<_, u32>;

	/// Paginated voter snapshot. At most [`T::Pages`] keys will exist.
	#[pallet::storage]
	type PagedVoterSnapshot<T: Config> = StorageMap<_, Twox64Concat, PageIndex, VoterPageOf<T>>;

	/// Same as [`PagedVoterSnapshot`], but it will store the hash of the snapshot.
	///
	/// The hash is generated using [`frame_system::Config::Hashing`].
	#[pallet::storage]
	type PagedVoterSnapshotHash<T: Config> = StorageMap<_, Twox64Concat, PageIndex, T::Hash>;

	/// Paginated target snapshot.
	///
	/// For the time being, since we assume one pages of targets, at most ONE key will exist.
	#[pallet::storage]
	type PagedTargetSnapshot<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, BoundedVec<T::AccountId, T::TargetSnapshotPerBlock>>;

	/// Same as [`PagedTargetSnapshot`], but it will store the hash of the snapshot.
	///
	/// The hash is generated using [`frame_system::Config::Hashing`].
	#[pallet::storage]
	type PagedTargetSnapshotHash<T: Config> = StorageMap<_, Twox64Concat, PageIndex, T::Hash>;

	#[pallet::pallet]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	/// Returns the most significant page of the snapshot.
	///
	/// Based on the contract of `ElectionDataProvider`, this is the first page that is filled.
	fn msp() -> PageIndex {
		T::Pages::get().checked_sub(1).unwrap_or_else(|| {
			// TODO: Defensive Trait.
			debug_assert!(false, "Integrity check must ensure that T::Pages is greater than 1");
			log!(warn, "Integrity check must ensure that T::Pages is greater than 1");
			Default::default()
		})
	}

	/// Returns the least significant page of the snapshot.
	///
	/// Based on the contract of `ElectionDataProvider`, this is the last page that is filled.
	fn lsp() -> PageIndex {
		Zero::zero()
	}

	/// Perform all the basic checks that are independent of the snapshot. TO be more specific,
	/// these are all the checks that you can do without the need to read the massive blob of the
	/// actual snapshot. This function only contains a handful of storage reads, with bounded size.
	///
	/// A sneaky detail is that this does check the `DesiredTargets` aspect of the snapshot, but
	/// neither of the large storage items.
	///
	/// Moreover, we do optionally check the fingerprint of the snapshot, if provided.
	///
	/// These compliment a feasibility-check, which is exactly the opposite: snapshot-dependent
	/// checks.
	pub(crate) fn snapshot_independent_checks(
		paged_solution: &PagedRawSolution<T>,
		maybe_snapshot_fingerprint: Option<T::Hash>,
	) -> Result<(), Error<T>> {
		// Note that the order of these checks are critical for the correctness and performance of
		// `restore_or_compute_then_maybe_submit`. We want to make sure that we always check round
		// first, so that if it has a wrong round, we can detect and delete it from the cache right
		// from the get go.

		// ensure round is current
		ensure!(Self::round() == paged_solution.round, Error::<T>::WrongRound);

		// ensure score is being improved, if the claim is even correct.
		ensure!(
			<T::Verifier as Verifier>::ensure_claimed_score_improves(paged_solution.score),
			Error::<T>::WeakSubmission,
		);

		// ensure solution pages are no more than the snapshot
		ensure!(
			paged_solution.solution_pages.len().saturated_into::<PageIndex>() <= T::Pages::get(),
			Error::<T>::WrongPageCount
		);

		// finally, check the winner count being correct.
		if let Some(desired_targets) = Snapshot::<T>::desired_targets() {
			ensure!(
				desired_targets == paged_solution.winner_count_single_page_target_snapshot() as u32,
				Error::<T>::WrongWinnerCount
			)
		}

		// check the snapshot fingerprint, if asked for.
		ensure!(
			maybe_snapshot_fingerprint
				.map_or(true, |snapshot_fingerprint| Snapshot::<T>::fingerprint() ==
					snapshot_fingerprint),
			Error::<T>::WrongFingerprint
		);

		Ok(())
	}

	/// Creates the target snapshot. Writes new data to:
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_targets_snapshot() -> Result<u32, ElectionError<T>> {
		// if requested, get the targets as well.
		Snapshot::<T>::set_desired_targets(
			T::DataProvider::desired_targets().map_err(ElectionError::DataProvider)?,
		);

		let limit = Some(T::TargetSnapshotPerBlock::get().saturated_into::<usize>());
		let targets: BoundedVec<_, T::TargetSnapshotPerBlock> = T::DataProvider::targets(limit, 0)
			.and_then(|v| v.try_into().map_err(|_| "try-into failed"))
			.map_err(ElectionError::DataProvider)?;

		let count = targets.len() as u32;
		Snapshot::<T>::set_targets(targets);
		Snapshot::<T>::update_metadata(None, Some(count));
		log!(debug, "created target snapshot with {} targets.", count);

		Ok(count)
	}

	/// Creates the voter snapshot. Writes new data to:
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_voters_snapshot_paged(remaining: PageIndex) -> Result<u32, ElectionError<T>> {
		let limit = Some(T::VoterSnapshotPerBlock::get().saturated_into::<usize>());
		let voters: BoundedVec<_, T::VoterSnapshotPerBlock> =
			T::DataProvider::voters(limit, remaining)
				.and_then(|v| v.try_into().map_err(|_| "try-into failed"))
				.map_err(ElectionError::DataProvider)?;

		let count = voters.len() as u32;
		Snapshot::<T>::set_voters(remaining, voters);
		Snapshot::<T>::update_metadata(Some(count), None);
		log!(debug, "created voter snapshot with {} voters, {} remaining.", count, remaining);

		Ok(count)
	}

	/// Perform the tasks to be done after a new `elect` has been triggered:
	///
	/// 1. Increment round.
	/// 2. Change phase to [`Phase::Off`]
	/// 3. Clear all snapshot data.
	fn rotate_round() {
		// Inc round.
		<Round<T>>::mutate(|r| *r += 1);

		// Phase is off now.
		<CurrentPhase<T>>::put(Phase::Off);

		// Kill everything in the verifier.
		T::Verifier::kill();

		// Kill the snapshot.
		Snapshot::<T>::kill();
	}

	#[cfg(test)]
	pub(crate) fn sanity_check() -> Result<(), &'static str> {
		match Self::current_phase() {
			Phase::Off => Snapshot::<T>::assert_snapshot(false, T::Pages::get()),
			Phase::Signed | Phase::Unsigned(_) =>
				Snapshot::<T>::assert_snapshot(true, T::Pages::get()),
			_ => (),
		};

		Ok(())
	}
}

impl<T: Config> ElectionProvider for Pallet<T>
where
	T::Fallback: ElectionProvider<
		AccountId = T::AccountId,
		BlockNumber = T::BlockNumber,
		MaxBackersPerWinner = <T::Verifier as Verifier>::MaxBackersPerWinner,
		MaxWinnersPerPage = <T::Verifier as Verifier>::MaxWinnersPerPage,
	>,
{
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Error = ElectionError<T>;
	type DataProvider = T::DataProvider;
	type Pages = T::Pages;
	type MaxWinnersPerPage = <T::Verifier as Verifier>::MaxWinnersPerPage;
	type MaxBackersPerWinner = <T::Verifier as Verifier>::MaxBackersPerWinner;

	fn elect(remaining: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		T::Verifier::get_queued_solution_page(remaining)
			.ok_or(ElectionError::SupportPageNotAvailable)
			.or_else(|err| {
				// if this is the last page, we might use the fallback to recover something.
				log!(error, "primary election provider failed due to: {:?}, trying fallback", err);
				if remaining.is_zero() {
					T::Fallback::elect(0).map_err(|fe| ElectionError::<T>::Fallback(fe))
				} else {
					Err(err)
				}
			})
			.map(|supports| {
				// if either of `Verifier` or `Fallback` was okay, and if this is the last page,
				// then clear everything.
				if remaining.is_zero() {
					log!(info, "receiving last call to elect(0), rotating round");
					Self::rotate_round()
				} else {
					<CurrentPhase<T>>::put(Phase::Export);
				}
				supports.into()
			})
			.map_err(|err| {
				// if any pages returns an error, we go into the emergency phase and don't do
				// anything else anymore. This will prevent any new submissions to signed and
				// unsigned pallet, and thus the verifier will also be almost stuck, except for the
				// submission of emergency solutions.
				log!(error, "fetching page {} failed. entering emergency mode.", remaining);
				<CurrentPhase<T>>::put(Phase::Emergency);
				err
			})
	}
}

#[cfg(test)]
mod phase_rotation {
	use super::{Event, *};
	use crate::{mock::*, Phase};
	use frame_election_provider_support::ElectionProvider;

	#[test]
	fn single_page() {
		ExtBuilder::full().pages(1).onchain_fallback(true).build_and_execute(|| {
			// 0 -------- 14 15 --------- 20 ------------- 25 ---------- 30
			//            |  |            |                |             |
			//    Snapshot Signed  SignedValidation    Unsigned       elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 1);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
			Snapshot::<Runtime>::assert_snapshot(true, 1);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 1);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			Snapshot::<Runtime>::assert_snapshot(true, 1);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			MultiBlock::elect(0).unwrap();

			assert!(MultiBlock::current_phase().is_off());
			Snapshot::<Runtime>::assert_snapshot(false, 1);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(43);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(44);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(45);
			assert!(MultiBlock::current_phase().is_signed());

			roll_to(50);
			assert!(MultiBlock::current_phase().is_signed_validation_open_at(50));

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn multi_page_2() {
		ExtBuilder::full().pages(2).onchain_fallback(true).build_and_execute(|| {
			// 0 -------13 14 15 ------- 20 ---- 25 ------- 30
			//           |     |         |       |          |
			//    Snapshot    Signed SigValid  Unsigned   Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(12);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(29);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			MultiBlock::elect(0).unwrap(); // and even this one's coming from the fallback.
			assert!(MultiBlock::current_phase().is_off());

			// all snapshots are gone.
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(42);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(43);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));

			roll_to(44);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(45);
			assert!(MultiBlock::current_phase().is_signed());

			roll_to(50);
			assert!(MultiBlock::current_phase().is_signed_validation_open_at(50));

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn multi_page_3() {
		ExtBuilder::full().pages(3).onchain_fallback(true).build_and_execute(|| {
			#[rustfmt::skip]
	 		// 0 ------- 12 13 14 15 ----------- 20 ---------25 ------- 30
			//            |       |              |            |          |
	 		//     Snapshot      Signed   SignedValidation  Unsigned   Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(11);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(12);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));
			Snapshot::<Runtime>::assert_snapshot(true, 3);

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
			Snapshot::<Runtime>::assert_snapshot(true, 3);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 2);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 3);

			roll_to(29);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 3);

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			Snapshot::<Runtime>::assert_snapshot(true, 3);

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			MultiBlock::elect(0).unwrap();
			assert!(MultiBlock::current_phase().is_off());

			// all snapshots are gone.
			Snapshot::<Runtime>::assert_snapshot(false, 3);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(41);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(42);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));

			roll_to(43);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));

			roll_to(44);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(45);
			assert!(MultiBlock::current_phase().is_signed());

			roll_to(50);
			assert!(MultiBlock::current_phase().is_signed_validation_open_at(50));

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn multi_with_lookahead() {
		todo!();
	}

	#[test]
	fn no_unsigned_phase() {
		todo!()
	}

	#[test]
	fn no_signed_phase() {
		todo!()
	}

	#[test]
	fn no_any_phase() {
		todo!()
	}

	#[test]
	fn incorrect_signed_validation_phase() {
		todo!()
	}
}

#[cfg(test)]
mod election_provider {
	use super::*;
	use crate::{mock::*, unsigned::miner::BaseMiner, verifier::Verifier, Phase};
	use frame_election_provider_support::ElectionProvider;
	use frame_support::assert_storage_noop;

	#[test]
	fn multi_page_elect_simple_works() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();
			let score = paged.score.clone();

			// now let's submit this one by one, into the signed phase.
			load_signed_for_verification(99, paged);

			// now the solution should start being verified.
			roll_to_signed_validation_open();
			assert_eq!(
				multi_block_events(),
				vec![
					crate::Event::SignedPhaseStarted(0),
					crate::Event::SignedValidationPhaseStarted(0)
				]
			);
			assert_eq!(verifier_events(), vec![]);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// proceed until it is fully verified.
			roll_next();
			assert_eq!(verifier_events(), vec![verifier::Event::Verified(2, 2)]);

			roll_next();
			assert_eq!(
				verifier_events(),
				vec![verifier::Event::Verified(2, 2), verifier::Event::Verified(1, 2)]
			);

			roll_next();
			assert_eq!(
				verifier_events(),
				vec![
					verifier::Event::Verified(2, 2),
					verifier::Event::Verified(1, 2),
					verifier::Event::Verified(0, 2),
					verifier::Event::Queued([55, 130, 8650], None),
				]
			);

			// there is now a queued solution.
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// now let's go to unsigned phase, but we don't expect anything to happen there since we
			// don't run OCWs.
			roll_to_unsigned_open();

			// pre-elect state
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 0);
			ensure_full_snapshot();

			// call elect for each page
			let _paged_solution = (MultiBlock::lsp()..MultiBlock::msp())
				.rev() // 2, 1, 0
				.map(|page| {
					MultiBlock::elect(page as PageIndex).unwrap();
					if page == 0 {
						assert!(MultiBlock::current_phase().is_off())
					} else {
						assert!(MultiBlock::current_phase().is_export())
					}
				})
				.collect::<Vec<_>>();

			// after the last elect, verifier is cleared,
			verifier::QueuedSolution::<Runtime>::ensure_killed();
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 1);
			// and the snapshot is cleared,
			assert_storage_noop!(Snapshot::<Runtime>::kill());
			// signed pallet is clean.
			// NOTE: in the future, if and when we add lazy cleanup to the signed pallet, this
			// assertion might break.
			signed::Submissions::<Runtime>::ensure_killed();
		});
	}

	#[test]
	fn multi_page_elect_fast_track() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();
			let score = paged.score.clone();
			load_signed_for_verification_and_start(99, paged, 0);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// roll to the block it is finalized
			roll_next();
			roll_next();
			roll_next();
			assert_eq!(
				verifier_events(),
				vec![
					verifier::Event::Verified(2, 2),
					verifier::Event::Verified(1, 2),
					verifier::Event::Verified(0, 2),
					verifier::Event::Queued([55, 130, 8650], None),
				]
			);

			// there is now a queued solution.
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// not much impact, just for the sane-ness of the test.
			roll_to_unsigned_open();

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 0);
			ensure_full_snapshot();

			// there are 3 pages (indexes 2..=0), but we short circuit by just calling 0.
			let _solution = crate::Pallet::<Runtime>::elect(0).unwrap();

			// after elect(0) is called, verifier is cleared,
			verifier::QueuedSolution::<Runtime>::ensure_killed();
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 1);
			// the snapshot is cleared,
			assert_storage_noop!(Snapshot::<Runtime>::kill());
			// and signed pallet is clean.
			signed::Submissions::<Runtime>::ensure_killed();
		});
	}

	#[test]
	fn elect_does_not_finish_without_call_of_page_0() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();
			let score = paged.score.clone();
			load_signed_for_verification_and_start(99, paged, 0);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// roll to the block it is finalized
			roll_next();
			roll_next();
			roll_next();
			assert_eq!(
				verifier_events(),
				vec![
					verifier::Event::Verified(2, 2),
					verifier::Event::Verified(1, 2),
					verifier::Event::Verified(0, 2),
					verifier::Event::Queued([55, 130, 8650], None),
				]
			);

			// there is now a queued solution
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// not much impact, just for the sane-ness of the test.
			roll_to_unsigned_open();

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 0);
			ensure_full_snapshot();

			// call elect for page 2 and 1, but NOT 0
			let solutions = (1..=MultiBlock::msp())
				.rev() // 2, 1
				.map(|page| {
					crate::Pallet::<Runtime>::elect(page as PageIndex).unwrap();
					assert!(MultiBlock::current_phase().is_export());
				})
				.collect::<Vec<_>>();
			assert_eq!(solutions.len(), 2);

			// nothing changes from the prelect state, except phase is now export.
			assert!(MultiBlock::current_phase().is_export());
			assert_eq!(Round::<Runtime>::get(), 0);
			ensure_full_snapshot();
		});
	}

	#[test]
	fn when_passive_stay_in_phase_unsigned() {
		ExtBuilder::full().build_and_execute(|| {
			// once the unsigned phase starts, it will not be changed by on_initialize (something
			// like `elect` must be called).
			roll_to_unsigned_open();
			for next in 0..100 {
				roll_next();
				assert!(matches!(MultiBlock::current_phase(), Phase::Unsigned((_, _))));
			}
		});
	}

	#[test]
	fn skip_unsigned_phase() {
		todo!("first call to elect comes before the start of the unsigned phase")
	}

	#[test]
	fn call_to_elect_should_prevent_any_submission() {
		todo!("once first call to elect comes, we shall go into a new phase where everything else should be over");
	}

	#[test]
	fn force_clear() {
		todo!("something very similar to the scenario of elect_does_not_finish_without_call_of_page_0, where we want to forcefully clear and put everything into halt phase")
	}

	#[test]
	fn multi_page_elect_fallback_works() {
		todo!()
	}
}

#[cfg(test)]
mod snapshot {
	use super::*;

	#[test]
	fn fetches_exact_voters() {
		todo!("fetches correct number of voters, based on T::VoterSnapshotPerBlock");
	}

	#[test]
	fn fetches_exact_targets() {
		todo!("fetches correct number of targets, based on T::TargetSnapshotPerBlock");
	}

	#[test]
	fn fingerprint_works() {
		todo!("one hardcoded test of the fingerprint value.");
	}
}

// #[cfg(test)]
// mod tests {

// 	#[test]
// 	fn early_termination() {
// 		// An early termination in the signed phase, with no queued solution.
// 		ExtBuilder::default().build_and_execute(|| {
// 			// Signed phase started at block 15 and will end at 25.
// 			roll_to(14);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			roll_to(15);
// 			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
// 			assert_eq!(MultiBlock::round(), 1);

// 			// An unexpected call to elect.
// 			roll_to(20);
// 			MultiBlock::elect().unwrap();

// 			// We surely can't have any feasible solutions. This will cause an on-chain election.
// 			assert_eq!(
// 				multi_block_events(),
// 				vec![
// 					Event::SignedPhaseStarted(1),
// 					Event::ElectionFinalized(Some(ElectionCompute::OnChain))
// 				],
// 			);
// 			// All storage items must be cleared.
// 			assert_eq!(MultiBlock::round(), 2);
// 			assert!(MultiBlock::snapshot().is_none());
// 			assert!(MultiBlock::snapshot_metadata().is_none());
// 			assert!(MultiBlock::desired_targets().is_none());
// 			assert!(MultiBlock::queued_solution().is_none());
// 			assert!(MultiBlock::signed_submissions().is_empty());
// 		})
// 	}

// 	#[test]
// 	fn early_termination_with_submissions() {
// 		// an early termination in the signed phase, with no queued solution.
// 		ExtBuilder::default().build_and_execute(|| {
// 			// signed phase started at block 15 and will end at 25.
// 			roll_to(14);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			roll_to(15);
// 			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
// 			assert_eq!(MultiBlock::round(), 1);

// 			// fill the queue with signed submissions
// 			for s in 0..SignedMaxSubmissions::get() {
// 				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
// 				assert_ok!(MultiBlock::submit(
// 					crate::mock::Origin::signed(99),
// 					Box::new(solution),
// 					MultiBlock::signed_submissions().len() as u32
// 				));
// 			}

// 			// an unexpected call to elect.
// 			roll_to(20);
// 			assert!(MultiBlock::elect().is_ok());

// 			// all storage items must be cleared.
// 			assert_eq!(MultiBlock::round(), 2);
// 			assert!(MultiBlock::snapshot().is_none());
// 			assert!(MultiBlock::snapshot_metadata().is_none());
// 			assert!(MultiBlock::desired_targets().is_none());
// 			assert!(MultiBlock::queued_solution().is_none());
// 			assert!(MultiBlock::signed_submissions().is_empty());
// 		})
// 	}

// 	#[test]
// 	fn fallback_strategy_works() {
// 		ExtBuilder::default().fallback(FallbackStrategy::OnChain).build_and_execute(|| {
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

// 			roll_to(25);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

// 			// Zilch solutions thus far.
// 			let (supports, _) = MultiBlock::elect().unwrap();

// 			assert_eq!(
// 				supports,
// 				vec![
// 					(30, Support { total: 40, voters: vec![(2, 5), (4, 5), (30, 30)] }),
// 					(40, Support { total: 60, voters: vec![(2, 5), (3, 10), (4, 5), (40, 40)] })
// 				]
// 			)
// 		});

// 		ExtBuilder::default().fallback(FallbackStrategy::Nothing).build_and_execute(|| {
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

// 			roll_to(25);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

// 			// Zilch solutions thus far.
// 			assert_eq!(MultiBlock::elect().unwrap_err(), ElectionError::NoFallbackConfigured);
// 		})
// 	}

// 	#[test]
// 	fn snapshot_too_big_failure_onchain_fallback() {
// 		// the `MockStaking` is designed such that if it has too many targets, it simply fails.
// 		ExtBuilder::default().build_and_execute(|| {
// 			Targets::set((0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>());

// 			// Signed phase failed to open.
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			// Unsigned phase failed to open.
// 			roll_to(25);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			// On-chain backup works though.
// 			roll_to(29);
// 			let (supports, _) = MultiBlock::elect().unwrap();
// 			assert!(supports.len() > 0);
// 		});
// 	}

// 	#[test]
// 	fn snapshot_too_big_failure_no_fallback() {
// 		// and if the backup mode is nothing, we go into the emergency mode..
// 		ExtBuilder::default().fallback(FallbackStrategy::Nothing).build_and_execute(|| {
// 			crate::mock::Targets::set(
// 				(0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>(),
// 			);

// 			// Signed phase failed to open.
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			// Unsigned phase failed to open.
// 			roll_to(25);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Off);

// 			roll_to(29);
// 			let err = MultiBlock::elect().unwrap_err();
// 			assert_eq!(err, ElectionError::NoFallbackConfigured);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Emergency);
// 		});
// 	}

// 	#[test]
// 	fn snapshot_too_big_truncate() {
// 		// but if there are too many voters, we simply truncate them.
// 		ExtBuilder::default().build_and_execute(|| {
// 			// we have 8 voters in total.
// 			assert_eq!(crate::mock::Voters::get().len(), 8);
// 			// but we want to take 4.
// 			crate::mock::VoterSnapshotPerBlock::set(2);

// 			// Signed phase opens just fine.
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

// 			assert_eq!(
// 				MultiBlock::snapshot_metadata().unwrap(),
// 				SolutionOrSnapshotSize { voters: 2, targets: 4 }
// 			);
// 		})
// 	}

// 	#[test]
// 	fn untrusted_score_verification_is_respected() {
// 		ExtBuilder::default().build_and_execute(|| {
// 			roll_to(15);
// 			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

// 			let (solution, _) = MultiBlock::mine_solution(2, falase).unwrap();
// 			// Default solution has a score of [50, 100, 5000].
// 			assert_eq!(solution.score, [50, 100, 5000]);

// 			<MinimumUntrustedScore<Runtime>>::put([49, 0, 0]);
// 			assert_ok!(MultiBlock::feasibility_check(solution.clone(), ElectionCompute::Signed));

// 			<MinimumUntrustedScore<Runtime>>::put([51, 0, 0]);
// 			assert_noop!(
// 				MultiBlock::feasibility_check(solution, ElectionCompute::Signed),
// 				FeasibilityError::UntrustedScoreTooLow,
// 			);
// 		})
// 	}

// 	#[test]
// 	fn number_of_voters_allowed_2sec_block() {
// 		// Just a rough estimate with the substrate weights.
// 		assert!(!MockWeightInfo::get());

// 		let all_voters: u32 = 10_000;
// 		let all_targets: u32 = 5_000;
// 		let desired: u32 = 1_000;
// 		let weight_with = |active| {
// 			<Runtime as Config>::WeightInfo::submit_unsigned(
// 				all_voters,
// 				all_targets,
// 				active,
// 				desired,
// 			)
// 		};

// 		let mut active = 1;
// 		while weight_with(active) <=
// 			<Runtime as frame_system::Config>::BlockWeights::get().max_block ||
// 			active == all_voters
// 		{
// 			active += 1;
// 		}

// 		println!("can support {} voters to yield a weight of {}", active, weight_with(active));
// 	}
// }
