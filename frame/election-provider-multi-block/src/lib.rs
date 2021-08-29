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
//! computed offchain (anywhere) and submitted back to the chain as signed or unsigned transaction,
//! with sensible configurations and fail-safe mechanisms to ensure system safety. Nonetheless, it
//! has a limited capacity in terms of number of voters it can process in a single block.
//!
//! This pallet takes [`pallet_election_provider_multi_phase`], keeps most of ides core premises,
//! and extends it to support paginated, multi-block operations. The final goal of this pallet is
//! scale linearly with the number of blocks allocated to the elections. In principle, with large
//! enough blocks (in a dedicated parachain), the number of voters included in the NPoS system can
//! grow significantly (yet, obviously not indefinitely).
//!
//! ## Companion pallets
//!
//! This pallet will only function in a sensible way if it is peered with its companion pallets.
//!
//! - The [`verifier`] module provides a standard implementation of the [`verifier::Verifier`]. This
//!   pallet is mandatory.
//! - The [`unsigned`] module provides the implementation of unsigned submission by validators. If
//!   this pallet is included, then [`Config::UnsignedPhase`] will determine its duration.
//! - TODO: signed phase
//! - TODO: emergency phase.
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
//! until drained). Each solution undergoes an expensive `Pallet::feasibility_check`, which
//! ensures the score claimed by this score was correct, and it is valid based on the election data
//! (i.e. votes and candidates). At each step, if the current best solution passes the feasibility
//! check, it is considered to be the best one. The sender of the origin is rewarded, and the rest
//! of the queued solutions get their deposit back and are discarded, without being checked.
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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_election_provider_support::{onchain, ElectionDataProvider, ElectionProvider, PageIndex};
use frame_support::{
	ensure,
	traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
	weights::Weight,
};
use sp_arithmetic::{
	traits::{CheckedAdd, Saturating, Zero},
	UpperOf,
};
use sp_npos_elections::{NposSolution, VoteWeight};
use sp_runtime::{traits::Bounded, PerThing, SaturatedConversion};
use sp_std::{convert::TryInto, prelude::*};
use verifier::Verifier;

#[cfg(test)]
mod mock;
#[macro_use]
pub mod helpers;

const LOG_TARGET: &'static str = "runtime::multiblock-election";

// pub mod signed;
pub mod fixed_vec;
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
// TODO: backport this to the original pallet.
pub struct InitiateEmergencyPhase<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for InitiateEmergencyPhase<T> {
	type DataProvider = T::DataProvider;
	type Error = &'static str;

	fn elect(remaining: PageIndex) -> Result<Supports<T::AccountId>, Self::Error> {
		ensure!(remaining == 0, "fallback should only have 1 page");
		log!(warn, "Entering emergency phase.");
		CurrentPhase::<T>::put(Phase::Emergency);
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
	/// An error in the miner (offchain) sub-system.
	Miner(unsigned::miner::MinerError),
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

impl<T: Config> From<unsigned::miner::MinerError> for ElectionError<T> {
	fn from(e: unsigned::miner::MinerError) -> Self {
		ElectionError::Miner(e)
	}
}

#[frame_support::pallet]
pub mod pallet {
	use std::fmt::Result;

	use crate::{types::*, verifier, BenchmarkingConfig, WeightInfo};
	use frame_election_provider_support::{
		ElectionDataProvider, ElectionProvider, NposSolution, PageIndex,
	};
	use frame_support::{
		pallet_prelude::*, traits::EstimateCallFee, IterableStorageDoubleMap, Twox64Concat,
	};
	use frame_system::pallet_prelude::*;
	use sp_arithmetic::{traits::CheckedAdd, PerThing, UpperOf};
	use sp_runtime::traits::{One, SaturatedConversion, Saturating, Zero};
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

		/// The number of snapshot voters to fetch per block.
		///
		/// In the future, this value will make more sense with multi-block snapshot.
		///
		/// Also, note the data type: If the voters are represented by a `u32` in `type
		/// CompactSolution`, the same `u32` is used here to ensure bounds are respected.
		#[pallet::constant]
		type VoterSnapshotPerBlock: Get<SolutionVoterIndexOf<Self>>;

		/// The number of pages.
		///
		/// The snapshot is created with this many keys in the storage map.
		///
		/// The solutions may contain at MOST this many pages, but less pages are acceptable as
		/// well.
		#[pallet::constant]
		type Pages: Get<PageIndex>;

		/// Something that will provide the election data.
		type DataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;

		/// The solution type.
		type Solution: codec::FullCodec
			+ Default
			+ PartialEq
			+ Eq
			+ Clone
			+ sp_std::fmt::Debug
			+ Ord
			+ NposSolution;

		type Fallback: ElectionProvider<
			Self::AccountId,
			Self::BlockNumber,
			DataProvider = Self::DataProvider,
		>;

		/// The configuration of benchmarking.
		type BenchmarkingConfig: BenchmarkingConfig;

		/// The weight of the pallet.
		type WeightInfo: WeightInfo;

		type Verifier: verifier::Verifier<Solution = SolutionOf<Self>, AccountId = Self::AccountId>;
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			// first, calculate the 3 main phase switches.
			let unsigned_deadline = T::UnsignedPhase::get();
			let signed_deadline = T::SignedPhase::get().saturating_add(unsigned_deadline);
			let snapshot_deadline = signed_deadline.saturating_add(T::Pages::get().into());

			// TODO: we can build some kind of a state-machine around the phase enum to abstract
			// this away.

			// now compute the offsets due to pagination.
			let signed_verification_deadline =
				signed_deadline.saturating_sub(T::Pages::get().into());
			let last_unsigned_verification_deadline: T::BlockNumber = T::Pages::get().into();

			// TODO: my assumption is that `next_election_prediction` is still the prediction of the
			// FIRST call to `elect`, so staking should be configured to call us AT LEAST `T::Pages`
			// blocks ahead of time.

			let next_election = T::DataProvider::next_election_prediction(now).max(now);
			let remaining_blocks = next_election - now;
			let current_phase = Self::current_phase();

			let last_verification_deadline = log!(
				trace,
				"current phase {:?}, next election {:?}, metadata: {:?}",
				current_phase,
				next_election,
				Snapshot::<T>::metadata()
			);

			match current_phase {
				// from Off to snapshot
				Phase::Off if remaining_blocks <= snapshot_deadline => {
					let remaining_pages = T::Pages::get().saturating_sub(One::one());
					log!(info, "starting snapshot creation [{}]", remaining_pages);
					let _ = Self::create_targets_snapshot().unwrap();
					let _ = Self::create_voters_snapshot_paged(remaining_pages).unwrap();
					CurrentPhase::<T>::put(Phase::Snapshot(remaining_pages));
					0
				},

				// snapshot to signed
				Phase::Snapshot(x) if x > 0 => {
					// we don't check block numbers here, snapshot creation is mandatory.
					let remaining_pages = x.saturating_sub(1);
					log!(info, "continuing snapshot creation [{}]", remaining_pages);
					CurrentPhase::<T>::put(Phase::Snapshot(remaining_pages));
					Self::create_voters_snapshot_paged(remaining_pages);
					0
				},
				Phase::Snapshot(0)
					if remaining_blocks <= signed_deadline &&
						remaining_blocks > unsigned_deadline =>
				{
					// TODO: even though we have the integrity test, what if we open the signed
					// phase, and there's not enough blocks to finalize it? that can happen under
					// any circumstance and we should deal with it.

					// snapshot must be fully created here.
					if cfg!(debug_assertions) {
						Snapshot::<T>::assert_snapshot(true, T::Pages::get());
					}

					// NOTE: if signed-phase length is zero, second part of the if-condition fails.
					<CurrentPhase<T>>::put(Phase::Signed);
					Self::deposit_event(Event::SignedPhaseStarted(Self::round()));
					0
				}

				// signed or snapshot to unsigned
				Phase::Signed | Phase::Snapshot(0)
					if remaining_blocks <= unsigned_deadline && remaining_blocks > Zero::zero() =>
				{
					<CurrentPhase<T>>::put(Phase::Unsigned((true, now)));
					Self::deposit_event(Event::UnsignedPhaseStarted(Self::round()));
					0
				}

				//
				Phase::Verification(last_verified_page) if last_verified_page > 0 => {
					let current_page = last_verified_page - 1;
					todo!();
					0
				},
				Phase::Verification(0) => {
					todo!();
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

			let pages_bn: T::BlockNumber = T::Pages::get().into();
			// pages must be at least 1.
			assert!(T::Pages::get() > 0);
			// pages shall not be more than the length of any phase
			assert!(pages_bn < T::SignedPhase::get());
			assert!(pages_bn < T::UnsignedPhase::get());

			// ----------------------------
			// Based on the requirements of [`sp_npos_elections::Assignment::try_normalize`].
			let max_vote: usize = <SolutionOf<T> as NposSolution>::LIMIT;

			// 1. Maximum sum of [ChainAccuracy; 16] must fit into `UpperOf<ChainAccuracy>`..
			// let maximum_chain_accuracy: Vec<UpperOf<OnChainAccuracyOf<T>>> = (0..max_vote)
			// 	.map(|_| {
			// 		<UpperOf<OnChainAccuracyOf<T>>>::from(
			// 			<OnChainAccuracyOf<T>>::one().deconstruct(),
			// 		)
			// 	})
			// 	.collect();
			// let _: UpperOf<OnChainAccuracyOf<T>> = maximum_chain_accuracy
			// 	.iter()
			// 	.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());

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
				<T::DataProvider as ElectionDataProvider<T::AccountId, T::BlockNumber>>::MAXIMUM_VOTES_PER_VOTER,
				<SolutionOf<T> as NposSolution>::LIMIT as u32,
			);
		}
	}

	#[pallet::event]
	#[pallet::metadata(
		<T as frame_system::Config>::AccountId = "AccountId",
		BalanceOf<T> = "Balance"
	)]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The signed phase of the given round has started.
		SignedPhaseStarted(u32),
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
	}

	#[pallet::type_value]
	pub fn DefaultForRound() -> u32 {
		1
	}

	/// Internal counter for the number of rounds.
	///
	/// This is useful for de-duplication of transactions submitted to the pool, and general
	/// diagnostics of the pallet.
	///
	/// This is merely incremented once per every time that an upstream `elect` is called.
	#[pallet::storage]
	#[pallet::getter(fn round)]
	pub type Round<T: Config> = StorageValue<_, u32, ValueQuery, DefaultForRound>;

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

		pub(crate) fn set_targets(targets: RoundTargetSnapshotPage<T>) {
			Self::write_storage_with_pre_allocate(
				&PagedTargetSnapshot::<T>::hashed_key_for(0),
				targets,
			);
		}

		pub(crate) fn set_voters(page: PageIndex, voters: RoundVoterSnapshotPage<T>) {
			Self::write_storage_with_pre_allocate(
				&PagedVoterSnapshot::<T>::hashed_key_for(page),
				voters,
			);
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
			PagedTargetSnapshot::<T>::remove_all(None);
		}

		// ----------- non-mutables
		pub(crate) fn desired_targets() -> Option<u32> {
			DesiredTargets::<T>::get()
		}

		pub(crate) fn voters(page: PageIndex) -> Option<RoundVoterSnapshotPage<T>> {
			PagedVoterSnapshot::<T>::get(page)
		}

		pub(crate) fn targets() -> Option<RoundTargetSnapshotPage<T>> {
			PagedTargetSnapshot::<T>::get(0)
		}

		pub(crate) fn metadata() -> Option<SolutionOrSnapshotSize> {
			SnapshotMetadata::<T>::get()
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

			(crate::Pallet::<T>::msp()..=crate::Pallet::<T>::lsp())
				.take(up_to_page.into())
				.for_each(|p| {
					assert!(
						exists ^ !Self::voters(p).is_some(),
						"voter page {} mismatch {}",
						p,
						exists
					);
				});
		}

		fn write_storage_with_pre_allocate<E: Encode>(key: &[u8], data: E) {
			let size = data.encoded_size();
			let mut buffer = Vec::with_capacity(size);
			data.encode_to(&mut buffer);

			// do some checks.
			debug_assert_eq!(buffer, data.encode());
			// buffer should have not re-allocated since.
			debug_assert!(buffer.len() == size && size == buffer.capacity());
			sp_io::storage::set(key, &buffer);
		}
	}

	#[cfg(test)]
	impl<T: Config> Snapshot<T> {
		pub fn voter_pages() -> PageIndex {
			PagedVoterSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub fn target_pages() -> PageIndex {
			PagedTargetSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub fn voters_iter() -> impl Iterator<Item = (PageIndex, RoundVoterSnapshotPage<T>)> {
			PagedVoterSnapshot::<T>::iter()
		}

		pub fn voters_iter_flattened() -> impl Iterator<Item = Voter<T>> {
			PagedVoterSnapshot::<T>::iter().map(|(_, v)| v).flatten()
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
	}

	/// The metadata of the [`RoundSnapshot`]
	#[pallet::storage]
	type SnapshotMetadata<T: Config> = StorageValue<_, SolutionOrSnapshotSize>;

	/// Desired number of targets to elect for this round.
	#[pallet::storage]
	type DesiredTargets<T> = StorageValue<_, u32>;

	/// Paginated voter snapshot. At most [`T::Pages`] keys will exist.
	#[pallet::storage]
	type PagedVoterSnapshot<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, RoundVoterSnapshotPage<T>>;

	/// Paginated target snapshot. At most ONE key will exist.
	#[pallet::storage]
	type PagedTargetSnapshot<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, RoundTargetSnapshotPage<T>>;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	/// Perform all the basic checks that are independent of the snapshot.
	pub(crate) fn snapshot_independent_checks(
		paged_solution: &PagedRawSolution<T>,
	) -> sp_runtime::DispatchResult {
		// ensure round is current
		ensure!(Self::round() == paged_solution.round, Error::<T>::WrongRound);

		// ensure score is being improved, if the claim is even correct.
		ensure!(
			<T::Verifier as Verifier>::check_claimed_score(paged_solution.score),
			Error::<T>::WeakSubmission,
		);

		// ensure solution pages are no more than the snapshot
		ensure!(
			paged_solution.solution_pages.len().saturated_into::<PageIndex>() <= T::Pages::get(),
			Error::<T>::WrongPageCount
		);

		// TODO: check the hash of snapshot.

		Ok(())
	}

	/// Returns the most significant page of the snapshot.
	///
	/// Based on the contract of `ElectionDataProvider`, this is the first page that is filled.
	fn msp() -> PageIndex {
		T::Pages::get().checked_sub(1).unwrap_or_else(|| {
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

	/// Creates the target snapshot. Writes new data to:
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_targets_snapshot() -> Result<u32, ElectionError<T>> {
		// if requested, get the targets as well.
		Snapshot::<T>::set_desired_targets(
			T::DataProvider::desired_targets().map_err(ElectionError::DataProvider)?,
		);

		let target_limit = <SolutionTargetIndexOf<T>>::max_value().saturated_into::<usize>();
		let targets =
			T::DataProvider::targets(Some(target_limit), 0).map_err(ElectionError::DataProvider)?;

		let length = targets.len();
		if length > target_limit {
			debug_assert!(false, "Snapshot limit has not been respected.");
			return Err(ElectionError::DataProvider("Snapshot too big."))
		}

		Snapshot::<T>::set_targets(targets);
		Snapshot::<T>::update_metadata(None, Some(length as u32));
		log!(trace, "created target snapshot with {} targets.", length);

		Ok(length as u32)
	}

	/// Creates the voter snapshot. Writes new data to:
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_voters_snapshot_paged(remaining: PageIndex) -> Result<u32, ElectionError<T>> {
		let voter_limit = T::VoterSnapshotPerBlock::get().saturated_into::<usize>();
		let voters = T::DataProvider::voters(Some(voter_limit), remaining)
			.map_err(ElectionError::DataProvider)?;

		// Defensive-only.
		if voters.len() > voter_limit {
			debug_assert!(false, "Snapshot limit has not been respected.");
			return Err(ElectionError::DataProvider("Snapshot too big."))
		}

		let count = voters.len() as u32;
		Snapshot::<T>::set_voters(remaining, voters);
		Snapshot::<T>::update_metadata(Some(count), None);

		log!(
			debug,
			"created paged voters snapshot with key {}, {} more pages needed",
			remaining,
			remaining
		);
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

impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for Pallet<T> {
	type Error = ElectionError<T>;
	type DataProvider = T::DataProvider;

	fn elect(remaining: PageIndex) -> Result<Supports<T::AccountId>, Self::Error> {
		T::Verifier::get_valid_page(remaining)
			.ok_or(ElectionError::SupportPageNotAvailable)
			.or_else(|err| {
				// if this is the last page, we might use the fallback to do something.
				if remaining.is_zero() {
					T::Fallback::elect(remaining).map_err(|fe| ElectionError::<T>::Fallback(fe))
				} else {
					Err(err)
				}
			})
			.map(|supports| {
				// if either of `Verifier` or `Fallback` was okay, and if this is the last page,
				// then clear everything.
				if remaining.is_zero() {
					log!(trace, "processing last page of election");
					Self::rotate_round()
				}

				supports
			})
	}
}

#[cfg(test)]
mod tests {
	use super::{Event, *};
	use crate::{mock::*, unsigned::miner::BaseMiner, verifier::Verifier, Phase};
	use frame_election_provider_support::ElectionProvider;
	use frame_support::{assert_noop, assert_ok};
	use sp_npos_elections::Support;

	#[test]
	fn phase_rotation_single_page() {
		ExtBuilder::default().pages(1).build_and_execute(|| {
			// 0 ------- 14 15 ------- 25 ------- 30 -------------- 44 45 ------- 55 ------- 60
			//              |           |          |                 |   |           |          |
			//            Signed      Unsigned   Elect        Snapshot  Signed     Unsigned    Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 1);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
			Snapshot::<Runtime>::assert_snapshot(true, 1);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 1);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)],
			);
			Snapshot::<Runtime>::assert_snapshot(true, 1);

			roll_to(29);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
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
			assert_eq!(MultiBlock::round(), 2);

			roll_to(43);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(44);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(45);
			assert!(MultiBlock::current_phase().is_signed());

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn phase_rotation_multi_page_2() {
		ExtBuilder::default().pages(2).build_and_execute(|| {
			// 0 -------13 14 15 ------- 25 ------- 30 -------------- 43 44 45 ------- 55 ------- 60
			//           |     |          |          |                 |     |          |          |
			//    Snapshot    Signed    Unsigned   Elect        Snapshot    Signed    Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 1);

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
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 2);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)],
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

			// we fast track to the last elect call with page 0 -- this should clear everything.
			MultiBlock::elect(0).unwrap();

			assert!(MultiBlock::current_phase().is_off());
			// all snapshots are gone.
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 2);

			roll_to(42);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(43);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));

			roll_to(44);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

			roll_to(45);
			assert!(MultiBlock::current_phase().is_signed());

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn phase_rotation_multi_page_3() {
		ExtBuilder::default().pages(3).build_and_execute(|| {
			#[rustfmt::skip]
	 		// 0 ------- 12 13 14 15 ------- 25 ------- 30 -------------- 42 43 44 45 ------- 55 ------- 60
			//            |     |             |          |                |        |          |       |
	 		//     Snapshot    Signed    Unsigned   Elect         Snapshot       Signed    Unsigned  Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			Snapshot::<Runtime>::assert_snapshot(false, 2);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 1);

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
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
			Snapshot::<Runtime>::assert_snapshot(true, 3);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			Snapshot::<Runtime>::assert_snapshot(true, 3);
			assert_eq!(MultiBlock::round(), 1);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)],
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

			// we fast track to the last elect call with page 0 -- this should clear everything.
			MultiBlock::elect(0).unwrap();

			assert!(MultiBlock::current_phase().is_off());
			// all snapshots are gone.
			Snapshot::<Runtime>::assert_snapshot(false, 3);
			assert_eq!(MultiBlock::round(), 2);

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

			roll_to(55);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn multi_page_elect_works() {
		ExtBuilder::default().pages(3).build_and_execute(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// load a solution into the verifier

			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get()).unwrap();
			let score = paged.score.clone();

			// put each submitted page
			for (page_index, solution_page) in paged.solution_pages.into_iter().enumerate() {
				assert_ok!(
					<<Runtime as crate::Config>::Verifier as Verifier>::set_unverified_solution_page(
						page_index as PageIndex,
						solution_page,
					)
				);
			}

			// "seal" the submission
			assert_ok!(
				<<Runtime as crate::Config>::Verifier as Verifier>::seal_unverified_solution(score)
			);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// roll to the block it is finalized
			roll_to(28);

			// there is now a queued solution
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// pre-elect state
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 1);
			assert!(Snapshot::<Runtime>::metadata().is_some());
			assert!(Snapshot::<Runtime>::desired_targets().is_some());
			assert!(Snapshot::<Runtime>::targets().is_some());

			// call elect for each page
			let msp = <Runtime as Config>::Pages::get();
			let solutions = (0..msp)
				.rev() // 2, 1, 0
				.map(|page| {
					crate::Pallet::<Runtime>::elect(page as PageIndex).unwrap();
				})
				.collect::<Vec<_>>();
			assert_eq!(solutions.len(), msp as usize);

			// after the last elect:
			// verifier is cleared,
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 2);
			// and the snapshot is cleared.
			assert!(Snapshot::<Runtime>::metadata().is_none());
			assert!(Snapshot::<Runtime>::desired_targets().is_none());
			assert!(Snapshot::<Runtime>::targets().is_none());
		});
	}

	#[test]
	fn multi_page_elect_fast_track() {
		ExtBuilder::default().pages(3).build_and_execute(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// load a solution into the verifier

			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get()).unwrap();
			let score = paged.score.clone();

			// put each submitted page
			for (page_index, solution_page) in paged.solution_pages.into_iter().enumerate() {
				assert_ok!(
					<<Runtime as crate::Config>::Verifier as Verifier>::set_unverified_solution_page(
						page_index as PageIndex,
						solution_page,
					)
				);
			}

			// "seal" the submission
			assert_ok!(
				<<Runtime as crate::Config>::Verifier as Verifier>::seal_unverified_solution(score)
			);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// roll to the block it is finalized
			roll_to(28);

			// there is now a queued solution
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 1);
			assert!(Snapshot::<Runtime>::metadata().is_some());
			assert!(Snapshot::<Runtime>::desired_targets().is_some());
			assert!(Snapshot::<Runtime>::targets().is_some());

			// there are 3 pages (indexes 2..=0), but we short circuit by just calling 0.
			let _solution = crate::Pallet::<Runtime>::elect(0).unwrap();

			// after elect(0) is called:
			// verifier is cleared,
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 2);
			// and the snapshot is cleared.
			assert!(Snapshot::<Runtime>::metadata().is_none());
			assert!(Snapshot::<Runtime>::desired_targets().is_none());
			assert!(Snapshot::<Runtime>::targets().is_none());
		});
	}

	fn elect_does_not_finish_without_call_of_page_0() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// load a solution into the verifier

			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get()).unwrap();
			let score = paged.score.clone();

			// put each submitted page
			for (page_index, solution_page) in paged.solution_pages.into_iter().enumerate() {
				assert_ok!(
					<<Runtime as crate::Config>::Verifier as Verifier>::set_unverified_solution_page(
						page_index as PageIndex,
						solution_page,
					)
				);
			}

			// "seal" the submission
			assert_ok!(
				<<Runtime as crate::Config>::Verifier as Verifier>::seal_unverified_solution(score)
			);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

			// roll to the block it is finalized
			roll_to(28);

			// there is now a queued solution
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(score));

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 1);
			assert!(Snapshot::<Runtime>::metadata().is_some());
			assert!(Snapshot::<Runtime>::desired_targets().is_some());
			assert!(Snapshot::<Runtime>::targets().is_some());

			// call elect for page 2 and 1, but NOT 0
			let msp = <Runtime as Config>::Pages::get();
			let solutions = (1..msp)
				.rev() // 2, 1
				.map(|page| {
					crate::Pallet::<Runtime>::elect(page as PageIndex).unwrap();
				})
				.collect::<Vec<_>>();
			assert_eq!(solutions.len(), 2);

			// nothing changes from the prelect state
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(Round::<Runtime>::get(), 1);
			assert!(Snapshot::<Runtime>::metadata().is_some());
			assert!(Snapshot::<Runtime>::desired_targets().is_some());
			assert!(Snapshot::<Runtime>::targets().is_some());
		});
	}

	#[test]
	fn when_passive_stay_in_phase_unsigned() {
		ExtBuilder::default().build_and_execute(|| {
			// once the unsigned phase starts, it will not be changed by on_initialize (something
			// like `elect` must be called).
			for page in 25..55 {
				roll_to(page);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			}
		});
	}

	#[test]
	fn multi_page_elect_fallback_works() {}

	/*
	#[test]
	fn signed_phase_void() {
		ExtBuilder::default().phases(0, 10).build_and_execute(|| {
			roll_to(15);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(19);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(20);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(20));
			assert!(MultiBlock::snapshot().is_some());

			roll_to(30);
			assert!(MultiBlock::current_phase().is_unsigned_open_at(20));

			MultiBlock::elect().unwrap();

			assert!(MultiBlock::current_phase().is_off());
			assert!(MultiBlock::snapshot().is_none());
		});
	}

	#[test]
	fn unsigned_phase_void() {
		ExtBuilder::default().phases(10, 0).build_and_execute(|| {
			roll_to(15);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(19);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(20);
			assert!(MultiBlock::current_phase().is_signed());
			assert!(MultiBlock::snapshot().is_some());

			roll_to(30);
			assert!(MultiBlock::current_phase().is_signed());

			assert_ok!(MultiBlock::elect());

			assert!(MultiBlock::current_phase().is_off());
			assert!(MultiBlock::snapshot().is_none());
		});
	}

	#[test]
	fn both_phases_void() {
		ExtBuilder::default().phases(0, 0).build_and_execute(|| {
			roll_to(15);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(19);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(20);
			assert!(MultiBlock::current_phase().is_off());

			roll_to(30);
			assert!(MultiBlock::current_phase().is_off());

			// This module is now only capable of doing on-chain backup.
			assert_ok!(MultiBlock::elect());

			assert!(MultiBlock::current_phase().is_off());
		});
	}

	#[test]
	fn early_termination() {
		// An early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// Signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(MultiBlock::round(), 1);

			// An unexpected call to elect.
			roll_to(20);
			MultiBlock::elect().unwrap();

			// We surely can't have any feasible solutions. This will cause an on-chain election.
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(1),
					Event::ElectionFinalized(Some(ElectionCompute::OnChain))
				],
			);
			// All storage items must be cleared.
			assert_eq!(MultiBlock::round(), 2);
			assert!(MultiBlock::snapshot().is_none());
			assert!(MultiBlock::snapshot_metadata().is_none());
			assert!(MultiBlock::desired_targets().is_none());
			assert!(MultiBlock::queued_solution().is_none());
			assert!(MultiBlock::signed_submissions().is_empty());
		})
	}

	#[test]
	fn early_termination_with_submissions() {
		// an early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(MultiBlock::round(), 1);

			// fill the queue with signed submissions
			for s in 0..SignedMaxSubmissions::get() {
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(MultiBlock::submit(
					crate::mock::Origin::signed(99),
					Box::new(solution),
					MultiBlock::signed_submissions().len() as u32
				));
			}

			// an unexpected call to elect.
			roll_to(20);
			assert!(MultiBlock::elect().is_ok());

			// all storage items must be cleared.
			assert_eq!(MultiBlock::round(), 2);
			assert!(MultiBlock::snapshot().is_none());
			assert!(MultiBlock::snapshot_metadata().is_none());
			assert!(MultiBlock::desired_targets().is_none());
			assert!(MultiBlock::queued_solution().is_none());
			assert!(MultiBlock::signed_submissions().is_empty());
		})
	}

	#[test]
	fn fallback_strategy_works() {
		ExtBuilder::default().fallback(FallbackStrategy::OnChain).build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// Zilch solutions thus far.
			let (supports, _) = MultiBlock::elect().unwrap();

			assert_eq!(
				supports,
				vec![
					(30, Support { total: 40, voters: vec![(2, 5), (4, 5), (30, 30)] }),
					(40, Support { total: 60, voters: vec![(2, 5), (3, 10), (4, 5), (40, 40)] })
				]
			)
		});

		ExtBuilder::default().fallback(FallbackStrategy::Nothing).build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// Zilch solutions thus far.
			assert_eq!(MultiBlock::elect().unwrap_err(), ElectionError::NoFallbackConfigured);
		})
	}

	#[test]
	fn snapshot_too_big_failure_onchain_fallback() {
		// the `MockStaking` is designed such that if it has too many targets, it simply fails.
		ExtBuilder::default().build_and_execute(|| {
			Targets::set((0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>());

			// Signed phase failed to open.
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			// Unsigned phase failed to open.
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			// On-chain backup works though.
			roll_to(29);
			let (supports, _) = MultiBlock::elect().unwrap();
			assert!(supports.len() > 0);
		});
	}

	#[test]
	fn snapshot_too_big_failure_no_fallback() {
		// and if the backup mode is nothing, we go into the emergency mode..
		ExtBuilder::default().fallback(FallbackStrategy::Nothing).build_and_execute(|| {
			crate::mock::Targets::set(
				(0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>(),
			);

			// Signed phase failed to open.
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			// Unsigned phase failed to open.
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(29);
			let err = MultiBlock::elect().unwrap_err();
			assert_eq!(err, ElectionError::NoFallbackConfigured);
			assert_eq!(MultiBlock::current_phase(), Phase::Emergency);
		});
	}

	#[test]
	fn snapshot_too_big_truncate() {
		// but if there are too many voters, we simply truncate them.
		ExtBuilder::default().build_and_execute(|| {
			// we have 8 voters in total.
			assert_eq!(crate::mock::Voters::get().len(), 8);
			// but we want to take 4.
			crate::mock::VoterSnapshotPerBlock::set(2);

			// Signed phase opens just fine.
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			assert_eq!(
				MultiBlock::snapshot_metadata().unwrap(),
				SolutionOrSnapshotSize { voters: 2, targets: 4 }
			);
		})
	}

	#[test]
	fn untrusted_score_verification_is_respected() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			let (solution, _) = MultiBlock::mine_solution(2).unwrap();
			// Default solution has a score of [50, 100, 5000].
			assert_eq!(solution.score, [50, 100, 5000]);

			<MinimumUntrustedScore<Runtime>>::put([49, 0, 0]);
			assert_ok!(MultiBlock::feasibility_check(solution.clone(), ElectionCompute::Signed));

			<MinimumUntrustedScore<Runtime>>::put([51, 0, 0]);
			assert_noop!(
				MultiBlock::feasibility_check(solution, ElectionCompute::Signed),
				FeasibilityError::UntrustedScoreTooLow,
			);
		})
	}

	#[test]
	fn number_of_voters_allowed_2sec_block() {
		// Just a rough estimate with the substrate weights.
		assert!(!MockWeightInfo::get());

		let all_voters: u32 = 10_000;
		let all_targets: u32 = 5_000;
		let desired: u32 = 1_000;
		let weight_with = |active| {
			<Runtime as Config>::WeightInfo::submit_unsigned(
				all_voters,
				all_targets,
				active,
				desired,
			)
		};

		let mut active = 1;
		while weight_with(active) <=
			<Runtime as frame_system::Config>::BlockWeights::get().max_block ||
			active == all_voters

		{
			active += 1;
		}

		println!("can support {} voters to yield a weight of {}", active, weight_with(active));
	}
	*/
}
