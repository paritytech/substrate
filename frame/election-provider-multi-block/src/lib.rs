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

//! # Multi-phase, multi-block, election provider pallet.
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
//! pallet is scale linearly with the number of blocks allocated to the elections. Moreover, the
//! amount of work that it does in one block should be bounded and measurable, making it suitable
//! for a parachain. In principle, with large enough blocks (in a dedicated parachain), the number
//! of voters included in the NPoS system can grow significantly (yet, obviously not indefinitely).
//!
//! Note that this pallet does not consider how the recipient is processing the results. To ensure
//! scalability, of course, the recipient of this pallet's data (i.e. `pallet-staking`) must also be
//! capable of pagination and multi-block processing.
//!
//! ## Companion pallets
//!
//! This pallet is essentially hierarchical. This particular one is the top level one. It contains
//! the shared information that all child pallets use. All child pallets can depend on on the top
//! level pallet ONLY, but not the other way around. For those cases, traits are used.
//!
//! This pallet will only function in a sensible way if it is peered with its companion pallets.
//!
//! - The [`verifier`] pallet provides a standard implementation of the [`verifier::Verifier`]. This
//!   pallet is mandatory.
//! - The [`unsigned`] module provides the implementation of unsigned submission by validators. If
//!   this pallet is included, then [`Config::UnsignedPhase`] will determine its duration.
//! - The [`Signed`] module provides the implementation of the signed submission by any account. If
//!   this pallet is included, the combined [`Config::SignedPhase`] and
//!   [`Config::SignedValidationPhase`] will deter its duration
//!
//! ### Pallet Ordering:
//!
//! TODO: parent, verifier, signed, unsigned
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
//! The duration of both phases are configurable, and their existence is optional. Each of the
//! phases can be disabled by essentially setting their length to zero. If both phases have length
//! zero, then the pallet essentially runs only the fallback strategy, denoted by
//! [`Config::Fallback`].
//!
//! - Note that the prediction of the election is assume to be the **first call** to elect. For
//! example, with 3 pages, the prediction must point to the `elect(2)`.
//! - Note that the unsigned phase starts [`pallet::Config::UnsignedPhase`] blocks before the
//! `next_election_prediction`, but only ends when a call to [`ElectionProvider::elect`] happens. If
//! no `elect` happens, the current phase (usually unsigned) is extended.
//!
//! > Given this, it is rather important for the user of this pallet to ensure it always terminates
//! election via `elect` before requesting a new one.
//!
//! TODO: test case: elect(2) -> elect(1) -> elect(2)
//! TODO: should we wipe the verifier afterwards, or just `::take()` the election result?
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

use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::{
	onchain, BoundedSupportsOf, ElectionDataProvider, ElectionProvider, PageIndex,
};
use frame_support::{
	ensure,
	traits::{ConstU32, Defensive, Get},
	BoundedVec, CloneNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
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

/// A fallback implementation that transitions the pallet to the emergency phase.
pub struct InitiateEmergencyPhase<T>(sp_std::marker::PhantomData<T>);
impl<T: verifier::Config> ElectionProvider for InitiateEmergencyPhase<T> {
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type DataProvider = T::DataProvider;
	type Error = &'static str;
	type Pages = ConstU32<1>;
	type MaxBackersPerWinner = T::MaxBackersPerWinner;
	type MaxWinnersPerPage = T::MaxWinnersPerPage;

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

/// Different operations that the [`Config::AdminOrigin`] can perform on the pallet.
#[derive(
	Encode,
	Decode,
	MaxEncodedLen,
	TypeInfo,
	RuntimeDebugNoBound,
	CloneNoBound,
	PartialEqNoBound,
	EqNoBound,
)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub enum AdminOperation<T: Config> {
	/// Clear all storage items.
	///
	/// This will probably end-up being quite expensive. It will clear the internals of all
	/// pallets, setting cleaning all of them.
	///
	/// Hopefully, this can result in a full reset of the system.
	KillEverything,
	/// Force-set the phase to the given phase.
	///
	/// This can have many many combinations, use only with care and sufficient testing.
	ForceSetPhase(Phase<T::BlockNumber>),
	/// Set the given (single page) emergency solution.
	///
	/// This can be called in any phase and, can behave like any normal solution, but it should
	/// probably be used only in [`Phase::Emergency`].
	SetSolution(SolutionOf<T>, ElectionScore),
	/// Trigger the (single page) fallback in `instant` mode, with the given parameters, and
	/// queue it if correct.
	///
	/// This can be called in any phase and, can behave like any normal solution, but it should
	/// probably be used only in [`Phase::Emergency`].
	TriggerFallback,
	/// Set the minimum untrusted score. This is directly communicated to the verifier component to
	/// be taken into account.
	///
	/// This is useful in preventing any serious issue where due to a bug we accept a very bad
	/// solution.
	SetMinUntrustedScore(ElectionScore),
}

#[frame_support::pallet]
pub mod pallet {
	use crate::{
		types::*,
		verifier::{self},
		AdminOperation, WeightInfo,
	};
	use frame_election_provider_support::{
		ElectionDataProvider, ElectionProvider, NposSolution, PageIndex,
	};
	use frame_support::{pallet_prelude::*, traits::EnsureOrigin, Twox64Concat};
	use frame_system::pallet_prelude::*;
	use sp_arithmetic::{traits::CheckedAdd, PerThing, UpperOf};
	use sp_runtime::traits::{Hash, Saturating, Zero};
	use sp_std::{borrow::ToOwned, prelude::*};

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
			+ verifier::AsynchronousVerifier;

		/// The number of blocks ahead of time to try and have the election results ready by.
		type Lookahead: Get<Self::BlockNumber>;

		/// The origin that can perform administration operations on this pallet.
		type AdminOrigin: EnsureOrigin<Self::Origin>;

		/// The weight of the pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn manage(_origin: OriginFor<T>, op: AdminOperation<T>) -> DispatchResultWithPostInfo {
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
				.saturating_sub(T::Lookahead::get())
				.max(now);
			let remaining_blocks = next_election - now;
			let current_phase = Self::current_phase();

			log!(
				trace,
				"current phase {:?}, next election {:?}, remaining: {:?}, deadlines: [unsigned {:?} signed_validation {:?}, signed {:?}, snapshot {:?}]",
				current_phase,
				next_election,
				remaining_blocks,
				unsigned_deadline,
				signed_validation_deadline,
				signed_deadline,
				snapshot_deadline,
			);

			match current_phase {
				// start and continue snapshot.
				Phase::Off
					if remaining_blocks <= snapshot_deadline
					// && remaining_blocks > signed_deadline
					=>
				{
					let remaining_pages = Self::msp();
					log!(info, "starting snapshot creation, remaining block: {}", remaining_pages);
					let count = Self::create_targets_snapshot().unwrap();
					let count = Self::create_voters_snapshot_paged(remaining_pages).unwrap();
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
					<CurrentPhase<T>>::put(Phase::Unsigned(now));
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

			// The duration of the signed validation phase should be such that at least one solution
			// can be verified.
			assert!(
				T::SignedValidationPhase::get() >= T::Pages::get().into(),
				"signed validation phase should be at least as long as the number of pages."
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

	/// Wrapper struct for working with snapshots.
	///
	/// It manages the following storage items:
	///
	/// - [`DesiredTargets`]: The number of targets that we wish to collect.
	/// - [`PagedVoterSnapshot`]: Paginated map of voters.
	/// - [`PagedVoterSnapshotHash`]: Hash of the aforementioned.
	/// - [`PagedTargetSnapshot`]: Paginated map of targets.
	/// - [`PagedTargetSnapshotHash`]: Hash of the aforementioned.
	///
	/// ### Invariants
	///
	/// The following invariants must be met at **all times** for this storage item to be "correct".
	///
	/// - [`PagedVoterSnapshotHash`] must always contain the correct the same number of keys, and
	///   the corresponding hash of the [`PagedVoterSnapshot`].
	/// - [`PagedTargetSnapshotHash`] must always contain the correct the same number of keys, and
	///   the corresponding hash of the [`PagedTargetSnapshot`].
	///
	/// - If any page from the paged voters/targets exists, then the aforementioned (desired
	///   targets) must also exist.
	///
	/// The following invariants might need to hold based on the current phase.
	///
	///   - If `Phase` IS `Snapshot(_)`, then partial voter/target pages must exist from `msp` to
	///     `lsp` based on the inner value.
	///   - If `Phase` IS `Off`, then, no snapshot must exist.
	///   - In all other phases, the snapshot must FULLY exist.
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

		/// Destroy the entire snapshot.
		///
		/// Should be called only once we transition to [`Phase::Off`].
		pub(crate) fn kill() {
			DesiredTargets::<T>::kill();
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

		/// Get a fingerprint of the snapshot, from all the hashes that are stored for each page of
		/// the snapshot.
		///
		/// This is computed as: `(target_hash, voter_hash_n, voter_hash_(n-1), ..., voter_hash_0)`
		/// where `n` is `T::Pages - 1`. In other words, it is the concatenated hash of targets, and
		/// voters, from `msp` to `lsp`.
		pub fn fingerprint() -> T::Hash {
			let mut hashed_target_and_voters =
				PagedTargetSnapshotHash::<T>::get(Pallet::<T>::lsp())
					.unwrap_or_default()
					.as_ref()
					.to_vec();
			let hashed_voters = (Pallet::<T>::msp()..=Pallet::<T>::lsp())
				.map(|i| PagedVoterSnapshotHash::<T>::get(i).unwrap_or_default())
				.map(|hash| <T::Hash as AsRef<[u8]>>::as_ref(&hash).to_owned())
				.flatten()
				.collect::<Vec<u8>>();
			hashed_target_and_voters.extend(hashed_voters);
			T::Hashing::hash(&hashed_target_and_voters)
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
		pub(crate) fn ensure_snapshot(
			exists: bool,
			mut up_to_page: PageIndex,
		) -> Result<(), &'static str> {
			up_to_page = up_to_page.min(T::Pages::get());
			// NOTE: if someday we split the snapshot taking of voters(msp) and targets into two
			// different blocks, then this assertion becomes obsolete.
			ensure!(up_to_page > 0, "can't check snapshot up to page 0");

			// if any number of pages supposed to exist, these must also exist.
			ensure!(exists ^ Self::desired_targets().is_none(), "desired target mismatch");
			ensure!(exists ^ Self::targets().is_none(), "targets mismatch");
			ensure!(exists ^ Self::targets_hash().is_none(), "targets hash mismatch");

			// and the hash is correct.
			if let Some(targets) = Self::targets() {
				let hash = Self::targets_hash().expect("must exist; qed");
				ensure!(hash == T::Hashing::hash(&targets.encode()), "targets hash mismatch");
			}

			// ensure that pages that should exist, indeed to exist..
			let mut sum_existing_voters = 0;
			for p in (crate::Pallet::<T>::lsp()..=crate::Pallet::<T>::msp())
				.rev()
				.take(up_to_page as usize)
			{
				ensure!(
					(exists ^ Self::voters(p).is_none()) &&
						(exists ^ Self::voters_hash(p).is_none()),
					"voter page existence mismatch"
				);

				if let Some(voters_page) = Self::voters(p) {
					sum_existing_voters = sum_existing_voters.saturating_add(voters_page.len());
					let hash = Self::voters_hash(p).expect("must exist; qed");
					ensure!(hash == T::Hashing::hash(&voters_page.encode()), "voter hash mismatch");
				}
			}

			// ..and those that should not exist, indeed DON'T.
			for p in (crate::Pallet::<T>::lsp()..=crate::Pallet::<T>::msp())
				.take((T::Pages::get() - up_to_page) as usize)
			{
				ensure!(
					(exists ^ Self::voters(p).is_some()) &&
						(exists ^ Self::voters_hash(p).is_some()),
					"voter page non-existence mismatch"
				);
			}

			Ok(())
		}

		#[cfg(any(test, debug_assertions))]
		pub(crate) fn sanity_check() -> Result<(), &'static str> {
			// check the snapshot existence based on the phase. This checks all of the needed
			// conditions except for the metadata values.
			let _ = match Pallet::<T>::current_phase() {
				// no page should exist in this phase.
				Phase::Off => Self::ensure_snapshot(false, T::Pages::get()),
				// exact number of pages must exist in this phase.
				Phase::Snapshot(p) => Self::ensure_snapshot(true, T::Pages::get() - p),
				// full snapshot must exist in these phases.
				Phase::Emergency |
				Phase::Signed |
				Phase::SignedValidation(_) |
				Phase::Export |
				Phase::Unsigned(_) => Self::ensure_snapshot(true, T::Pages::get()),
				// cannot assume anything. We might halt at any point.
				Phase::Halted => Ok(()),
			}?;

			Ok(())
		}
	}

	#[cfg(test)]
	impl<T: Config> Snapshot<T> {
		pub(crate) fn voter_pages() -> PageIndex {
			use sp_runtime::SaturatedConversion;
			PagedVoterSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub(crate) fn target_pages() -> PageIndex {
			use sp_runtime::SaturatedConversion;
			PagedTargetSnapshot::<T>::iter().count().saturated_into::<PageIndex>()
		}

		pub(crate) fn voters_iter_flattened() -> impl Iterator<Item = VoterOf<T>> {
			let key_range =
				(crate::Pallet::<T>::lsp()..=crate::Pallet::<T>::msp()).collect::<Vec<_>>();
			key_range
				.into_iter()
				.map(|k| PagedVoterSnapshot::<T>::get(k).unwrap_or_default())
				.flatten()
		}

		pub(crate) fn remove_voter_page(page: PageIndex) {
			PagedVoterSnapshot::<T>::remove(page);
		}

		pub(crate) fn kill_desired_targets() {
			DesiredTargets::<T>::kill();
		}

		pub(crate) fn remove_target_page(page: PageIndex) {
			PagedTargetSnapshot::<T>::remove(page);
		}

		pub(crate) fn remove_target(at: usize) {
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
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	/// Returns the most significant page of the snapshot.
	///
	/// Based on the contract of `ElectionDataProvider`, this is the first page that is filled.
	fn msp() -> PageIndex {
		T::Pages::get().checked_sub(1).defensive_unwrap_or_default()
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
		let targets: BoundedVec<_, T::TargetSnapshotPerBlock> =
			T::DataProvider::electable_targets(limit, 0)
				.and_then(|v| v.try_into().map_err(|_| "try-into failed"))
				.map_err(ElectionError::DataProvider)?;

		let count = targets.len() as u32;
		log!(debug, "created target snapshot with {} targets.", count);
		Snapshot::<T>::set_targets(targets);

		Ok(count)
	}

	/// Creates the voter snapshot. Writes new data to:
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_voters_snapshot_paged(remaining: PageIndex) -> Result<u32, ElectionError<T>> {
		let limit = Some(T::VoterSnapshotPerBlock::get().saturated_into::<usize>());
		let voters: BoundedVec<_, T::VoterSnapshotPerBlock> =
			T::DataProvider::electing_voters(limit, remaining)
				.and_then(|v| v.try_into().map_err(|_| "try-into failed"))
				.map_err(ElectionError::DataProvider)?;

		let count = voters.len() as u32;
		Snapshot::<T>::set_voters(remaining, voters);
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

	#[cfg(any(test, debug_assertions))]
	pub(crate) fn sanity_check() -> Result<(), &'static str> {
		Snapshot::<T>::sanity_check()
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
	use frame_support::traits::Hooks;

	#[test]
	fn single_page() {
		ExtBuilder::full().pages(1).onchain_fallback(true).build_and_execute(|| {
			// 0 -------- 14 15 --------- 20 ------------- 25 ---------- 30
			//            |  |            |                |             |
			//    Snapshot Signed  SignedValidation    Unsigned       elect()

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 1));
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
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			MultiBlock::elect(0).unwrap();

			assert!(MultiBlock::current_phase().is_off());
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 1));
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
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 2));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(12);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			roll_to(29);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			MultiBlock::elect(0).unwrap(); // and even this one's coming from the fallback.
			assert!(MultiBlock::current_phase().is_off());

			// all snapshots are gone.
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 2));
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
			// 0 ------- 12 13 14 15 ----------- 20 ---------25 ------- 30
			//            |       |              |            |          |
			//     Snapshot      Signed   SignedValidation  Unsigned   Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 3));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(4);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(11);
			assert_eq!(MultiBlock::current_phase(), Phase::Off);

			roll_to(12);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

			roll_to(13);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

			roll_to(14);
			assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));
			assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 3));

			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(19);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert_eq!(MultiBlock::round(), 0);

			roll_to(20);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(
				multi_block_events(),
				vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
			);

			roll_to(24);
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(MultiBlock::round(), 0);

			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(
				multi_block_events(),
				vec![
					Event::SignedPhaseStarted(0),
					Event::SignedValidationPhaseStarted(0),
					Event::UnsignedPhaseStarted(0)
				],
			);

			roll_to(29);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			roll_to(30);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			MultiBlock::elect(0).unwrap();
			assert!(MultiBlock::current_phase().is_off());

			// all snapshots are gone.
			assert_none_snapshot();
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
		ExtBuilder::full()
			.pages(3)
			.lookahead(2)
			.onchain_fallback(true)
			.build_and_execute(|| {
				// 0 ------- 10 11 12 13 ----------- 17 ---------22 ------- 27
				//            |       |              |            |          |
				//     Snapshot      Signed   SignedValidation  Unsigned   Elect

				assert_eq!(System::block_number(), 0);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_none_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(4);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_eq!(MultiBlock::round(), 0);

				roll_to(9);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);

				roll_to(10);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));
				assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 1));

				roll_to(11);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
				assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 2));

				roll_to(12);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));
				assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, 3));

				roll_to(13);
				assert_eq!(MultiBlock::current_phase(), Phase::Signed);
				assert_eq!(multi_block_events(), vec![Event::SignedPhaseStarted(0)]);
				assert_eq!(MultiBlock::round(), 0);

				roll_to(17);
				assert_eq!(MultiBlock::current_phase(), Phase::Signed);
				assert_full_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(18);
				assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(18));
				assert_eq!(
					multi_block_events(),
					vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
				);

				roll_to(22);
				assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(18));
				assert_full_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(23);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(23));
				assert_eq!(
					multi_block_events(),
					vec![
						Event::SignedPhaseStarted(0),
						Event::SignedValidationPhaseStarted(0),
						Event::UnsignedPhaseStarted(0)
					],
				);

				roll_to(27);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(23));

				roll_to(28);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(23));

				// We close when upstream tells us to elect.
				roll_to(30);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(23));

				MultiBlock::elect(0).unwrap();
				assert!(MultiBlock::current_phase().is_off());

				// all snapshots are gone.
				assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, 3));
				assert_eq!(MultiBlock::round(), 1);

				roll_to(41 - 2);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);

				roll_to(42 - 2);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));

				roll_to(43 - 2);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));

				roll_to(44 - 2);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

				roll_to(45 - 2);
				assert!(MultiBlock::current_phase().is_signed());

				roll_to(50 - 2);
				assert!(MultiBlock::current_phase().is_signed_validation_open_at(50 - 2));

				roll_to(55 - 2);
				assert!(MultiBlock::current_phase().is_unsigned_open_at(55 - 2));
			})
	}

	#[test]
	fn no_unsigned_phase() {
		ExtBuilder::full()
			.pages(3)
			.unsigned_phase(0)
			.onchain_fallback(true)
			.build_and_execute(|| {
				// 0 --------------------- 17 ------ 20 ---------25 ------- 30
				//            |            |         |            |          |
				//                     Snapshot    Signed  SignedValidation   Elect

				assert_eq!(System::block_number(), 0);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_none_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(4);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_eq!(MultiBlock::round(), 0);

				roll_to(17);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));
				roll_to(18);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
				roll_to(19);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

				assert_full_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(20);
				assert_eq!(MultiBlock::current_phase(), Phase::Signed);
				roll_to(25);
				assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(25));

				assert_eq!(
					multi_block_events(),
					vec![Event::SignedPhaseStarted(0), Event::SignedValidationPhaseStarted(0)],
				);

				// Signed validation can now be expanded until a call to `elect` comes
				roll_to(27);
				assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(25));
				roll_to(32);
				assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(25));

				MultiBlock::elect(0).unwrap();
				assert!(MultiBlock::current_phase().is_off());

				// all snapshots are gone.
				assert_none_snapshot();
				assert_eq!(MultiBlock::round(), 1);
				assert_ok!(signed::Submissions::<Runtime>::ensure_killed(0));
				verifier::QueuedSolution::<Runtime>::assert_killed();
			})
	}

	#[test]
	fn no_signed_phase() {
		ExtBuilder::full()
			.pages(3)
			.signed_phase(0, 0)
			.onchain_fallback(true)
			.build_and_execute(|| {
				// 0 ------------------------- 22 ------ 25 ------- 30
				//                             |         |          |
				//                         Snapshot   Unsigned   Elect

				assert_eq!(System::block_number(), 0);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_none_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(20);
				assert_eq!(MultiBlock::current_phase(), Phase::Off);
				assert_eq!(MultiBlock::round(), 0);

				roll_to(22);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(2));
				roll_to(23);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(1));
				roll_to(24);
				assert_eq!(MultiBlock::current_phase(), Phase::Snapshot(0));

				assert_full_snapshot();
				assert_eq!(MultiBlock::round(), 0);

				roll_to(25);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
				assert_eq!(multi_block_events(), vec![Event::UnsignedPhaseStarted(0)],);

				// Unsigned can now be expanded until a call to `elect` comes
				roll_to(27);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
				roll_to(32);
				assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

				MultiBlock::elect(0).unwrap();
				assert!(MultiBlock::current_phase().is_off());

				// all snapshots are gone.
				assert_none_snapshot();
				assert_eq!(MultiBlock::round(), 1);
				assert_ok!(signed::Submissions::<Runtime>::ensure_killed(0));
				verifier::QueuedSolution::<Runtime>::assert_killed();
			})
	}

	#[test]
	fn no_any_phase() {
		todo!()
	}

	#[test]
	#[should_panic(
		expected = "signed validation phase should be at least as long as the number of pages"
	)]
	fn incorrect_signed_validation_phase() {
		ExtBuilder::full()
			.pages(3)
			.signed_validation_phase(2)
			.build_and_execute(|| <MultiBlock as Hooks<BlockNumber>>::integrity_test())
	}
}

#[cfg(test)]
mod election_provider {
	use super::*;
	use crate::{mock::*, unsigned::miner::BaseMiner, verifier::Verifier, Phase};
	use frame_election_provider_support::ElectionProvider;
	use frame_support::{assert_storage_noop, unsigned::ValidateUnsigned};

	// This is probably the most important test of all, a basic, correct scenario. This test should
	// be studied in detail, and all of the branches of how it can go wrong or diverge from the
	// basic scenario assessed.
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
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), None);

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
					verifier::Event::Queued(score, None),
				]
			);

			// there is now a queued solution.
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), Some(score));

			// now let's go to unsigned phase, but we don't expect anything to happen there since we
			// don't run OCWs.
			roll_to_unsigned_open();

			// pre-elect state
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(MultiBlock::round(), 0);
			assert_full_snapshot();

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
			verifier::QueuedSolution::<Runtime>::assert_killed();
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 1);
			// and the snapshot is cleared,
			assert_storage_noop!(Snapshot::<Runtime>::kill());
			// signed pallet is clean.
			// NOTE: in the future, if and when we add lazy cleanup to the signed pallet, this
			// assertion might break.
			assert_ok!(signed::Submissions::<Runtime>::ensure_killed(0));
		});
	}

	#[test]
	fn multi_page_elect_fast_track() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			let round = MultiBlock::round();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();
			let score = paged.score.clone();
			load_signed_for_verification_and_start(99, paged, 0);

			// there is no queued solution prior to the last page of the solution getting verified
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), None);

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
					verifier::Event::Queued(score, None),
				]
			);

			// there is now a queued solution.
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), Some(score));

			// not much impact, just for the sane-ness of the test.
			roll_to_unsigned_open();

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(Round::<Runtime>::get(), 0);
			assert_full_snapshot();

			// there are 3 pages (indexes 2..=0), but we short circuit by just calling 0.
			let _solution = crate::Pallet::<Runtime>::elect(0).unwrap();

			// round is incremented.
			assert_eq!(MultiBlock::round(), round + 1);
			// after elect(0) is called, verifier is cleared,
			verifier::QueuedSolution::<Runtime>::assert_killed();
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 1);
			// the snapshot is cleared,
			assert_none_snapshot();
			// and signed pallet is clean.
			assert_ok!(signed::Submissions::<Runtime>::ensure_killed(round));
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
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), None);

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
					verifier::Event::Queued(score, None),
				]
			);

			// there is now a queued solution
			assert_eq!(<Runtime as crate::Config>::Verifier::queued_score(), Some(score));

			// not much impact, just for the sane-ness of the test.
			roll_to_unsigned_open();

			// pre-elect state:
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			assert_eq!(Round::<Runtime>::get(), 0);
			assert_full_snapshot();

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
			assert_full_snapshot();
		});
	}

	#[test]
	fn when_passive_stay_in_phase_unsigned() {
		ExtBuilder::full().build_and_execute(|| {
			// once the unsigned phase starts, it will not be changed by on_initialize (something
			// like `elect` must be called).
			roll_to_unsigned_open();
			for _ in 0..100 {
				roll_next();
				assert!(matches!(MultiBlock::current_phase(), Phase::Unsigned(_)));
			}
		});
	}

	#[test]
	fn skip_unsigned_phase() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			let round = MultiBlock::round();

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();

			load_signed_for_verification_and_start_and_roll_to_verified(99, paged, 0);

			// and right here, in the middle of the signed verification phase, we close the round.
			// Everything should work fine.
			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));
			assert_eq!(Round::<Runtime>::get(), 0);
			assert_full_snapshot();

			// fetch all pages.
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

			// round is incremented.
			assert_eq!(MultiBlock::round(), round + 1);
			// after elect(0) is called, verifier is cleared,
			verifier::QueuedSolution::<Runtime>::assert_killed();
			// the phase is off,
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			// the round is incremented,
			assert_eq!(Round::<Runtime>::get(), 1);
			// the snapshot is cleared,
			assert_storage_noop!(Snapshot::<Runtime>::kill());
			// and signed pallet is clean.
			assert_ok!(signed::Submissions::<Runtime>::ensure_killed(round));
		});
	}

	#[test]
	fn call_to_elect_should_prevent_any_submission() {
		ExtBuilder::full().build_and_execute(|| {
			roll_to_signed_open();
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);

			// load a solution into the verifier
			let paged = BaseMiner::<Runtime>::mine_solution(Pages::get(), false).unwrap();
			load_signed_for_verification_and_start_and_roll_to_verified(99, paged, 0);

			assert_eq!(MultiBlock::current_phase(), Phase::SignedValidation(20));

			// fetch one page.
			assert!(MultiBlock::elect(MultiBlock::msp()).is_ok());

			// try submit one signed page:
			assert_noop!(
				SignedPallet::submit_page(Origin::signed(999), 0, Default::default()),
				"phase not signed"
			);
			assert_noop!(
				SignedPallet::register(Origin::signed(999), Default::default()),
				"phase not signed"
			);
			assert_storage_noop!(assert!(<UnsignedPallet as ValidateUnsigned>::pre_dispatch(
				&unsigned::Call::submit_unsigned { paged_solution: Default::default() }
			)
			.is_err()));
		});
	}

	#[test]
	fn multi_page_elect_fallback_works() {
		todo!()
	}
}

mod admin_ops {
	use super::*;

	#[test]
	fn elect_call_on_off_or_halt_phase() {
		todo!();
	}

	#[test]
	fn force_clear() {
		todo!("something very similar to the scenario of elect_does_not_finish_without_call_of_page_0, where we want to forcefully clear and put everything into halt phase")
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

	#[test]
	fn snapshot_size_2second_weight() {
		todo!()
	}
}
