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

//! # Multi phase, offchain election provider pallet.
//!
//! Currently, this election-provider has two distinct phases (see [`Phase`]), **signed** and
//! **unsigned**.
//!
//! ## Phases
//!
//! The timeline of pallet is as follows. At each block,
//! [`frame_election_provider_support::ElectionDataProvider::next_election_prediction`] is used to
//! estimate the time remaining to the next call to
//! [`frame_election_provider_support::ElectionProvider::elect`]. Based on this, a phase is chosen.
//! The timeline is as follows.
//!
//! ```ignore
//!                                                                    elect()
//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
//!   +-------------------------------------------------------------------+
//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
//! ```
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
//! ### Fallback
//!
//! If we reach the end of both phases (i.e. call to [`ElectionProvider::elect`] happens) and no
//! good solution is queued, then the fallback strategy [`pallet::Config::Fallback`] is used to
//! determine what needs to be done. The on-chain election is slow, and contains no balancing or
//! reduction post-processing. See [`onchain::OnChainSequentialPhragmen`]. The
//! [`FallbackStrategy::Nothing`] just returns an error, and enables the [`Phase::Emergency`].
//!
//! ### Emergency Phase
//!
//! If, for any of the below reasons:
//!
//! 1. No signed or unsigned solution submitted & Fallback is `None` or failed
//! 2. Internal error
//!
//! A call to `T::ElectionProvider::elect` is made, and `Ok(_)` cannot be returned, then the pallet
//! proceeds to the [`Phase::Emergency`]. During this phase, any solution can be submitted from
//! [`Config::ForceOrigin`], without any checking. Once submitted, the forced solution is kept in
//! [`QueuedSolution`] until the next call to `T::ElectionProvider::elect`, where it is returned and
//! [`Phase`] goes back to `Off`.
//!
//! This implies that the user of this pallet (i.e. a staking pallet) should re-try calling
//! `T::ElectionProvider::elect` in case of error until `OK(_)` is returned.
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
//! ## Accuracy
//!
//! The accuracy of the election is configured via two trait parameters. namely,
//! [`OnChainAccuracyOf`] dictates the accuracy used to compute the on-chain fallback election and
//! [`SolutionAccuracyOf`] is the accuracy that the submitted solutions must adhere to.
//!
//! Note that both accuracies are of great importance. The offchain solution should be as small as
//! possible, reducing solutions size/weight. The on-chain solution can use more space for accuracy,
//! but should still be fast to prevent massively large blocks in case of a fallback.
//!
//! ## Error types
//!
//! This pallet provides a verbose error system to ease future debugging and debugging. The
//! overall hierarchy of errors is as follows:
//!
//! 1. [`pallet::Error`]: These are the errors that can be returned in the dispatchables of the
//!    pallet, either signed or unsigned. Since decomposition with nested enums is not possible
//!    here, they are prefixed with the logical sub-system to which they belong.
//! 2. [`ElectionError`]: These are the errors that can be generated while the pallet is doing
//!    something in automatic scenarios, such as `offchain_worker` or `on_initialize`. These errors
//!    are helpful for logging and are thus nested as:
//!    - [`ElectionError::Miner`]: wraps a [`unsigned::MinerError`].
//!    - [`ElectionError::Feasibility`]: wraps a [`FeasibilityError`].
//!    - [`ElectionError::OnChainFallback`]: wraps a
//!      [`frame_election_provider_support::onchain::Error`].
//!
//! Note that there could be an overlap between these sub-errors. For example, A
//! `SnapshotUnavailable` can happen in both miner and feasibility check phase.
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
//! **Recursive Fallback**: Currently, the fallback is a separate enum. A different and fancier way
//! of doing this would be to have the fallback be another
//! [`frame_election_provider_support::ElectionProvider`]. In this case, this pallet can even have
//! the on-chain election provider as fallback, or special _noop_ fallback that simply returns an
//! error, thus replicating [`FallbackStrategy::Nothing`]. In this case, we won't need the
//! additional config OnChainAccuracy either.
//!
//! **Score based on (byte) size**: We should always prioritize small solutions over bigger ones, if
//! there is a tie. Even more harsh should be to enforce the bound of the `reduce` algorithm.
//!
//! **Make the number of nominators configurable from the runtime**. Remove `sp_npos_elections`
//! dependency from staking and the solution type. It should be generated at runtime, there
//! it should be encoded how many votes each nominators have. Essentially translate
//! <https://github.com/paritytech/substrate/pull/7929> to this pallet.
//!
//! **More accurate weight for error cases**: Both `ElectionDataProvider` and `ElectionProvider`
//! assume no weight is consumed in their functions, when operations fail with `Err`. This can
//! clearly be improved, but not a priority as we generally expect snapshot creation to fail only
//! due to extreme circumstances.
//!
//! **Take into account the encode/decode weight in benchmarks.** Currently, we only take into
//! account the weight of encode/decode in the `submit_unsigned` given its priority. Nonetheless,
//! all operations on the solution and the snapshot are worthy of taking this into account.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_election_provider_support::{onchain, ElectionDataProvider, ElectionProvider, PageIndex};
use frame_support::{
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_none, offchain::SendTransactionTypes};
use sp_arithmetic::{
	traits::{CheckedAdd, Saturating, Zero},
	UpperOf,
};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, ElectionScore, EvaluateSupport, NposSolution,
	PerThing128, Supports, VoteWeight,
};
use sp_runtime::{
	traits::Bounded,
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		TransactionValidityError, ValidTransaction,
	},
	DispatchError, PerThing, Perbill, RuntimeDebug, SaturatedConversion,
};
use sp_std::{convert::TryInto, prelude::*};

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[macro_use]
pub mod helpers;

const LOG_TARGET: &'static str = "runtime::multiblock-election";

pub mod signed;
pub mod types;
pub mod unsigned;
pub mod verifier;
pub mod weights;

pub use signed::{
	BalanceOf, NegativeImbalanceOf, PositiveImbalanceOf, SignedSubmission, SignedSubmissionOf,
	SignedSubmissions, SubmissionIndicesOf,
};
pub use verifier::Verifier;
pub use weights::WeightInfo;

pub use types::*;

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
impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for InitiateEmergencyPhase<T> {
	type DataProvider = T::DataProvider;
	type Error = ElectionError;

	fn elect(remaining: PageIndex) -> Result<(Supports<T::AccountId>, Weight), Self::Error> {
		ensure!(remaining == 0, ElectionError::Fallback("fallback should only have 1 page"));
		log!(warn, "Entering emergency phase.");
		CurrentPhase::<T>::put(Phase::Emergency);
		Err(ElectionError::Fallback("Emergency phase started."))
	}
}

/// Internal errors of the pallet.
///
/// Note that this is different from [`pallet::Error`].
#[derive(Debug, Eq, PartialEq)]
pub enum ElectionError {
	/// An error happened in the feasibility check sub-system.
	Feasibility(verifier::FeasibilityError),
	/// An error in the miner (offchain) sub-system.
	Miner(unsigned::miner::MinerError),
	/// An error in the fallback.
	Fallback(&'static str), // TODO: this error type is hardcoded
	/// An error in the onchain seq-phragmen implementation
	OnChain(onchain::Error),
	/// An error happened in the data provider.
	DataProvider(&'static str),
	/// the corresponding page in the queued supports is not available.
	SupportPageNotAvailable,
}

// TODO: Use a macro for these.
impl From<onchain::Error> for ElectionError {
	fn from(e: onchain::Error) -> Self {
		ElectionError::OnChain(e)
	}
}

impl From<verifier::FeasibilityError> for ElectionError {
	fn from(e: verifier::FeasibilityError) -> Self {
		ElectionError::Feasibility(e)
	}
}

impl From<unsigned::miner::MinerError> for ElectionError {
	fn from(e: unsigned::miner::MinerError) -> Self {
		ElectionError::Miner(e)
	}
}

pub use pallet::*;
#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_election_provider_support::PageIndex;
	use frame_support::{pallet_prelude::*, traits::EstimateCallFee, Twox64Concat};
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::One;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::Event>
			+ TryInto<Event<Self>>;

		/// Currency type.
		type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

		/// Something that can predict the fee of a call. Used to sensibly distribute rewards.
		type EstimateCallFee: EstimateCallFee<Call<Self>, BalanceOf<Self>>;

		/// Duration of the unsigned phase.
		#[pallet::constant]
		type UnsignedPhase: Get<Self::BlockNumber>;
		/// Duration of the signed phase.
		#[pallet::constant]
		type SignedPhase: Get<Self::BlockNumber>;

		/// Maximum number of signed submissions that can be queued.
		///
		/// It is best to avoid adjusting this during an election, as it impacts downstream data
		/// structures. In particular, `SignedSubmissionIndices<T>` is bounded on this value. If you
		/// update this value during an election, you _must_ ensure that
		/// `SignedSubmissionIndices.len()` is less than or equal to the new value. Otherwise,
		/// attempts to submit new solutions may cause a runtime panic.
		#[pallet::constant]
		type SignedMaxSubmissions: Get<u32>;

		/// Maximum weight of a signed solution.
		///
		/// This should probably be similar to [`Config::MinerMaxWeight`].
		#[pallet::constant]
		type SignedMaxWeight: Get<Weight>;

		/// Base reward for a signed solution
		#[pallet::constant]
		type SignedRewardBase: Get<BalanceOf<Self>>;

		/// Base deposit for a signed solution.
		#[pallet::constant]
		type SignedDepositBase: Get<BalanceOf<Self>>;

		/// Per-byte deposit for a signed solution.
		#[pallet::constant]
		type SignedDepositByte: Get<BalanceOf<Self>>;

		/// Per-weight deposit for a signed solution.
		#[pallet::constant]
		type SignedDepositWeight: Get<BalanceOf<Self>>;

		/// The number of snapshot voters to fetch per block.
		///
		/// In the future, this value will make more sense with multi-block snapshot.
		///
		/// Also, note the data type: If the voters are represented by a `u32` in `type
		/// CompactSolution`, the same `u32` is used here to ensure bounds are respected.
		#[pallet::constant]
		// TODO: we could and should use u16 henceforth for voter index.
		type VoterSnapshotPerBlock: Get<SolutionVoterIndexOf<Self>>;
		// TODO: would be good to have the ability to update this on the fly.
		type Pages: Get<PageIndex>;

		/// Handler for the slashed deposits.
		type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// Handler for the rewards.
		type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;

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
			Error = ElectionError, // TODO:
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

			// NOTE: my assumption is that `next_election_prediction` is still the prediction of the
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
				Self::snapshot_metadata()
			);

			match current_phase {
				// from Off to snapshot
				Phase::Off if remaining_blocks <= snapshot_deadline => {
					let remaining_pages = T::Pages::get().saturating_sub(One::one());
					log!(info, "starting snapshot creation[{}]", remaining_pages);
					CurrentPhase::<T>::put(Phase::Snapshot(remaining_pages));
					let _ = Self::create_targets_snapshot();
					Self::create_voters_snapshot_paged(remaining_pages).unwrap();
					0
				},

				// snapshot to signed
				Phase::Snapshot(x) if x > 0 => {
					// we don't check block numbers here, snapshot creation is mandatory.
					let remaining_pages = x.saturating_sub(1);
					log!(info, "continuing snapshot creation[{}]", remaining_pages);
					CurrentPhase::<T>::put(Phase::Snapshot(x));
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

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit a solution for the signed phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// The solution is potentially queued, based on the claimed score and processed at the end
		/// of the signed phase.
		///
		/// A deposit is reserved and recorded for the solution. Based on the outcome, the solution
		/// might be rewarded, slashed, or get all or a part of the deposit back.
		///
		/// # <weight>
		/// Queue size must be provided as witness data.
		/// # </weight>
		#[pallet::weight(T::WeightInfo::submit(*num_signed_submissions))]
		pub fn submit(
			origin: OriginFor<T>,
			raw_solution: Box<PagedRawSolution<SolutionOf<T>>>,
			num_signed_submissions: u32,
		) -> DispatchResult {
			todo!();
			// let who = ensure_signed(origin)?;

			// // ensure witness data is correct.
			// ensure!(
			// 	num_signed_submissions >=
			// 		<SignedSubmissions<T>>::decode_len().unwrap_or_default() as u32,
			// 	Error::<T>::SignedInvalidWitness,
			// );

			// // ensure solution is timely.
			// ensure!(Self::current_phase().is_signed(), Error::<T>::PreDispatchEarlySubmission);

			// // NOTE: this is the only case where having separate snapshot would have been better
			// // because could do just decode_len. But we can create abstractions to do this.

			// // build size. Note: this is not needed for weight calc, thus not input.
			// // unlikely to ever return an error: if phase is signed, snapshot will exist.
			// let size = Self::snapshot_metadata().ok_or(Error::<T>::MissingSnapshotMetadata)?;

			// ensure!(
			// 	Self::feasibility_weight_of(&raw_solution, size) < T::SignedMaxWeight::get(),
			// 	Error::<T>::SignedTooMuchWeight,
			// );

			// // create the submission
			// let deposit = Self::deposit_for(&raw_solution, size);
			// let reward = {
			// 	let call = Call::submit(raw_solution.clone(), num_signed_submissions);
			// 	let call_fee = T::EstimateCallFee::estimate_call_fee(&call, None.into());
			// 	T::SignedRewardBase::get().saturating_add(call_fee)
			// };

			// let submission =
			// 	SignedSubmission { who: who.clone(), deposit, raw_solution: *raw_solution, reward };

			// // insert the submission if the queue has space or it's better than the weakest
			// // eject the weakest if the queue was full
			// let mut signed_submissions = Self::signed_submissions();
			// let maybe_removed = match signed_submissions.insert(submission) {
			// 	// it's an error if we failed to insert a submission: this indicates the queue was
			// 	// full but our solution had insufficient score to eject any solution
			// 	signed::InsertResult::NotInserted => return Err(Error::<T>::SignedQueueFull.into()),
			// 	signed::InsertResult::Inserted => None,
			// 	signed::InsertResult::InsertedEjecting(weakest) => Some(weakest),
			// };

			// // collect deposit. Thereafter, the function cannot fail.
			// T::Currency::reserve(&who, deposit).map_err(|_| Error::<T>::SignedCannotPayDeposit)?;

			// let ejected_a_solution = maybe_removed.is_some();
			// // if we had to remove the weakest solution, unreserve its deposit
			// if let Some(removed) = maybe_removed {
			// 	let _remainder = T::Currency::unreserve(&removed.who, removed.deposit);
			// 	debug_assert!(_remainder.is_zero());
			// }

			// signed_submissions.put();
			// Self::deposit_event(Event::SolutionStored(ElectionCompute::Signed,
			// ejected_a_solution)); Ok(())
		}
	}

	#[pallet::event]
	#[pallet::metadata(
		<T as frame_system::Config>::AccountId = "AccountId",
		BalanceOf<T> = "Balance"
	)]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A solution was stored with the given compute.
		///
		/// If the solution is signed, this means that it hasn't yet been processed. If the
		/// solution is unsigned, this means that it has also been processed.
		///
		/// The `bool` is `true` when a previous solution was ejected to make room for this one.
		SolutionStored(ElectionCompute, bool),
		/// The election has been finalized, with `Some` of the given computation, or else if the
		/// election failed, `None`.
		ElectionFinalized(Option<ElectionCompute>),
		/// An account has been rewarded for their signed submission being finalized.
		Rewarded(<T as frame_system::Config>::AccountId, BalanceOf<T>),
		/// An account has been slashed for submitting an invalid signed submission.
		Slashed(<T as frame_system::Config>::AccountId, BalanceOf<T>),
		/// The signed phase of the given round has started.
		SignedPhaseStarted(u32),
		/// The unsigned phase of the given round has started.
		UnsignedPhaseStarted(u32),
	}

	/// Error of the pallet that can be returned in response to dispatches.
	#[pallet::error]
	pub enum Error<T> {
		/// The queue was full, and the solution was not better than any of the existing ones.
		SignedQueueFull,
		/// The origin failed to pay the deposit.
		SignedCannotPayDeposit,
		/// Witness data to dispatchable is invalid.
		SignedInvalidWitness,
		/// The signed submission consumes too much weight
		SignedTooMuchWeight,
		/// OCW submitted solution for wrong round
		OcwCallWrongEra,
		/// Snapshot metadata should exist but didn't.
		MissingSnapshotMetadata,
		/// `Self::insert_submission` returned an invalid index.
		InvalidSubmissionIndex,
		/// The call is not allowed at this point.
		CallNotAllowed,
		/// Wrong number of pages.
		WrongPageCount,
	}

	#[pallet::origin]
	pub struct Origin<T>(PhantomData<T>);

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

	/// The metadata of the [`RoundSnapshot`]
	///
	/// Only exists when [`Snapshot`] is present.
	#[pallet::storage]
	#[pallet::getter(fn snapshot_metadata)]
	pub type SnapshotMetadata<T: Config> = StorageValue<_, SolutionOrSnapshotSize>;

	/// Desired number of targets to elect for this round.
	///
	/// Only exists when [`Snapshot`] is present.
	#[pallet::storage]
	#[pallet::getter(fn desired_targets)]
	pub type DesiredTargets<T> = StorageValue<_, u32>;

	#[pallet::storage]
	#[pallet::getter(fn paged_voter_snapshot)]
	pub type PagedVoterSnapshot<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, RoundVoterSnapshotPage<T>>;

	#[pallet::storage]
	#[pallet::getter(fn paged_target_snapshot)]
	pub type PagedTargetSnapshot<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, RoundTargetSnapshotPage<T>>;

	// The following storage items collectively comprise `SignedSubmissions<T>`, and should never be
	// accessed independently. Instead, get `Self::signed_submissions()`, modify it as desired, and
	// then do `signed_submissions.put()` when you're done with it.

	/// The next index to be assigned to an incoming signed submission.
	///
	/// Every accepted submission is assigned a unique index; that index is bound to that particular
	/// submission for the duration of the election. On election finalization, the next index is
	/// reset to 0.
	///
	/// We can't just use `SignedSubmissionIndices.len()`, because that's a bounded set; past its
	/// capacity, it will simply saturate. We can't just iterate over `SignedSubmissionsMap`,
	/// because iteration is slow. Instead, we store the value here.
	#[pallet::storage]
	pub(crate) type SignedSubmissionNextIndex<T: Config> = StorageValue<_, u32, ValueQuery>;

	/// A sorted, bounded set of `(score, index)`, where each `index` points to a value in
	/// `SignedSubmissions`.
	///
	/// We never need to process more than a single signed submission at a time. Signed submissions
	/// can be quite large, so we're willing to pay the cost of multiple database accesses to access
	/// them one at a time instead of reading and decoding all of them at once.
	#[pallet::storage]
	pub(crate) type SignedSubmissionIndices<T: Config> =
		StorageValue<_, SubmissionIndicesOf<T>, ValueQuery>;

	/// Unchecked, signed solutions.
	///
	/// Together with `SubmissionIndices`, this stores a bounded set of `SignedSubmissions` while
	/// allowing us to keep only a single one in memory at a time.
	///
	/// Twox note: the key of the map is an auto-incrementing index which users cannot inspect or
	/// affect; we shouldn't need a cryptographically secure hasher.
	#[pallet::storage]
	pub(crate) type SignedSubmissionsMap<T: Config> =
		StorageMap<_, Twox64Concat, u32, SignedSubmissionOf<T>, ValueQuery>;

	// `SignedSubmissions` items end here.

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	/// Creates the target snapshot. Writes new data to:
	///
	/// 1. [`SnapshotMetadata`]
	/// 2. [`PagedTargetSnapshot`]
	/// 3. [`DesiredTargets`]
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_targets_snapshot() -> Result<u32, ElectionError> {
		log!(trace, "creating target snapshot");
		// if requested, get the targets as well.
		let (desired_targets, _) =
			T::DataProvider::desired_targets().map_err(ElectionError::DataProvider)?;
		<DesiredTargets<T>>::put(desired_targets);

		let target_limit = <SolutionTargetIndexOf<T>>::max_value().saturated_into::<usize>();

		let (targets, _) =
			T::DataProvider::targets(Some(target_limit), 0).map_err(ElectionError::DataProvider)?;

		let length = targets.len();
		if length > target_limit {
			debug_assert!(false, "Snapshot limit has not been respected.");
			return Err(ElectionError::DataProvider("Snapshot too big."))
		}

		Self::write_storage_with_pre_allocate(
			&<PagedTargetSnapshot<T>>::hashed_key_for(0),
			targets,
		);

		// update the metadata.
		<SnapshotMetadata<T>>::mutate(|m| {
			let mut new_metadata = m.unwrap_or_default();
			new_metadata.targets = new_metadata.targets.saturating_add(length as u32);
			*m = Some(new_metadata);
		});

		Ok(length as u32)
	}

	/// Creates the voter snapshot. Writes new data to:
	///
	/// 1. [`SnapshotMetadata`]
	/// 2. [`PagedTargetSnapshot`]
	/// 3. [`DesiredTargets`]
	///
	/// Returns `Ok(num_created)` if operation is okay.
	pub fn create_voters_snapshot_paged(remaining: PageIndex) -> Result<u32, ElectionError> {
		log!(trace, "creating paged snapshot, {} pages remaining", remaining);

		let voter_limit = T::VoterSnapshotPerBlock::get().saturated_into::<usize>();
		let (voters, _) = T::DataProvider::voters(Some(voter_limit), remaining)
			.map_err(ElectionError::DataProvider)?;

		// Defensive-only.
		if voters.len() > voter_limit {
			debug_assert!(false, "Snapshot limit has not been respected.");
			return Err(ElectionError::DataProvider("Snapshot too big."))
		}

		// update the metadata.
		<SnapshotMetadata<T>>::mutate(|m| {
			let mut new_metadata = m.unwrap_or_default();
			new_metadata.voters = new_metadata.voters.saturating_add(voters.len() as u32);
			// TODO: just change this to not be an option??
			*m = Some(new_metadata);
		});

		let count = voters.len() as u32;

		// write to storage.
		Self::write_storage_with_pre_allocate(
			&<PagedVoterSnapshot<T>>::hashed_key_for(remaining),
			voters,
		);

		Ok(count)
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
		// TODO: also create a wrapper struct for these storage items.
		<PagedTargetSnapshot<T>>::remove_all(None);
		<PagedVoterSnapshot<T>>::remove_all(None);
		<SnapshotMetadata<T>>::kill();
		<DesiredTargets<T>>::kill();
	}
}

impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for Pallet<T> {
	type Error = ElectionError;
	type DataProvider = T::DataProvider;

	fn elect(remaining: PageIndex) -> Result<(Supports<T::AccountId>, Weight), Self::Error> {
		let ready_page = T::Verifier::get_verified_solution(remaining)
			.ok_or(ElectionError::SupportPageNotAvailable)
			.or_else(|err| {
				// if this is the last page, we might use the fallback to do something.
				if remaining.is_zero() {
					T::Fallback::elect(remaining).map(|(x, _)| x)
				} else {
					err
				}
			})
			.map(|ready_page| {
				// only if this returns `Ok` and it is the last round we clear our data
				if remaining.is_zero() {
					Self::rotate_round()
				}
			})?;

		Ok((ready_page.supports, 0))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		mock::{
			multi_phase_events, roll_to, AccountId, ExtBuilder, MockWeightInfo, MultiPhase,
			Runtime, SignedMaxSubmissions, System, TargetIndex, Targets,
		},
		Phase,
	};
	use frame_election_provider_support::ElectionProvider;
	use frame_support::{assert_noop, assert_ok};
	use sp_npos_elections::Support;

	// TODO: post-condition check that the metadata storage items are consistent: they must all
	// exist at the same time.
	fn ensure_snapshot(exists: bool) {
		assert!(exists ^ !MultiPhase::desired_targets().is_some());
		assert!(exists ^ !<PagedVoterSnapshot<Runtime>>::contains_key(0));
		assert!(exists ^ !<PagedTargetSnapshot<Runtime>>::contains_key(0));
		assert!(exists ^ !MultiPhase::snapshot_metadata().is_some());
	}

	#[test]
	fn phase_rotation_single_page() {
		ExtBuilder::default().build_and_execute(|| {
			// 0 ------- 15 ------- 25 ------- 30 ------- ------- 45 ------- 55 ------- 60
			//           |           |          |                 |           |          |
			//         Signed      Unsigned   Elect             Signed     Unsigned    Elect

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			ensure_snapshot(false);
			assert_eq!(MultiPhase::round(), 1);

			roll_to(4);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			assert_eq!(MultiPhase::round(), 1);

			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert_eq!(multi_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			ensure_snapshot(true);
			assert_eq!(MultiPhase::round(), 1);

			roll_to(24);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			ensure_snapshot(true);
			assert_eq!(MultiPhase::round(), 1);

			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_phase_events(),
				vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)],
			);
			ensure_snapshot(true);

			roll_to(29);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			ensure_snapshot(true);

			roll_to(30);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			ensure_snapshot(true);

			// We close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			ensure_snapshot(true);

			MultiPhase::elect(0).unwrap();

			assert!(MultiPhase::current_phase().is_off());
			ensure_snapshot(false);
			assert_eq!(MultiPhase::round(), 2);

			roll_to(44);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(45);
			assert!(MultiPhase::current_phase().is_signed());

			roll_to(55);
			assert!(MultiPhase::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn phase_rotation_multi_page() {
		ExtBuilder::default().build_and_execute(|| {})
	}

	/*
	#[test]
	fn signed_phase_void() {
		ExtBuilder::default().phases(0, 10).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(19);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(20);
			assert!(MultiPhase::current_phase().is_unsigned_open_at(20));
			assert!(MultiPhase::snapshot().is_some());

			roll_to(30);
			assert!(MultiPhase::current_phase().is_unsigned_open_at(20));

			MultiPhase::elect().unwrap();

			assert!(MultiPhase::current_phase().is_off());
			assert!(MultiPhase::snapshot().is_none());
		});
	}

	#[test]
	fn unsigned_phase_void() {
		ExtBuilder::default().phases(10, 0).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(19);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(20);
			assert!(MultiPhase::current_phase().is_signed());
			assert!(MultiPhase::snapshot().is_some());

			roll_to(30);
			assert!(MultiPhase::current_phase().is_signed());

			assert_ok!(MultiPhase::elect());

			assert!(MultiPhase::current_phase().is_off());
			assert!(MultiPhase::snapshot().is_none());
		});
	}

	#[test]
	fn both_phases_void() {
		ExtBuilder::default().phases(0, 0).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(19);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(20);
			assert!(MultiPhase::current_phase().is_off());

			roll_to(30);
			assert!(MultiPhase::current_phase().is_off());

			// This module is now only capable of doing on-chain backup.
			assert_ok!(MultiPhase::elect());

			assert!(MultiPhase::current_phase().is_off());
		});
	}

	#[test]
	fn early_termination() {
		// An early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// Signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(multi_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert_eq!(MultiPhase::round(), 1);

			// An unexpected call to elect.
			roll_to(20);
			MultiPhase::elect().unwrap();

			// We surely can't have any feasible solutions. This will cause an on-chain election.
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted(1),
					Event::ElectionFinalized(Some(ElectionCompute::OnChain))
				],
			);
			// All storage items must be cleared.
			assert_eq!(MultiPhase::round(), 2);
			assert!(MultiPhase::snapshot().is_none());
			assert!(MultiPhase::snapshot_metadata().is_none());
			assert!(MultiPhase::desired_targets().is_none());
			assert!(MultiPhase::queued_solution().is_none());
			assert!(MultiPhase::signed_submissions().is_empty());
		})
	}

	#[test]
	fn early_termination_with_submissions() {
		// an early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(multi_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert_eq!(MultiPhase::round(), 1);

			// fill the queue with signed submissions
			for s in 0..SignedMaxSubmissions::get() {
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(MultiPhase::submit(
					crate::mock::Origin::signed(99),
					Box::new(solution),
					MultiPhase::signed_submissions().len() as u32
				));
			}

			// an unexpected call to elect.
			roll_to(20);
			assert!(MultiPhase::elect().is_ok());

			// all storage items must be cleared.
			assert_eq!(MultiPhase::round(), 2);
			assert!(MultiPhase::snapshot().is_none());
			assert!(MultiPhase::snapshot_metadata().is_none());
			assert!(MultiPhase::desired_targets().is_none());
			assert!(MultiPhase::queued_solution().is_none());
			assert!(MultiPhase::signed_submissions().is_empty());
		})
	}

	#[test]
	fn fallback_strategy_works() {
		ExtBuilder::default().fallback(FallbackStrategy::OnChain).build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));

			// Zilch solutions thus far.
			let (supports, _) = MultiPhase::elect().unwrap();

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
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));

			// Zilch solutions thus far.
			assert_eq!(MultiPhase::elect().unwrap_err(), ElectionError::NoFallbackConfigured);
		})
	}

	#[test]
	fn snapshot_too_big_failure_onchain_fallback() {
		// the `MockStaking` is designed such that if it has too many targets, it simply fails.
		ExtBuilder::default().build_and_execute(|| {
			Targets::set((0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>());

			// Signed phase failed to open.
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// Unsigned phase failed to open.
			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// On-chain backup works though.
			roll_to(29);
			let (supports, _) = MultiPhase::elect().unwrap();
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
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// Unsigned phase failed to open.
			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			roll_to(29);
			let err = MultiPhase::elect().unwrap_err();
			assert_eq!(err, ElectionError::NoFallbackConfigured);
			assert_eq!(MultiPhase::current_phase(), Phase::Emergency);
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
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);

			assert_eq!(
				MultiPhase::snapshot_metadata().unwrap(),
				SolutionOrSnapshotSize { voters: 2, targets: 4 }
			);
		})
	}

	#[test]
	fn untrusted_score_verification_is_respected() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);

			let (solution, _) = MultiPhase::mine_solution(2).unwrap();
			// Default solution has a score of [50, 100, 5000].
			assert_eq!(solution.score, [50, 100, 5000]);

			<MinimumUntrustedScore<Runtime>>::put([49, 0, 0]);
			assert_ok!(MultiPhase::feasibility_check(solution.clone(), ElectionCompute::Signed));

			<MinimumUntrustedScore<Runtime>>::put([51, 0, 0]);
			assert_noop!(
				MultiPhase::feasibility_check(solution, ElectionCompute::Signed),
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
