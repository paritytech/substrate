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
//! ### Signed Phase
//!
//!	In the signed phase, solutions (of type [`RawSolution`]) are submitted and queued on chain. A
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
//! [`FallbackStrategy::Nothing`] should probably only be used for testing, and returns an error.
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
//! [`CompactAccuracyOf`] is the accuracy that the submitted solutions must adhere to.
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
//! **Challenge Phase**. We plan adding a third phase to the pallet, called the challenge phase.
//! This is phase in which no further solutions are processed, and the current best solution might
//! be challenged by anyone (signed or unsigned). The main plan here is to enforce the solution to
//! be PJR. Checking PJR on-chain is quite expensive, yet proving that a solution is **not** PJR is
//! rather cheap. If a queued solution is challenged:
//!
//! 1. We must surely slash whoever submitted that solution (might be a challenge for unsigned
//!    solutions).
//! 2. It is probably fine to fallback to the on-chain election, as we expect this to happen rarely.
//!
//! **Bailing out**. The functionality of bailing out of a queued solution is nice. A miner can
//! submit a solution as soon as they _think_ it is high probability feasible, and do the checks
//! afterwards, and remove their solution (for a small cost of probably just transaction fees, or a
//! portion of the bond).
//!
//! **Conditionally open unsigned phase**: Currently, the unsigned phase is always opened. This is
//! useful because an honest validation will run our OCW code, which should be good enough to trump
//! a mediocre or malicious signed submission (assuming in the absence of honest signed bots). If an
//! when the signed submissions are checked against an absolute measure (e.g. PJR), then we can only
//! open the unsigned phase in extreme conditions (i.e. "not good signed solution received") to
//! spare some work in the validators
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
//! dependency from staking and the compact solution type. It should be generated at runtime, there
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
use frame_support::{
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{Currency, Get, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_none, offchain::SendTransactionTypes};
use frame_election_provider_support::{ElectionDataProvider, ElectionProvider, onchain};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, CompactSolution, ElectionScore,
	EvaluateSupport, PerThing128, Supports, VoteWeight,
};
use sp_runtime::{
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		TransactionValidityError, ValidTransaction,
	},
	DispatchError, PerThing, Perbill, RuntimeDebug, SaturatedConversion,
	traits::Bounded,
};
use sp_std::{
	convert::TryInto,
	prelude::*,
};
use sp_arithmetic::{
	UpperOf,
	traits::{Zero, CheckedAdd},
};

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarking;
#[cfg(test)]
mod mock;
#[macro_use]
pub mod helpers;

const LOG_TARGET: &'static str = "runtime::election-provider";

pub mod unsigned;
pub mod weights;

/// The weight declaration of the pallet.
pub use weights::WeightInfo;

/// The compact solution type used by this crate.
pub type CompactOf<T> = <T as Config>::CompactSolution;

/// The voter index. Derived from [`CompactOf`].
pub type CompactVoterIndexOf<T> = <CompactOf<T> as CompactSolution>::Voter;
/// The target index. Derived from [`CompactOf`].
pub type CompactTargetIndexOf<T> = <CompactOf<T> as CompactSolution>::Target;
/// The accuracy of the election, when submitted from offchain. Derived from [`CompactOf`].
pub type CompactAccuracyOf<T> = <CompactOf<T> as CompactSolution>::Accuracy;
/// The accuracy of the election, when computed on-chain. Equal to [`Config::OnChainAccuracy`].
pub type OnChainAccuracyOf<T> = <T as Config>::OnChainAccuracy;

/// Wrapper type that implements the configurations needed for the on-chain backup.
struct OnChainConfig<T: Config>(sp_std::marker::PhantomData<T>);
impl<T: Config> onchain::Config for OnChainConfig<T> {
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type BlockWeights = T::BlockWeights;
	type Accuracy = T::OnChainAccuracy;
	type DataProvider = T::DataProvider;
}

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
}

impl BenchmarkingConfig for () {
	const VOTERS: [u32; 2] = [4000, 6000];
	const TARGETS: [u32; 2] = [1000, 1600];
	const ACTIVE_VOTERS: [u32; 2] = [1000, 3000];
	const DESIRED_TARGETS: [u32; 2] = [400, 800];
}

/// Current phase of the pallet.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Phase<Bn> {
	/// Nothing, the election is not happening.
	Off,
	/// Signed phase is open.
	Signed,
	/// Unsigned phase. First element is whether it is active or not, second the starting block
	/// number.
	///
	/// We do not yet check whether the unsigned phase is active or passive. The intent is for the
	/// blockchain to be able to declare: "I believe that there exists an adequate signed solution,"
	/// advising validators not to bother running the unsigned offchain worker.
	///
	/// As validator nodes are free to edit their OCW code, they could simply ignore this advisory
	/// and always compute their own solution. However, by default, when the unsigned phase is passive,
	/// the offchain workers will not bother running.
	Unsigned((bool, Bn)),
}

impl<Bn> Default for Phase<Bn> {
	fn default() -> Self {
		Phase::Off
	}
}

impl<Bn: PartialEq + Eq> Phase<Bn> {
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
		matches!(self, Phase::Unsigned((true, real)) if *real == at)
	}

	/// Whether the phase is unsigned and open or not.
	pub fn is_unsigned_open(&self) -> bool {
		matches!(self, Phase::Unsigned((true, _)))
	}

	/// Whether the phase is off or not.
	pub fn is_off(&self) -> bool {
		matches!(self, Phase::Off)
	}
}

/// A configuration for the pallet to indicate what should happen in the case of a fallback i.e.
/// reaching a call to `elect` with no good solution.
#[cfg_attr(test, derive(Clone))]
pub enum FallbackStrategy {
	/// Run a on-chain sequential phragmen.
	///
	/// This might burn the chain for a few minutes due to a stall, but is generally a safe
	/// approach to maintain a sensible validator set.
	OnChain,
	/// Nothing. Return an error.
	Nothing,
}

/// The type of `Computation` that provided this election data.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum ElectionCompute {
	/// Election was computed on-chain.
	OnChain,
	/// Election was computed with a signed submission.
	Signed,
	/// Election was computed with an unsigned submission.
	Unsigned,
}

impl Default for ElectionCompute {
	fn default() -> Self {
		ElectionCompute::OnChain
	}
}

/// A raw, unchecked solution.
///
/// This is what will get submitted to the chain.
///
/// Such a solution should never become effective in anyway before being checked by the
/// `Pallet::feasibility_check`
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct RawSolution<C> {
	/// Compact election edges.
	pub compact: C,
	/// The _claimed_ score of the solution.
	pub score: ElectionScore,
	/// The round at which this solution should be submitted.
	pub round: u32,
}

impl<C: Default> Default for RawSolution<C> {
	fn default() -> Self {
		// Round 0 is always invalid, only set this to 1.
		Self { round: 1, compact: Default::default(), score: Default::default() }
	}
}

/// A checked solution, ready to be enacted.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct ReadySolution<A> {
	/// The final supports of the solution.
	///
	/// This is target-major vector, storing each winners, total backing, and each individual
	/// backer.
	pub supports: Supports<A>,
	/// The score of the solution.
	///
	/// This is needed to potentially challenge the solution.
	pub score: ElectionScore,
	/// How this election was computed.
	pub compute: ElectionCompute,
}

/// A snapshot of all the data that is needed for en entire round. They are provided by
/// [`ElectionDataProvider`] and are kept around until the round is finished.
///
/// These are stored together because they are often accessed together.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct RoundSnapshot<A> {
	/// All of the voters.
	pub voters: Vec<(A, VoteWeight, Vec<A>)>,
	/// All of the targets.
	pub targets: Vec<A>,
}

/// Encodes the length of a solution or a snapshot.
///
/// This is stored automatically on-chain, and it contains the **size of the entire snapshot**.
/// This is also used in dispatchables as weight witness data and should **only contain the size of
/// the presented solution**, not the entire snapshot.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, Default)]
pub struct SolutionOrSnapshotSize {
	/// The length of voters.
	#[codec(compact)]
	pub voters: u32,
	/// The length of targets.
	#[codec(compact)]
	pub targets: u32,
}

/// Internal errors of the pallet.
///
/// Note that this is different from [`pallet::Error`].
#[derive(Debug, Eq, PartialEq)]
pub enum ElectionError {
	/// An error happened in the feasibility check sub-system.
	Feasibility(FeasibilityError),
	/// An error in the miner (offchain) sub-system.
	Miner(unsigned::MinerError),
	/// An error in the on-chain fallback.
	OnChainFallback(onchain::Error),
	/// An error happened in the data provider.
	DataProvider(&'static str),
	/// No fallback is configured. This is a special case.
	NoFallbackConfigured,
}

impl From<onchain::Error> for ElectionError {
	fn from(e: onchain::Error) -> Self {
		ElectionError::OnChainFallback(e)
	}
}

impl From<FeasibilityError> for ElectionError {
	fn from(e: FeasibilityError) -> Self {
		ElectionError::Feasibility(e)
	}
}

impl From<unsigned::MinerError> for ElectionError {
	fn from(e: unsigned::MinerError) -> Self {
		ElectionError::Miner(e)
	}
}

/// Errors that can happen in the feasibility check.
#[derive(Debug, Eq, PartialEq)]
pub enum FeasibilityError {
	/// Wrong number of winners presented.
	WrongWinnerCount,
	/// The snapshot is not available.
	///
	/// Kinda defensive: The pallet should technically never attempt to do a feasibility check when
	/// no snapshot is present.
	SnapshotUnavailable,
	/// Internal error from the election crate.
	NposElection(sp_npos_elections::Error),
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
}

impl From<sp_npos_elections::Error> for FeasibilityError {
	fn from(e: sp_npos_elections::Error) -> Self {
		FeasibilityError::NposElection(e)
	}
}

pub use pallet::*;
#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>> {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event> + TryInto<Event<Self>>;

		/// Currency type.
		type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

		/// Duration of the unsigned phase.
		#[pallet::constant]
		type UnsignedPhase: Get<Self::BlockNumber>;
		/// Duration of the signed phase.
		#[pallet::constant]
		type SignedPhase: Get<Self::BlockNumber>;

		/// The minimum amount of improvement to the solution score that defines a solution as
		/// "better" (in any phase).
		#[pallet::constant]
		type SolutionImprovementThreshold: Get<Perbill>;

		/// The repeat threshold of the offchain worker.
		///
		/// For example, if it is 5, that means that at least 5 blocks will elapse between attempts
		/// to submit the worker's solution.
		#[pallet::constant]
		type OffchainRepeat: Get<Self::BlockNumber>;

		/// The priority of the unsigned transaction submitted in the unsigned-phase
		type MinerTxPriority: Get<TransactionPriority>;
		/// Maximum number of iteration of balancing that will be executed in the embedded miner of
		/// the pallet.
		type MinerMaxIterations: Get<u32>;

		/// Maximum weight that the miner should consume.
		///
		/// The miner will ensure that the total weight of the unsigned solution will not exceed
		/// this value, based on [`WeightInfo::submit_unsigned`].
		type MinerMaxWeight: Get<Weight>;

		/// Maximum length (bytes) that the mined solution should consume.
		///
		/// The miner will ensure that the total length of the unsigned solution will not exceed
		/// this value.
		type MinerMaxLength: Get<u32>;

		/// Something that will provide the election data.
		type DataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;

		/// The compact solution type
		type CompactSolution: codec::Codec
			+ Default
			+ PartialEq
			+ Eq
			+ Clone
			+ sp_std::fmt::Debug
			+ CompactSolution;

		/// Accuracy used for fallback on-chain election.
		type OnChainAccuracy: PerThing128;

		/// Configuration for the fallback
		type Fallback: Get<FallbackStrategy>;

		/// The configuration of benchmarking.
		type BenchmarkingConfig: BenchmarkingConfig;

		/// The weight of the pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let next_election = T::DataProvider::next_election_prediction(now).max(now);

			let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
			let unsigned_deadline = T::UnsignedPhase::get();

			let remaining = next_election - now;
			let current_phase = Self::current_phase();

			match current_phase {
				Phase::Off if remaining <= signed_deadline && remaining > unsigned_deadline => {
					// NOTE: if signed-phase length is zero, second part of the if-condition fails.
					match Self::on_initialize_open_signed() {
						Ok(snap_weight) => {
							log!(info, "Starting signed phase round {}.", Self::round());
							T::WeightInfo::on_initialize_open_signed().saturating_add(snap_weight)
						}
						Err(why) => {
							// not much we can do about this at this point.
							log!(warn, "failed to open signed phase due to {:?}", why);
							T::WeightInfo::on_initialize_nothing()
							// NOTE: ^^ The trait specifies that this is a noop in terms of weight
							// in case of error.
						}
					}
				}
				Phase::Signed | Phase::Off
					if remaining <= unsigned_deadline && remaining > Zero::zero() =>
				{
					// determine if followed by signed or not.
					let (need_snapshot, enabled, signed_weight) = if current_phase == Phase::Signed {
						// followed by a signed phase: close the signed phase, no need for snapshot.
						// TODO: proper weight https://github.com/paritytech/substrate/pull/7910.
						(false, true, Weight::zero())
					} else {
						// no signed phase: create a new snapshot, definitely `enable` the unsigned
						// phase.
						(true, true, Weight::zero())
					};

					match Self::on_initialize_open_unsigned(need_snapshot, enabled, now) {
						Ok(snap_weight) => {
							log!(info, "Starting unsigned phase({}).", enabled);
							let base_weight = if need_snapshot {
								T::WeightInfo::on_initialize_open_unsigned_with_snapshot()
							} else {
								T::WeightInfo::on_initialize_open_unsigned_without_snapshot()
							};

							base_weight.saturating_add(snap_weight).saturating_add(signed_weight)
						}
						Err(why) => {
							// not much we can do about this at this point.
							log!(warn, "failed to open unsigned phase due to {:?}", why);
							T::WeightInfo::on_initialize_nothing()
							// NOTE: ^^ The trait specifies that this is a noop in terms of weight
							// in case of error.
						}
					}
				}
				_ => T::WeightInfo::on_initialize_nothing(),
			}
		}

		fn offchain_worker(now: T::BlockNumber) {
			use sp_runtime::offchain::storage_lock::{StorageLock, BlockAndTime};

			// create a lock with the maximum deadline of number of blocks in the unsigned phase.
			// This should only come useful in an **abrupt** termination of execution, otherwise the
			// guard will be dropped upon successful execution.
			let mut lock = StorageLock::<BlockAndTime<frame_system::Pallet::<T>>>::with_block_deadline(
				unsigned::OFFCHAIN_LOCK,
				T::UnsignedPhase::get().saturated_into(),
			);

			match lock.try_lock() {
				Ok(_guard) => {
					Self::do_synchronized_offchain_worker(now);
				},
				Err(deadline) => {
					log!(debug, "offchain worker lock not released, deadline is {:?}", deadline);
				}
			};
		}

		fn integrity_test() {
			use sp_std::mem::size_of;
			// The index type of both voters and targets need to be smaller than that of usize (very
			// unlikely to be the case, but anyhow).
			assert!(size_of::<CompactVoterIndexOf<T>>() <= size_of::<usize>());
			assert!(size_of::<CompactTargetIndexOf<T>>() <= size_of::<usize>());

			// ----------------------------
			// based on the requirements of [`sp_npos_elections::Assignment::try_normalize`].
			let max_vote: usize = <CompactOf<T> as CompactSolution>::LIMIT;

			// 1. Maximum sum of [ChainAccuracy; 16] must fit into `UpperOf<ChainAccuracy>`..
			let maximum_chain_accuracy: Vec<UpperOf<OnChainAccuracyOf<T>>> = (0..max_vote)
				.map(|_| {
					<UpperOf<OnChainAccuracyOf<T>>>::from(
						<OnChainAccuracyOf<T>>::one().deconstruct(),
					)
				})
				.collect();
			let _: UpperOf<OnChainAccuracyOf<T>> = maximum_chain_accuracy
				.iter()
				.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());

			// 2. Maximum sum of [CompactAccuracy; 16] must fit into `UpperOf<OffchainAccuracy>`.
			let maximum_chain_accuracy: Vec<UpperOf<CompactAccuracyOf<T>>> = (0..max_vote)
				.map(|_| {
					<UpperOf<CompactAccuracyOf<T>>>::from(
						<CompactAccuracyOf<T>>::one().deconstruct(),
					)
				})
				.collect();
			let _: UpperOf<CompactAccuracyOf<T>> = maximum_chain_accuracy
				.iter()
				.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());

			// We only accept data provider who's maximum votes per voter matches our
			// `T::CompactSolution`'s `LIMIT`.
			//
			// NOTE that this pallet does not really need to enforce this in runtime. The compact
			// solution cannot represent any voters more than `LIMIT` anyhow.
			assert_eq!(
				<T::DataProvider as ElectionDataProvider<T::AccountId, T::BlockNumber>>::MAXIMUM_VOTES_PER_VOTER,
				<CompactOf<T> as CompactSolution>::LIMIT as u32,
			);
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit a solution for the unsigned phase.
		///
		/// The dispatch origin fo this call must be __none__.
		///
		/// This submission is checked on the fly. Moreover, this unsigned solution is only
		/// validated when submitted to the pool from the **local** node. Effectively, this means
		/// that only active validators can submit this transaction when authoring a block (similar
		/// to an inherent).
		///
		/// To prevent any incorrect solution (and thus wasted time/weight), this transaction will
		/// panic if the solution submitted by the validator is invalid in any way, effectively
		/// putting their authoring reward at risk.
		///
		/// No deposit or reward is associated with this submission.
		#[pallet::weight(T::WeightInfo::submit_unsigned(
			witness.voters,
			witness.targets,
			solution.compact.voter_count() as u32,
			solution.compact.unique_targets().len() as u32
		))]
		pub fn submit_unsigned(
			origin: OriginFor<T>,
			solution: RawSolution<CompactOf<T>>,
			witness: SolutionOrSnapshotSize,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let error_message =
				"Invalid unsigned submission must produce invalid block and \
				 deprive validator from their authoring reward.";

			// Check score being an improvement, phase, and desired targets.
			Self::unsigned_pre_dispatch_checks(&solution).expect(error_message);

			// ensure witness was correct.
			let SolutionOrSnapshotSize { voters, targets } =
				Self::snapshot_metadata().expect(error_message);

			// NOTE: we are asserting, not `ensure`ing -- we want to panic here.
			assert!(voters as u32 == witness.voters, "{}", error_message);
			assert!(targets as u32 == witness.targets, "{}", error_message);

			let ready =
				Self::feasibility_check(solution, ElectionCompute::Unsigned).expect(error_message);

			// store the newly received solution.
			log!(info, "queued unsigned solution with score {:?}", ready.score);
			<QueuedSolution<T>>::put(ready);
			Self::deposit_event(Event::SolutionStored(ElectionCompute::Unsigned));

			Ok(None.into())
		}
	}

	#[pallet::event]
	#[pallet::metadata(<T as frame_system::Config>::AccountId = "AccountId")]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A solution was stored with the given compute.
		///
		/// If the solution is signed, this means that it hasn't yet been processed. If the
		/// solution is unsigned, this means that it has also been processed.
		SolutionStored(ElectionCompute),
		/// The election has been finalized, with `Some` of the given computation, or else if the
		/// election failed, `None`.
		ElectionFinalized(Option<ElectionCompute>),
		/// An account has been rewarded for their signed submission being finalized.
		Rewarded(<T as frame_system::Config>::AccountId),
		/// An account has been slashed for submitting an invalid signed submission.
		Slashed(<T as frame_system::Config>::AccountId),
		/// The signed phase of the given round has started.
		SignedPhaseStarted(u32),
		/// The unsigned phase of the given round has started.
		UnsignedPhaseStarted(u32),
	}

	/// Error of the pallet that can be returned in response to dispatches.
	#[pallet::error]
	pub enum Error<T> {
		/// Submission was too early.
		PreDispatchEarlySubmission,
		/// Wrong number of winners presented.
		PreDispatchWrongWinnerCount,
		/// Submission was too weak, score-wise.
		PreDispatchWeakSubmission,
		/// OCW submitted solution for wrong round
		OcwCallWrongEra,
	}

	#[pallet::origin]
	pub struct Origin<T>(PhantomData<T>);
	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			if let Call::submit_unsigned(solution, _) = call {
				// discard solution not coming from the local OCW.
				match source {
					TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ }
					_ => {
						return InvalidTransaction::Call.into();
					}
				}

				let _ = Self::unsigned_pre_dispatch_checks(solution)
					.map_err(|err| {
						log!(error, "unsigned transaction validation failed due to {:?}", err);
						err
					})
					.map_err(dispatch_error_to_invalid)?;

				ValidTransaction::with_tag_prefix("OffchainElection")
					// The higher the score[0], the better a solution is.
					.priority(
						T::MinerTxPriority::get().saturating_add(
							solution.score[0].saturated_into()
						),
					)
					// used to deduplicate unsigned solutions: each validator should produce one
					// solution per round at most, and solutions are not propagate.
					.and_provides(solution.round)
					// transaction should stay in the pool for the duration of the unsigned phase.
					.longevity(T::UnsignedPhase::get().saturated_into::<u64>())
					// We don't propagate this. This can never be validated at a remote node.
					.propagate(false)
					.build()
			} else {
				InvalidTransaction::Call.into()
			}
		}

		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			if let Call::submit_unsigned(solution, _) = call {
				Self::unsigned_pre_dispatch_checks(solution)
					.map_err(dispatch_error_to_invalid)
					.map_err(Into::into)
			} else {
				Err(InvalidTransaction::Call.into())
			}
		}
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

	/// Current best solution, signed or unsigned, queued to be returned upon `elect`.
	#[pallet::storage]
	#[pallet::getter(fn queued_solution)]
	pub type QueuedSolution<T: Config> = StorageValue<_, ReadySolution<T::AccountId>>;

	/// Snapshot data of the round.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
	#[pallet::storage]
	#[pallet::getter(fn snapshot)]
	pub type Snapshot<T: Config> = StorageValue<_, RoundSnapshot<T::AccountId>>;

	/// Desired number of targets to elect for this round.
	///
	/// Only exists when [`Snapshot`] is present.
	#[pallet::storage]
	#[pallet::getter(fn desired_targets)]
	pub type DesiredTargets<T> = StorageValue<_, u32>;

	/// The metadata of the [`RoundSnapshot`]
	///
	/// Only exists when [`Snapshot`] is present.
	#[pallet::storage]
	#[pallet::getter(fn snapshot_metadata)]
	pub type SnapshotMetadata<T: Config> = StorageValue<_, SolutionOrSnapshotSize>;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	/// Internal logic of the offchain worker, to be executed only when the offchain lock is
	/// acquired with success.
	fn do_synchronized_offchain_worker(now: T::BlockNumber) {
		log!(trace, "lock for offchain worker acquired.");
		match Self::current_phase() {
			Phase::Unsigned((true, opened)) if opened == now => {
				// mine a new solution, cache it, and attempt to submit it
				let initial_output = Self::ensure_offchain_repeat_frequency(now).and_then(|_| {
					Self::mine_check_save_submit()
				});
				log!(debug, "initial offchain thread output: {:?}", initial_output);
			}
			Phase::Unsigned((true, opened)) if opened < now => {
				// try and resubmit the cached solution, and recompute ONLY if it is not
				// feasible.
				let resubmit_output = Self::ensure_offchain_repeat_frequency(now).and_then(|_| {
					Self::restore_or_compute_then_maybe_submit()
				});
				log!(debug, "resubmit offchain thread output: {:?}", resubmit_output);
			}
			_ => {}
		}

		// after election finalization, clear OCW solution storage.
		if <frame_system::Pallet<T>>::events()
			.into_iter()
			.filter_map(|event_record| {
				let local_event = <T as Config>::Event::from(event_record.event);
				local_event.try_into().ok()
			})
			.any(|event| {
				matches!(event, Event::ElectionFinalized(_))
			})
		{
			unsigned::kill_ocw_solution::<T>();
		}
	}

	/// Logic for [`<Pallet as Hooks>::on_initialize`] when signed phase is being opened.
	///
	/// This is decoupled for easy weight calculation.
	///
	/// Returns `Ok(snapshot_weight)` if success, where `snapshot_weight` is the weight that
	/// needs to recorded for the creation of snapshot.
	pub(crate) fn on_initialize_open_signed() -> Result<Weight, ElectionError> {
		let weight = Self::create_snapshot()?;
		<CurrentPhase<T>>::put(Phase::Signed);
		Self::deposit_event(Event::SignedPhaseStarted(Self::round()));
		Ok(weight.saturating_add(T::DbWeight::get().writes(1)))
	}

	/// Logic for [`<Pallet as Hooks<T>>::on_initialize`] when unsigned phase is being opened.
	///
	/// This is decoupled for easy weight calculation.
	///
	/// Returns `Ok(snapshot_weight)` if success, where `snapshot_weight` is the weight that
	/// needs to recorded for the creation of snapshot.
	pub(crate) fn on_initialize_open_unsigned(
		need_snapshot: bool,
		enabled: bool,
		now: T::BlockNumber,
	) -> Result<Weight, ElectionError> {
		let weight = if need_snapshot {
			// if not being followed by a signed phase, then create the snapshots.
			debug_assert!(Self::snapshot().is_none());
			Self::create_snapshot()?
		} else {
			0
		};

		<CurrentPhase<T>>::put(Phase::Unsigned((enabled, now)));
		Self::deposit_event(Event::UnsignedPhaseStarted(Self::round()));
		Ok(weight.saturating_add(T::DbWeight::get().writes(1)))
	}

	/// Creates the snapshot. Writes new data to:
	///
	/// 1. [`SnapshotMetadata`]
	/// 2. [`RoundSnapshot`]
	/// 3. [`DesiredTargets`]
	///
	/// Returns `Ok(consumed_weight)` if operation is okay.
	pub(crate) fn create_snapshot() -> Result<Weight, ElectionError> {
		let target_limit = <CompactTargetIndexOf<T>>::max_value().saturated_into::<usize>();
		let voter_limit = <CompactVoterIndexOf<T>>::max_value().saturated_into::<usize>();

		let (targets, w1) =
			T::DataProvider::targets(Some(target_limit)).map_err(ElectionError::DataProvider)?;
		let (voters, w2) =
			T::DataProvider::voters(Some(voter_limit)).map_err(ElectionError::DataProvider)?;
		let (desired_targets, w3) =
			T::DataProvider::desired_targets().map_err(ElectionError::DataProvider)?;

		// defensive-only
		if targets.len() > target_limit || voters.len() > voter_limit {
			debug_assert!(false, "Snapshot limit has not been respected.");
			return Err(ElectionError::DataProvider("Snapshot too big for submission."));
		}

		// only write snapshot if all existed.
		<SnapshotMetadata<T>>::put(SolutionOrSnapshotSize {
			voters: voters.len() as u32,
			targets: targets.len() as u32,
		});
		<DesiredTargets<T>>::put(desired_targets);
		<Snapshot<T>>::put(RoundSnapshot { voters, targets });
		Ok(w1.saturating_add(w2).saturating_add(w3).saturating_add(T::DbWeight::get().writes(3)))
	}

	/// Kill everything created by [`Pallet::create_snapshot`].
	pub(crate) fn kill_snapshot() {
		<Snapshot<T>>::kill();
		<SnapshotMetadata<T>>::kill();
		<DesiredTargets<T>>::kill();
	}

	/// Checks the feasibility of a solution.
	fn feasibility_check(
		solution: RawSolution<CompactOf<T>>,
		compute: ElectionCompute,
	) -> Result<ReadySolution<T::AccountId>, FeasibilityError> {
		let RawSolution { compact, score, round } = solution;

		// first, check round.
		ensure!(Self::round() == round, FeasibilityError::InvalidRound);

		// winners are not directly encoded in the solution.
		let winners = compact.unique_targets();

		let desired_targets =
			Self::desired_targets().ok_or(FeasibilityError::SnapshotUnavailable)?;

		// NOTE: this is a bit of duplicate, but we keep it around for veracity. The unsigned path
		// already checked this in `unsigned_per_dispatch_checks`. The signed path *could* check it
		// upon arrival, thus we would then remove it here. Given overlay it is cheap anyhow
		ensure!(winners.len() as u32 == desired_targets, FeasibilityError::WrongWinnerCount);

		// read the entire snapshot.
		let RoundSnapshot { voters: snapshot_voters, targets: snapshot_targets } =
			Self::snapshot().ok_or(FeasibilityError::SnapshotUnavailable)?;

		// ----- Start building. First, we need some closures.
		let cache = helpers::generate_voter_cache::<T>(&snapshot_voters);
		let voter_at = helpers::voter_at_fn::<T>(&snapshot_voters);
		let target_at = helpers::target_at_fn::<T>(&snapshot_targets);
		let voter_index = helpers::voter_index_fn_usize::<T>(&cache);

		// first, make sure that all the winners are sane.
		// OPTIMIZATION: we could first build the assignments, and then extract the winners directly
		// from that, as that would eliminate a little bit of duplicate work. For now, we keep them
		// separate: First extract winners separately from compact, and then assignments. This is
		// also better, because we can reject solutions that don't meet `desired_targets` early on.
		let winners = winners
			.into_iter()
			.map(|i| target_at(i).ok_or(FeasibilityError::InvalidWinner))
			.collect::<Result<Vec<T::AccountId>, FeasibilityError>>()?;

		// Then convert compact -> assignment. This will fail if any of the indices are gibberish.
		let assignments = compact
			.into_assignment(voter_at, target_at)
			.map_err::<FeasibilityError, _>(Into::into)?;

		// Ensure that assignments is correct.
		let _ = assignments
			.iter()
			.map(|ref assignment| {
				// check that assignment.who is actually a voter (defensive-only).
				// NOTE: while using the index map from `voter_index` is better than a blind linear
				// search, this *still* has room for optimization. Note that we had the index when
				// we did `compact -> assignment` and we lost it. Ideal is to keep the index around.

				// defensive-only: must exist in the snapshot.
				let snapshot_index =
					voter_index(&assignment.who).ok_or(FeasibilityError::InvalidVoter)?;
				// defensive-only: index comes from the snapshot, must exist.
				let (_voter, _stake, targets) =
					snapshot_voters.get(snapshot_index).ok_or(FeasibilityError::InvalidVoter)?;

				// check that all of the targets are valid based on the snapshot.
				if assignment.distribution.iter().any(|(d, _)| !targets.contains(d)) {
					return Err(FeasibilityError::InvalidVote);
				}
				Ok(())
			})
			.collect::<Result<(), FeasibilityError>>()?;

		// ----- Start building support. First, we need one more closure.
		let stake_of = helpers::stake_of_fn::<T>(&snapshot_voters, &cache);

		// This might fail if the normalization fails. Very unlikely. See `integrity_test`.
		let staked_assignments = assignment_ratio_to_staked_normalized(assignments, stake_of)
			.map_err::<FeasibilityError, _>(Into::into)?;

		// This might fail if one of the voter edges is pointing to a non-winner, which is not
		// really possible anymore because all the winners come from the same `compact`.
		let supports = sp_npos_elections::to_supports(&winners, &staked_assignments)
			.map_err::<FeasibilityError, _>(Into::into)?;

		// Finally, check that the claimed score was indeed correct.
		let known_score = (&supports).evaluate();
		ensure!(known_score == score, FeasibilityError::InvalidScore);

		Ok(ReadySolution { supports, compute, score })
	}

	/// Perform the tasks to be done after a new `elect` has been triggered:
	///
	/// 1. Increment round.
	/// 2. Change phase to [`Phase::Off`]
	/// 3. Clear all snapshot data.
	fn post_elect() {
		// inc round
		<Round<T>>::mutate(|r| *r = *r + 1);

		// change phase
		<CurrentPhase<T>>::put(Phase::Off);

		// kill snapshots
		Self::kill_snapshot();
	}

	/// On-chain fallback of election.
	fn onchain_fallback() -> Result<(Supports<T::AccountId>, Weight), ElectionError> {
		<onchain::OnChainSequentialPhragmen<OnChainConfig<T>> as ElectionProvider<
			T::AccountId,
			T::BlockNumber,
		>>::elect()
		.map_err(Into::into)
	}

	fn do_elect() -> Result<(Supports<T::AccountId>, Weight), ElectionError> {
		<QueuedSolution<T>>::take()
			.map_or_else(
				|| match T::Fallback::get() {
					FallbackStrategy::OnChain => Self::onchain_fallback()
						.map(|(s, w)| (s, w, ElectionCompute::OnChain))
						.map_err(Into::into),
					FallbackStrategy::Nothing => Err(ElectionError::NoFallbackConfigured),
				},
				|ReadySolution { supports, compute, .. }| Ok((
					supports,
					T::WeightInfo::elect_queued(),
					compute
				)),
			)
			.map(|(supports, weight, compute)| {
				Self::deposit_event(Event::ElectionFinalized(Some(compute)));
				if Self::round() != 1 {
					log!(info, "Finalized election round with compute {:?}.", compute);
				}
				(supports, weight)
			})
			.map_err(|err| {
				Self::deposit_event(Event::ElectionFinalized(None));
				if Self::round() != 1 {
					log!(warn, "Failed to finalize election round. reason {:?}", err);
				}
				err
			})
	}
}

impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for Pallet<T> {
	type Error = ElectionError;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<(Supports<T::AccountId>, Weight), Self::Error> {
		let outcome_and_weight = Self::do_elect();
		// IMPORTANT: regardless of if election was `Ok` or `Err`, we shall do some cleanup.
		Self::post_elect();
		outcome_and_weight
	}
}

/// convert a DispatchError to a custom InvalidTransaction with the inner code being the error
/// number.
pub fn dispatch_error_to_invalid(error: DispatchError) -> InvalidTransaction {
	let error_number = match error {
		DispatchError::Module { error, .. } => error,
		_ => 0,
	};
	InvalidTransaction::Custom(error_number)
}

#[cfg(test)]
mod feasibility_check {
	//! All of the tests here should be dedicated to only testing the feasibility check and nothing
	//! more. The best way to audit and review these tests is to try and come up with a solution
	//! that is invalid, but gets through the system as valid.

	use super::{mock::*, *};

	const COMPUTE: ElectionCompute = ElectionCompute::OnChain;

	#[test]
	fn snapshot_is_there() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());
			let solution = raw_solution();

			// for whatever reason it might be:
			<Snapshot<Runtime>>::kill();

			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::SnapshotUnavailable
			);
		})
	}

	#[test]
	fn round() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			solution.round += 1;
			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::InvalidRound
			);
		})
	}

	#[test]
	fn desired_targets() {
		ExtBuilder::default().desired_targets(8).build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();

			assert_eq!(solution.compact.unique_targets().len(), 4);
			assert_eq!(MultiPhase::desired_targets().unwrap(), 8);

			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::WrongWinnerCount,
			);
		})
	}

	#[test]
	fn winner_indices() {
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(MultiPhase::snapshot().unwrap().targets.len(), 4);
			// ----------------------------------------------------^^ valid range is [0..3].

			// swap all votes from 3 to 4. This will ensure that the number of unique winners
			// will still be 4, but one of the indices will be gibberish. Requirement is to make
			// sure 3 a winner, which we don't do here.
			solution
				.compact
				.votes1
				.iter_mut()
				.filter(|(_, t)| *t == TargetIndex::from(3u16))
				.for_each(|(_, t)| *t += 1);
			solution.compact.votes2.iter_mut().for_each(|(_, (t0, _), t1)| {
				if *t0 == TargetIndex::from(3u16) {
					*t0 += 1
				};
				if *t1 == TargetIndex::from(3u16) {
					*t1 += 1
				};
			});
			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::InvalidWinner
			);
		})
	}

	#[test]
	fn voter_indices() {
		// should be caught in `compact.into_assignment`.
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(MultiPhase::snapshot().unwrap().voters.len(), 8);
			// ----------------------------------------------------^^ valid range is [0..7].

			// check that there is a index 7 in votes1, and flip to 8.
			assert!(
				solution
					.compact
					.votes1
					.iter_mut()
					.filter(|(v, _)| *v == VoterIndex::from(7u32))
					.map(|(v, _)| *v = 8)
					.count() > 0
			);
			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::NposElection(sp_npos_elections::Error::CompactInvalidIndex),
			);
		})
	}

	#[test]
	fn voter_votes() {
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(MultiPhase::snapshot().unwrap().voters.len(), 8);
			// ----------------------------------------------------^^ valid range is [0..7].

			// first, check that voter at index 7 (40) actually voted for 3 (40) -- this is self
			// vote. Then, change the vote to 2 (30).
			assert_eq!(
				solution
					.compact
					.votes1
					.iter_mut()
					.filter(|(v, t)| *v == 7 && *t == 3)
					.map(|(_, t)| *t = 2)
					.count(),
				1,
			);
			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::InvalidVote,
			);
		})
	}

	#[test]
	fn score() {
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(MultiPhase::snapshot().unwrap().voters.len(), 8);

			// simply faff with the score.
			solution.score[0] += 1;

			assert_noop!(
				MultiPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::InvalidScore,
			);
		})
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, Event, *};
	use frame_election_provider_support::ElectionProvider;
	use sp_npos_elections::Support;

	#[test]
	fn phase_rotation_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 0 ------- 15 ------- 25 ------- 30 ------- ------- 45 ------- 55 ------- 60
			//           |           |                            |           |
			//         Signed      Unsigned                     Signed     Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			assert_eq!(MultiPhase::round(), 1);

			roll_to(4);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			assert!(MultiPhase::snapshot().is_none());
			assert_eq!(MultiPhase::round(), 1);

			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert_eq!(multi_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert!(MultiPhase::snapshot().is_some());
			assert_eq!(MultiPhase::round(), 1);

			roll_to(24);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert!(MultiPhase::snapshot().is_some());
			assert_eq!(MultiPhase::round(), 1);

			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(
				multi_phase_events(),
				vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)],
			);
			assert!(MultiPhase::snapshot().is_some());

			roll_to(29);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(MultiPhase::snapshot().is_some());

			roll_to(30);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(MultiPhase::snapshot().is_some());

			// we close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(MultiPhase::snapshot().is_some());

			MultiPhase::elect().unwrap();

			assert!(MultiPhase::current_phase().is_off());
			assert!(MultiPhase::snapshot().is_none());
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

			// this module is now only capable of doing on-chain backup.
			assert_ok!(MultiPhase::elect());

			assert!(MultiPhase::current_phase().is_off());
		});
	}

	#[test]
	fn early_termination() {
		// an early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(multi_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert_eq!(MultiPhase::round(), 1);

			// an unexpected call to elect.
			roll_to(20);
			MultiPhase::elect().unwrap();

			// we surely can't have any feasible solutions. This will cause an on-chain election.
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted(1),
					Event::ElectionFinalized(Some(ElectionCompute::OnChain))
				],
			);
			// all storage items must be cleared.
			assert_eq!(MultiPhase::round(), 2);
			assert!(MultiPhase::snapshot().is_none());
			assert!(MultiPhase::snapshot_metadata().is_none());
			assert!(MultiPhase::desired_targets().is_none());
			assert!(MultiPhase::queued_solution().is_none());
		})
	}

	#[test]
	fn fallback_strategy_works() {
		ExtBuilder::default().fallback(FallbackStrategy::OnChain).build_and_execute(|| {
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));

			// zilch solutions thus far.
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

			// zilch solutions thus far.
			assert_eq!(MultiPhase::elect().unwrap_err(), ElectionError::NoFallbackConfigured);
		})
	}

	#[test]
	fn snapshot_creation_fails_if_too_big() {
		ExtBuilder::default().build_and_execute(|| {
			Targets::set((0..(TargetIndex::max_value() as AccountId) + 1).collect::<Vec<_>>());

			// signed phase failed to open.
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// unsigned phase failed to open.
			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// on-chain backup works though.
			roll_to(29);
			let (supports, _) = MultiPhase::elect().unwrap();
			assert!(supports.len() > 0);
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
		while weight_with(active)
			<= <Runtime as frame_system::Config>::BlockWeights::get().max_block
			|| active == all_voters
		{
			active += 1;
		}

		println!("can support {} voters to yield a weight of {}", active, weight_with(active));
	}
}
