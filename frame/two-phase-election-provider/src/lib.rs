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

//! # Two phase, offchain election provider pallet.
//!
//! As the name suggests, this election-provider has two distinct phases (see [`Phase`]), signed and
//! unsigned.
//!
//! ## Phases
//!
//! The timeline of pallet is as follows. At each block,
//! [`sp_election_providers::ElectionDataProvider::next_election_prediction`] is used to estimate
//! the time remaining to the next call to [`sp_election_providers::ElectionProvider::elect`]. Based
//! on this, a phase is chosen. The timeline is as follows.
//!
//! ```ignore
//!                                                                    elect()
//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
//!   +-------------------------------------------------------------------+
//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
//!
//! ```
//!
//! Note that the unsigned phase starts [`pallet::Config::UnsignedPhase`] blocks before the
//! `next_election_prediction`, but only ends when a call to [`ElectionProvider::elect`] happens.
//!
//! > Given this, it is rather important for the user of this pallet to ensure it always terminates
//! election via `elect` before requesting a new one.
//!
//! Each of the phases can be disabled by essentially setting their length to zero. If both phases
//! have length zero, then the pallet essentially runs only the on-chain backup.
//!
//! ### Signed Phase
//!
//!	In the signed phase, solutions (of type [`RawSolution`]) are submitted and queued on chain. A
//! deposit is reserved, based on the size of the solution, for the cost of keeping this solution
//! on-chain for a number of blocks, and the potential weight of the solution upon being checked. A
//! maximum of [`pallet::Config::MaxSignedSubmissions`] solutions are stored. The queue is always
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
//! until drained). Each solution undergoes an expensive [`Pallet::feasibility_check`], which
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
//! [`sp_election_providers::ElectionProvider`]. In this case, this pallet can even have the on-chain
//! election provider as fallback, or special _noop_ fallback that simply returns an error, thus
//! replicating [`FallbackStrategy::Nothing`].
//!
//! **Score based on size**: We should always prioritize small solutions over bigger ones, if there
//! is a tie. Even more harsh should be to enforce the bound of the `reduce` algorithm.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode, HasCompact};
use frame_support::{
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_none, ensure_signed, offchain::SendTransactionTypes};
use sp_election_providers::{ElectionDataProvider, ElectionProvider, onchain};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, is_score_better, CompactSolution, ElectionScore,
	EvaluateSupport, ExtendedBalance, PerThing128, Supports, VoteWeight,
};
use sp_runtime::{
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		TransactionValidityError, ValidTransaction,
	},
	DispatchError, InnerOf, PerThing, Perbill, RuntimeDebug, SaturatedConversion,
};
use sp_std::prelude::*;
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

const LOG_TARGET: &'static str = "election-provider";

// for the helper macros
#[doc(hidden)]
pub use sp_runtime::traits::UniqueSaturatedInto;
#[doc(hidden)]
pub use sp_std;

pub mod signed;
pub mod unsigned;
pub mod weights;

use weights::WeightInfo;

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

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

struct OnChainConfig<T: Config>(sp_std::marker::PhantomData<T>)
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>;
impl<T: Config> onchain::Config for OnChainConfig<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
{
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Accuracy = T::OnChainAccuracy;
	type DataProvider = T::DataProvider;
}

/// Current phase of the pallet.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Phase<Bn> {
	/// Nothing, the election is not happening.
	Off,
	/// Signed phase is open.
	Signed,
	/// Unsigned phase. First element is whether it is open or not, second the starting block
	/// number.
	Unsigned((bool, Bn)),
}

impl<Bn> Default for Phase<Bn> {
	fn default() -> Self {
		Phase::Off
	}
}

impl<Bn: PartialEq + Eq> Phase<Bn> {
	/// Weather the phase is signed or not.
	pub fn is_signed(&self) -> bool {
		matches!(self, Phase::Signed)
	}

	/// Weather the phase is unsigned or not.
	pub fn is_unsigned(&self) -> bool {
		matches!(self, Phase::Unsigned(_))
	}

	/// Weather the phase is unsigned and open or not, with specific start.
	pub fn is_unsigned_open_at(&self, at: Bn) -> bool {
		matches!(self, Phase::Unsigned((true, real)) if *real == at)
	}

	/// Weather the phase is unsigned and open or not.
	pub fn is_unsigned_open(&self) -> bool {
		matches!(self, Phase::Unsigned((true, _)))
	}

	/// Weather the phase is off or not.
	pub fn is_off(&self) -> bool {
		matches!(self, Phase::Off)
	}
}

/// A configuration for the module to indicate what should happen in the case of a fallback i.e.
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
/// [`Pallet::feasibility_check`]
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct RawSolution<C> {
	/// Compact election edges.
	compact: C,
	/// The _claimed_ score of the solution.
	score: ElectionScore,
	/// The round at which this solution should be submitted.
	round: u32,
}

impl<C: Default> Default for RawSolution<C> {
	fn default() -> Self {
		// Round 0 is always invalid, only set this to 1.
		Self { round: 1, compact: Default::default(), score: Default::default() }
	}
}

/// A raw, unchecked signed submission.
///
/// This is just a wrapper around [`RawSolution`] and some additional info.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct SignedSubmission<A, B: HasCompact, C> {
	/// Who submitted this solution.
	who: A,
	/// The deposit reserved for storing this solution.
	deposit: B,
	/// The reward that should be given to this solution, if chosen the as the final one.
	reward: B,
	/// The raw solution itself.
	solution: RawSolution<C>,
}

/// A checked solution, ready to be enacted.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct ReadySolution<A> {
	/// The final supports of the solution.
	///
	/// This is target-major vector, storing each winners, total backing, and each individual
	/// backer.
	supports: Supports<A>,
	/// The score of the solution.
	///
	/// This is needed to potentially challenge the solution.
	score: ElectionScore,
	/// How this election was computed.
	compute: ElectionCompute,
}

/// Solution size of the election.
///
/// This is needed for proper weight calculation.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, Default)]
pub struct SolutionSize {
	/// Number of all voters.
	///
	/// This must match the on-chain snapshot.
	#[codec(compact)]
	voters: u32,
	/// Number of all targets.
	///
	/// This must match the on-chain snapshot.
	#[codec(compact)]
	targets: u32,
}

/// A snapshot of all the data that is needed for en entire round. They are provided by
/// [`ElectionDataProvider`] at the beginning of the signed phase and are kept around until the
/// round is finished.
///
/// These are stored together because they are often times accessed together.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct RoundSnapshot<A> {
	/// All of the voters.
	pub voters: Vec<(A, VoteWeight, Vec<A>)>,
	/// All of the targets.
	pub targets: Vec<A>,
}

/// Some metadata related to snapshot.
///
/// In this pallet, there are cases where we want to read the whole snapshot (voters, targets,
/// desired), and cases that we are interested in just the length of these values. The former favors
/// the snapshot to be stored in one struct (as it is now) while the latter prefers them to be
/// separate to enable the use of `decode_len`. This approach is a middle ground, storing the
/// snapshot as one struct, whilst storing the lengths separately.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct RoundSnapshotMetadata {
	/// The length of voters.
	voters_len: u32,
	/// The length of targets.
	targets_len: u32,
}

/// Internal errors of the pallet.
///
/// Note that this is different from [`pallet::Error`].
#[derive(RuntimeDebug, Eq, PartialEq)]
pub enum ElectionError {
	/// A feasibility error.
	Feasibility(FeasibilityError),
	/// An error in the on-chain fallback.
	OnChainFallback(onchain::Error),
	/// No fallback is configured
	NoFallbackConfigured,
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	///
	/// This can only happen in the unsigned phase.
	PoolSubmissionFailed,
}

impl From<onchain::Error> for ElectionError {
	fn from(e: onchain::Error) -> Self {
		ElectionError::OnChainFallback(e)
	}
}

impl From<sp_npos_elections::Error> for ElectionError {
	fn from(e: sp_npos_elections::Error) -> Self {
		ElectionError::NposElections(e)
	}
}

impl From<FeasibilityError> for ElectionError {
	fn from(e: FeasibilityError) -> Self {
		ElectionError::Feasibility(e)
	}
}

/// Errors that can happen in the feasibility check.
#[derive(RuntimeDebug, Eq, PartialEq)]
pub enum FeasibilityError {
	/// Wrong number of winners presented.
	WrongWinnerCount,
	/// The snapshot is not available.
	///
	/// This must be an internal error of the chain.
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
	pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<Self>>>,
		ExtendedBalance: From<InnerOf<OnChainAccuracyOf<Self>>>,
	{
		type Event: From<Event<Self>>
			+ Into<<Self as frame_system::Config>::Event>
			+ IsType<<Self as frame_system::Config>::Event>;

		/// Currency type.
		type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

		/// Duration of the signed phase.
		#[pallet::constant]
		type SignedPhase: Get<Self::BlockNumber>;
		/// Duration of the unsigned phase.
		#[pallet::constant]
		type UnsignedPhase: Get<Self::BlockNumber>;
		/// Maximum number of singed submissions that can be queued.
		#[pallet::constant]
		type MaxSignedSubmissions: Get<u32>;

		#[pallet::constant]
		type SignedRewardBase: Get<BalanceOf<Self>>;
		#[pallet::constant]
		type SignedRewardFactor: Get<Perbill>;
		#[pallet::constant]
		type SignedRewardMax: Get<Option<BalanceOf<Self>>>;

		#[pallet::constant]
		type SignedDepositBase: Get<BalanceOf<Self>>;
		#[pallet::constant]
		type SignedDepositByte: Get<BalanceOf<Self>>;
		#[pallet::constant]
		type SignedDepositWeight: Get<BalanceOf<Self>>;

		/// The minimum amount of improvement to the solution score that defines a solution as
		/// "better".
		#[pallet::constant]
		type SolutionImprovementThreshold: Get<Perbill>;

		/// The priority of the unsigned transaction submitted in the unsigned-phase
		type UnsignedPriority: Get<TransactionPriority>;
		/// Maximum number of iteration of balancing that will be executed in the embedded miner of
		/// the pallet.
		type MinerMaxIterations: Get<u32>;
		/// Maximum weight that the miner should consume.
		///
		/// The miner will ensure that the total weight of the unsigned solution will not exceed
		/// this values, based on [`WeightInfo::submit_unsigned`].
		type MinerMaxWeight: Get<Weight>;

		/// Handler for the slashed deposits.
		type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;
		/// Handler for the rewards.
		type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;

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

		/// The weight of the pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
	{
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let next_election = T::DataProvider::next_election_prediction(now).max(now);

			let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
			let unsigned_deadline = T::UnsignedPhase::get();

			let remaining = next_election - now;
			let current_phase = Self::current_phase();

			match current_phase {
				Phase::Off if remaining <= signed_deadline && remaining > unsigned_deadline => {
					Self::on_initialize_open_signed();
					log!(info, "Starting signed phase at #{:?} , round {}.", now, Self::round());
					T::WeightInfo::on_initialize_open_signed()
				},
				Phase::Signed | Phase::Off if remaining <= unsigned_deadline && remaining > 0u32.into() => {
					let additional = Self::on_initialize_open_unsigned(current_phase, now);
					log!(info, "Starting unsigned phase at #{:?}.", now);
					T::WeightInfo::on_initialize_open_signed().saturating_add(additional)
				},
				_ => {
					T::WeightInfo::on_initialize_nothing()
				}
			}
		}

		fn offchain_worker(n: T::BlockNumber) {
			// We only run the OCW in the fist block of the unsigned phase.
			if Self::current_phase().is_unsigned_open_at(n) {
				match Self::set_check_offchain_execution_status(n) {
					Ok(_) => match Self::mine_and_submit() {
						Ok(_) => log!(
							info,
							"successfully submitted a solution via OCW at block {:?}",
							n
						),
						Err(e) => log!(error, "error while submitting transaction in OCW: {:?}", e),
					},
					Err(why) => log!(error, "Error in unsigned offchain worker: {:?}", why),
				}
			}
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
				.map(|_| <OnChainAccuracyOf<T>>::one().deconstruct().into())
				.collect();
			let _: UpperOf<OnChainAccuracyOf<T>> = maximum_chain_accuracy
				.iter()
				.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());

			// 2. Maximum sum of [CompactAccuracy; 16] must fit into `UpperOf<OffchainAccuracy>`.
			let maximum_chain_accuracy: Vec<UpperOf<CompactAccuracyOf<T>>> = (0..max_vote)
				.map(|_| <CompactAccuracyOf<T>>::one().deconstruct().into())
				.collect();
			let _: UpperOf<CompactAccuracyOf<T>> = maximum_chain_accuracy
				.iter()
				.fold(Zero::zero(), |acc, x| acc.checked_add(x).unwrap());
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
	{
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
		#[pallet::weight(T::WeightInfo::submit(*witness_data))]
		pub fn submit(
			origin: OriginFor<T>,
			solution: RawSolution<CompactOf<T>>,
			witness_data: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure witness data is correct.
			ensure!(
				witness_data >= <SignedSubmissions<T>>::decode_len().unwrap_or_default() as u32,
				Error::<T>::InvalidWitness,
			);

			// ensure solution is timely.
			ensure!(
				Self::current_phase().is_signed(),
				Error::<T>::EarlySubmission,
			);

			// NOTE: this is the only case where having separate snapshot would have been better
			// because could do just decode_len. But we can create abstractions to do this.

			// build size. Note: this is not needed for weight calc, thus not input.
			// defensive-only: if phase is signed, snapshot will exist.
			let size = Self::build_solution_size().unwrap_or_default();

			// ensure solution claims is better.
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index =
				Self::insert_submission(&who, &mut signed_submissions, solution, size);
			ensure!(maybe_index.is_some(), Error::<T>::QueueFull);
			let index = maybe_index.expect("Option checked to be `Some`; qed.");

			// collect deposit. Thereafter, the function cannot fail.
			// Defensive -- index is valid.
			let deposit = signed_submissions
				.get(index)
				.map(|s| s.deposit)
				.unwrap_or_default();
			T::Currency::reserve(&who, deposit).map_err(|_| Error::<T>::CannotPayDeposit)?;

			// store the new signed submission.
			debug_assert!(signed_submissions.len() as u32 <= T::MaxSignedSubmissions::get());
			log!(
				info,
				"queued signed solution with (claimed) score {:?}",
				signed_submissions
					.get(index)
					.map(|s| s.solution.score)
					.unwrap_or_default()
			);

			<SignedSubmissions<T>>::put(signed_submissions);
			Self::deposit_event(Event::SolutionStored(ElectionCompute::Signed));
			Ok(None.into())
		}

		/// Submit a solution for the unsigned phase.
		///
		/// The dispatch origin fo this call must be __none__.
		///
		/// This submission is checked on the fly, thus it is likely yo be more limited and smaller.
		/// Moreover, this unsigned solution is only validated when submitted to the pool from the
		/// local process. Effectively, this means that only active validators can submit this
		/// transaction when authoring a block.
		///
		/// To prevent any incorrect solution (and thus wasted time/weight), this transaction will
		/// panic if the solution submitted by the validator is invalid, effectively putting their
		/// authoring reward at risk.
		///
		/// No deposit or reward is associated with this.
		#[pallet::weight(T::WeightInfo::submit_unsigned(
			witness.voters,
			witness.targets,
			solution.compact.voter_count() as u32,
			solution.compact.unique_targets().len() as u32
		))]
		pub fn submit_unsigned(
			origin: OriginFor<T>,
			solution: RawSolution<CompactOf<T>>,
			witness: SolutionSize,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let error_message = "Invalid unsigned submission must produce invalid block and \
				deprive validator from their authoring reward.";

			// check phase and score.
			// NOTE: since we do this in pre-dispatch, we can just ignore it here.
			Self::unsigned_pre_dispatch_checks(&solution).expect(error_message);

			// ensure witness was correct.
			let RoundSnapshotMetadata {
				voters_len,
				targets_len,
			} = Self::snapshot_metadata().expect(error_message);

			// NOTE: we are asserting, not `ensure`ing -- we want to panic here.
			assert!(voters_len as u32 == witness.voters, error_message);
			assert!(targets_len as u32 == witness.targets, error_message);

			let ready =
				Self::feasibility_check(solution, ElectionCompute::Unsigned).expect(error_message);

			// store the newly received solution.
			log!(
				info,
				"queued unsigned solution with score {:?}",
				ready.score
			);
			<QueuedSolution<T>>::put(ready);
			Self::deposit_event(Event::SolutionStored(ElectionCompute::Unsigned));

			Ok(None.into())
		}
	}

	#[pallet::event]
	#[pallet::metadata(<T as frame_system::Config>::AccountId = "AccountId")]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
	{
		/// A solution was stored with the given compute.
		///
		/// If the solution is signed, this means that it hasn't yet been processed. If the solution
		/// is unsigned, this means that it has also been processed.
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

	#[pallet::error]
	pub enum Error<T> {
		/// Submission was too early.
		EarlySubmission,
		/// Submission was too weak, score-wise.
		WeakSubmission,
		/// The queue was full, and the solution was not better than any of the existing ones.
		QueueFull,
		/// The origin failed to pay the deposit.
		CannotPayDeposit,
		/// witness data to dispathable is invalid.
		InvalidWitness,
	}

	#[pallet::origin]
	pub struct Origin<T>(PhantomData<T>);

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
	{
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
						T::UnsignedPriority::get().saturating_add(solution.score[0].saturated_into()),
					)
					// used to deduplicate unsigned solutions: each validator should produce one
					// solution per round at most, and solutions are not propagate.
					.and_provides(solution.round)
					// transaction should stay in the pool for the duration of the unsigned phase.
					.longevity(T::UnsignedPhase::get().saturated_into::<u64>())
					// We don't propagate this. This can never the validated at a remote node.
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
	/// diagnostics of the module.
	///
	/// This is merely incremented once per every time that an upstream `elect` is called.
	#[pallet::storage]
	#[pallet::getter(fn round)]
	pub type Round<T: Config> = StorageValue<_, u32, ValueQuery, DefaultForRound>;

	/// Current phase.
	#[pallet::storage]
	#[pallet::getter(fn current_phase)]
	pub type CurrentPhase<T: Config> = StorageValue<_, Phase<T::BlockNumber>, ValueQuery>;

	/// Sorted (worse -> best) list of unchecked, signed solutions.
	#[pallet::storage]
	#[pallet::getter(fn signed_submissions)]
	pub type SignedSubmissions<T: Config> = StorageValue<
		_,
		Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
		ValueQuery,
	>;

	/// Current best solution, signed or unsigned.
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
	pub type SnapshotMetadata<T: Config> = StorageValue<_, RoundSnapshotMetadata>;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
{
	/// Logic for `<Pallet as Hooks>::on_initialize` when signed phase is being opened.
	///
	/// This is decoupled for easy weight calculation.
	pub fn on_initialize_open_signed() {
		<CurrentPhase<T>>::put(Phase::Signed);
		Self::create_snapshot();
		Self::deposit_event(Event::SignedPhaseStarted(Self::round()));
	}

	/// Logic for `<Pallet as Hooks<T>>::on_initialize` when unsigned phase is being opened.
	///
	/// This is decoupled for easy weight calculation. Note that the default weight benchmark of
	/// this function will assume an empty signed queue for `finalize_signed_phase`.
	pub fn on_initialize_open_unsigned(
		current_phase: Phase<T::BlockNumber>,
		now: T::BlockNumber,
	) -> Weight {
		if current_phase == Phase::Off {
			// if not being followed by a signed phase, then create the snapshots.
			debug_assert!(Self::snapshot().is_none());
			Self::create_snapshot();
		} else {
			// if followed by a signed phase, then finalize the signed stuff.
			debug_assert!(Self::signed_submissions().is_empty());
		}

		// noop if no signed phase has been open. NOTE: benchmarks assume this is noop, we return
		//additional weight manually.
		let (_found, additional_weight) = Self::finalize_signed_phase();
		log!(
			info,
			"[{:?}] Signed phase closed, found solution = {}",
			now,
			_found
		);

		// for now always start the unsigned phase.
		<CurrentPhase<T>>::put(Phase::Unsigned((true, now)));
		Self::deposit_event(Event::UnsignedPhaseStarted(Self::round()));

		additional_weight
	}

	/// Creates the snapshot. Writes new data to:
	///
	/// 1. [`SnapshotMetadata`]
	/// 2. [`RoundSnapshot`]
	/// 3. [`DesiredTargets`]
	pub fn create_snapshot() {
		// if any of them don't exist, create all of them. This is a bit conservative.
		let targets = T::DataProvider::targets();
		let voters = T::DataProvider::voters();
		let desired_targets = T::DataProvider::desired_targets();

		<SnapshotMetadata<T>>::put(RoundSnapshotMetadata {
			voters_len: voters.len() as u32,
			targets_len: targets.len() as u32,
		});
		<DesiredTargets<T>>::put(desired_targets);
		<Snapshot<T>>::put(RoundSnapshot { voters, targets });
	}

	/// Build the solution size from the snapshot metadata, if it exists. Else, returns `None`.
	fn build_solution_size() -> Option<SolutionSize> {
		let metadata = Self::snapshot_metadata()?;
		Some(SolutionSize {
			voters: metadata.voters_len as u32,
			targets: metadata.targets_len as u32,
		})
	}

	/// Checks the feasibility of a solution.
	///
	/// This checks the solution for the following:
	///
	/// 0. **all** of the used indices must be correct.
	/// 1. present correct number of winners.
	/// 2. any assignment is checked to match with [Snapshot::voters].
	/// 3. for each assignment, the check of `ElectionDataProvider` is also examined.
	/// 4. the claimed score is valid.
	fn feasibility_check(
		solution: RawSolution<CompactOf<T>>,
		compute: ElectionCompute,
	) -> Result<ReadySolution<T::AccountId>, FeasibilityError> {
		let RawSolution {
			compact,
			score,
			round,
		} = solution;

		// first, check round.
		ensure!(Self::round() == round, FeasibilityError::InvalidRound);

		// winners are not directly encoded in the solution.
		let winners = compact.unique_targets();

		// TODO: this can probably checked ahead of time, both in signed and unsigned story.
		let desired_targets =
			Self::desired_targets().ok_or(FeasibilityError::SnapshotUnavailable)?;

		ensure!(
			winners.len() as u32 == desired_targets,
			FeasibilityError::WrongWinnerCount,
		);

		// read the entire snapshot.
		let RoundSnapshot {
			voters: snapshot_voters,
			targets: snapshot_targets,
		} = Self::snapshot().ok_or(FeasibilityError::SnapshotUnavailable)?;

		// ----- Start building. First, we need some closures.
		let cache = helpers::generate_voter_cache::<T>(&snapshot_voters);
		let voter_at = helpers::voter_at_fn::<T>(&snapshot_voters);
		let target_at = helpers::target_at_fn::<T>(&snapshot_targets);
		let voter_index = helpers::voter_index_fn_usize::<T>(&cache);

		// first, make sure that all the winners are sane.
		let winners = winners
			.into_iter()
			.map(|i| target_at(i).ok_or(FeasibilityError::InvalidWinner))
			.collect::<Result<Vec<T::AccountId>, FeasibilityError>>()?;

		// Then convert compact -> Assignment. This will fail if any of the indices are gibberish.
		// that winner indices are already checked.
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
				let snapshot_index = voter_index(&assignment.who).ok_or(FeasibilityError::InvalidVoter)?;
				// defensive-only: index comes from the snapshot, must exist.
				let (_voter, _stake, targets) = snapshot_voters.get(snapshot_index).ok_or(FeasibilityError::InvalidVoter)?;

				// check that all of the targets are valid based on the snapshot.
				if assignment
					.distribution
					.iter()
					.any(|(d, _)| !targets.contains(d))
				{
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

		// let supports = supports.flatten();
		Ok(ReadySolution {
			supports,
			compute,
			score,
		})
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
		<Snapshot<T>>::kill();
		<SnapshotMetadata<T>>::kill();
		<DesiredTargets<T>>::kill();
	}

	/// On-chain fallback of election.
	fn onchain_fallback() -> Result<Supports<T::AccountId>, ElectionError>
	where
		ExtendedBalance: From<<T::OnChainAccuracy as PerThing>::Inner>,
	{
		<onchain::OnChainSequentialPhragmen<OnChainConfig<T>> as ElectionProvider<
			T::AccountId,
			T::BlockNumber,
		>>::elect()
		.map_err(Into::into)
	}

	fn do_elect() -> Result<Supports<T::AccountId>, ElectionError> {
		// NOTE: SignedSubmission is guaranteed to be drained by the end of the signed phase too,
		// thus no need for a manual cleanup:
		debug_assert!(Self::signed_submissions().is_empty());
		<QueuedSolution<T>>::take()
			.map_or_else(
				|| match T::Fallback::get() {
					FallbackStrategy::OnChain => Self::onchain_fallback()
						.map(|r| (r, ElectionCompute::OnChain))
						.map_err(Into::into),
					FallbackStrategy::Nothing => Err(ElectionError::NoFallbackConfigured),
				},
				|ReadySolution {
					supports, compute, ..
				}| Ok((supports, compute)),
			)
			.map(|(supports, compute)| {
				Self::deposit_event(Event::ElectionFinalized(Some(compute)));
				log!(info, "Finalized election round with compute {:?}.", compute);
				supports
			})
			.map_err(|err| {
				Self::deposit_event(Event::ElectionFinalized(None));
				log!(warn, "Failed to finalize election round. reason {:?}", err);
				err
			})
	}
}

impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for Pallet<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	ExtendedBalance: From<InnerOf<OnChainAccuracyOf<T>>>,
{
	type Error = ElectionError;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<T::AccountId>, Self::Error> {
		let outcome = Self::do_elect();
		// cleanup.
		Self::post_elect();
		outcome
	}

	fn ongoing() -> bool {
		matches!(Self::current_phase(), Phase::Signed | Phase::Unsigned(_))
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
			assert!(TwoPhase::current_phase().is_signed());
			let solution = raw_solution();

			// for whatever reason it might be:
			<Snapshot<Runtime>>::kill();

			assert_noop!(
				TwoPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::SnapshotUnavailable
			);
		})
	}

	#[test]
	fn round() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
			assert!(TwoPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			solution.round += 1;
			assert_noop!(
				TwoPhase::feasibility_check(solution, COMPUTE),
				FeasibilityError::InvalidRound
			);
		})
	}

	#[test]
	fn desired_targets() {
		ExtBuilder::default()
			.desired_targets(8)
			.build_and_execute(|| {
				roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
				assert!(TwoPhase::current_phase().is_signed());

				let solution = raw_solution();

				assert_eq!(solution.compact.unique_targets().len(), 4);
				assert_eq!(TwoPhase::desired_targets().unwrap(), 8);

				assert_noop!(
					TwoPhase::feasibility_check(solution, COMPUTE),
					FeasibilityError::WrongWinnerCount
				);
			})
	}

	#[test]
	fn winner_indices() {
		ExtBuilder::default()
			.desired_targets(2)
			.build_and_execute(|| {
				roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
				assert!(TwoPhase::current_phase().is_signed());

				let mut solution = raw_solution();
				assert_eq!(TwoPhase::snapshot().unwrap().targets.len(), 4);
				// ----------------------------------------------------^^ valid range is [0..3].

				// swap all votes from 3 to 4. This will ensure that the number of unique winners will
				// still be 4, but one of the indices will be gibberish. Requirement is to make sure 3
				// a winner, which we don't do here.
				solution
					.compact
					.votes1
					.iter_mut()
					.filter(|(_, t)| *t == 3u16)
					.for_each(|(_, t)| *t += 1);
				solution
					.compact
					.votes2
					.iter_mut()
					.for_each(|(_, (t0, _), t1)| {
						if *t0 == 3u16 {
							*t0 += 1
						};
						if *t1 == 3u16 {
							*t1 += 1
						};
					});
				assert_noop!(
					TwoPhase::feasibility_check(solution, COMPUTE),
					FeasibilityError::InvalidWinner
				);
			})
	}

	#[test]
	fn voter_indices() {
		// should be caught in `compact.into_assignment`.
		ExtBuilder::default()
			.desired_targets(2)
			.build_and_execute(|| {
				roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
				assert!(TwoPhase::current_phase().is_signed());

				let mut solution = raw_solution();
				assert_eq!(TwoPhase::snapshot().unwrap().voters.len(), 8);
				// ----------------------------------------------------^^ valid range is [0..7].

				// check that there is a index 7 in votes1, and flip to 8.
				assert!(
					solution
						.compact
						.votes1
						.iter_mut()
						.filter(|(v, _)| *v == 7u32)
						.map(|(v, _)| *v = 8)
						.count() > 0
				);
				assert_noop!(
					TwoPhase::feasibility_check(solution, COMPUTE),
					FeasibilityError::NposElection(sp_npos_elections::Error::CompactInvalidIndex),
				);
			})
	}

	#[test]
	fn voter_votes() {
		ExtBuilder::default()
			.desired_targets(2)
			.build_and_execute(|| {
				roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
				assert!(TwoPhase::current_phase().is_signed());

				let mut solution = raw_solution();
				assert_eq!(TwoPhase::snapshot().unwrap().voters.len(), 8);
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
					TwoPhase::feasibility_check(solution, COMPUTE),
					FeasibilityError::InvalidVote,
				);
			})
	}

	#[test]
	fn score() {
		ExtBuilder::default()
			.desired_targets(2)
			.build_and_execute(|| {
				roll_to(<EpochLength>::get() - <SignedPhase>::get() - <UnsignedPhase>::get());
				assert!(TwoPhase::current_phase().is_signed());

				let mut solution = raw_solution();
				assert_eq!(TwoPhase::snapshot().unwrap().voters.len(), 8);

				// simply faff with the score.
				solution.score[0] += 1;

				assert_noop!(
					TwoPhase::feasibility_check(solution, COMPUTE),
					FeasibilityError::InvalidScore,
				);
			})
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, Event, *};
	use sp_election_providers::ElectionProvider;
	use sp_npos_elections::Support;

	#[test]
	fn phase_rotation_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 0 ------- 15 ------- 25 ------- 30 ------- ------- 45 ------- 55 ------- 60
			//           |           |                            |           |
			//         Signed      Unsigned                     Signed     Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert_eq!(TwoPhase::round(), 1);

			roll_to(4);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot().is_none());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert_eq!(two_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert!(TwoPhase::snapshot().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(24);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(25);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert_eq!(two_phase_events(), vec![Event::SignedPhaseStarted(1), Event::UnsignedPhaseStarted(1)]);
			assert!(TwoPhase::snapshot().is_some());

			roll_to(29);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(TwoPhase::snapshot().is_some());

			roll_to(30);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(TwoPhase::snapshot().is_some());

			// we close when upstream tells us to elect.
			roll_to(32);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));
			assert!(TwoPhase::snapshot().is_some());

			TwoPhase::elect().unwrap();

			assert!(TwoPhase::current_phase().is_off());
			assert!(TwoPhase::snapshot().is_none());
			assert_eq!(TwoPhase::round(), 2);

			roll_to(44);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(45);
			assert!(TwoPhase::current_phase().is_signed());

			roll_to(55);
			assert!(TwoPhase::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn signed_phase_void() {
		ExtBuilder::default().phases(0, 10).build_and_execute(|| {
			roll_to(15);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(19);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(20);
			assert!(TwoPhase::current_phase().is_unsigned_open_at(20));
			assert!(TwoPhase::snapshot().is_some());

			roll_to(30);
			assert!(TwoPhase::current_phase().is_unsigned_open_at(20));

			TwoPhase::elect().unwrap();

			assert!(TwoPhase::current_phase().is_off());
			assert!(TwoPhase::snapshot().is_none());
		});
	}

	#[test]
	fn unsigned_phase_void() {
		ExtBuilder::default().phases(10, 0).build_and_execute(|| {
			roll_to(15);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(19);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(20);
			assert!(TwoPhase::current_phase().is_signed());
			assert!(TwoPhase::snapshot().is_some());

			roll_to(30);
			assert!(TwoPhase::current_phase().is_signed());

			let _ = TwoPhase::elect().unwrap();

			assert!(TwoPhase::current_phase().is_off());
			assert!(TwoPhase::snapshot().is_none());
		});
	}

	#[test]
	fn both_phases_void() {
		ExtBuilder::default().phases(0, 0).build_and_execute(|| {
			roll_to(15);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(19);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(20);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(30);
			assert!(TwoPhase::current_phase().is_off());

			// this module is now only capable of doing on-chain backup.
			let _ = TwoPhase::elect().unwrap();

			assert!(TwoPhase::current_phase().is_off());
		});
	}

	#[test]
	fn early_termination() {
		// an early termination in the signed phase, with no queued solution.
		ExtBuilder::default().build_and_execute(|| {
			// signed phase started at block 15 and will end at 25.
			roll_to(14);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);

			roll_to(15);
			assert_eq!(two_phase_events(), vec![Event::SignedPhaseStarted(1)]);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert_eq!(TwoPhase::round(), 1);

			// an unexpected call to elect.
			roll_to(20);
			TwoPhase::elect().unwrap();

			// we surely can't have any feasible solutions. This will cause an on-chain election.
			assert_eq!(
				two_phase_events(),
				vec![
					Event::SignedPhaseStarted(1),
					Event::ElectionFinalized(Some(ElectionCompute::OnChain))
				],
			);
			// all storage items must be cleared.
			assert_eq!(TwoPhase::round(), 2);
			assert!(TwoPhase::snapshot().is_none());
			assert!(TwoPhase::snapshot_metadata().is_none());
			assert!(TwoPhase::desired_targets().is_none());
			assert!(TwoPhase::queued_solution().is_none());
		})
	}

	#[test]
	fn fallback_strategy_works() {
		ExtBuilder::default()
			.fallabck(FallbackStrategy::OnChain)
			.build_and_execute(|| {
				roll_to(15);
				assert_eq!(TwoPhase::current_phase(), Phase::Signed);

				roll_to(25);
				assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));

				// zilch solutions thus far.
				let supports = TwoPhase::elect().unwrap();

				assert_eq!(
					supports,
					vec![
						(
							30,
							Support {
								total: 40,
								voters: vec![(2, 5), (4, 5), (30, 30)]
							}
						),
						(
							40,
							Support {
								total: 60,
								voters: vec![(2, 5), (3, 10), (4, 5), (40, 40)]
							}
						)
					]
				)
			});

		ExtBuilder::default()
			.fallabck(FallbackStrategy::Nothing)
			.build_and_execute(|| {
				roll_to(15);
				assert_eq!(TwoPhase::current_phase(), Phase::Signed);

				roll_to(25);
				assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));

				// zilch solutions thus far.
				assert_eq!(
					TwoPhase::elect().unwrap_err(),
					ElectionError::NoFallbackConfigured
				);
			})
	}
}
