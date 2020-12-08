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

//! # Two phase election provider pallet.
//!
//! As the name suggests, this election-provider has two distinct phases (see
//! [Phase](two_phase::Phase)), signed and unsigned.
//!
//! ## Phases
//!
//! The timeline of pallet is as follows. At each block,
//! [`ElectionDataProvider::next_election_prediction`] is used to estimate the time remaining to the
//! next call to [`ElectionProvider::elect`]. Based on this, a phase is chosen. The timeline is as
//! follows.
//!
//! ```ignore
//!                                                                    elect()
//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
//!   +-------------------------------------------------------------------+
//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
//!
//! ```
//!
//! Note that the unsigned phase starts [Config::UnsignedPhase](two_phase::Config::UnsignedPhase)
//! blocks before the `next_election_prediction`, but only ends when a call to
//! `ElectionProvider::elect` happens.
//!
//! Each of the phases can be disabled by essentially setting their length to zero. If both phases
//! have length zero, then the pallet essentially runs only the on-chain backup.
//!
//! ### Signed Phase
//!
//!	In the signed phase, solutions (of type [RawSolution](struct.RawSolution.html)) are submitted
//! and queued on chain. A deposit is reserved, based on the size of the solution, for the cost of
//! keeping this solution on-chain for a number of blocks, and the potential weight of the solution
//! upon being checked. A maximum of [`Config::MaxSignedSubmissions`] solutions are stored. The
//! queue is always sorted based on score (worse to best).
//!
//! Upon arrival of a new solution:
//!
//! 1. If the queue is not full, it is stored in the appropriate index.
//! 2. If the queue is full but the submitted solution is better than one of the queued ones, the
//!    worse solution is discarded, the bond of the outgoing solution is returned, and the new
//!    solution is stored in the correct index.
//! 3. If the queue is full and the solution is not an improvement compared to any of the queued
//!    ones, it is instantly rejected and no additional bond is reserved.
//!
//! A signed solution cannot be reversed, taken back, updated, or retracted. In other words, the
//! origin can not bail out in any way.
//!
//! Upon the end of the signed phase, the solutions are examined from worse to best (i.e. `pop()`ed
//! until drained). Each solution undergoes an expensive [`Module::feasibility_check`], which ensure
//! the score claimed by this score was correct, among other checks. At each step, if the current
//! best solution passes the feasibility check, it is considered to be the best one. The sender of
//! the origin is rewarded, and the rest of the queued solutions get their deposit back, without
//! being checked.
//!
//! The following example covers all of the cases at the end of the signed phase:
//!
//! ```ignore
//! Queue
//! +-------------------------------+
//! |Solution(score=20, valid=false)| +-->  Slashed
//! +-------------------------------+
//! |Solution(score=15, valid=true )| +-->  Rewarded
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
//! despite one of them being invalid.
//!
//! ## Unsigned Phase
//!
//! The unsigned phase will always follow the signed phase, with the specified duration. In this
//! phase, only validator nodes can submit solutions. A validator node who has offchain workers
//! enabled will start to mine a solution in this phase and submits it back to the chain as an
//! unsigned transaction, thus the name _unsigned_ phase.
//!
//! Validators will only submit solutions if the one that they have computed is sufficiently better
//! than the best queued one (see [SolutionImprovementThreshold]) and will limit the weigh of the
//! solution to [MinerMaxWeight].
//!
//! ### Fallback
//!
//! If we reach the end of both phases (i.e. call to [ElectionProvider::elect] happens) and no good
//! solution is queued, then we fallback to an on-chain election. The on-chain election is slow, and
//! contains to balancing or reduction post-processing.
//!
//! ## Feasible Solution (correct solution)
//!
//! All submissions must undergo a feasibility check. A feasible solution is as follows:
//!
//! 0. **all** of the used indices must be correct.
//! 1. present correct number of winners.
//! 2. any assignment is checked to match with [Snapshot::voters].
//! 3. for each assignment, the check of `ElectionDataProvider` is also examined.
//! 4. the claimed score is valid.
//!
//! ## Accuracy
//!
//! Solutions are encoded using indices of the [Snapshot]. The accuracy used for these indices
//! heavily influences the size of the solution. These indices are configured by an upstream user of
//! this pallet, through `CompactSolution` type of the `ElectionDataProvider`.
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

use crate::onchain::OnChainSequentialPhragmen;
use codec::{Decode, Encode, HasCompact};
use frame_support::{
	decl_event, decl_module, decl_storage,
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_none, ensure_signed, offchain::SendTransactionTypes};
use sp_election_providers::{ElectionDataProvider, ElectionProvider};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, is_score_better, Assignment, CompactSolution,
	ElectionScore, EvaluateSupport, ExtendedBalance, PerThing128, Supports, VoteWeight,
};
use sp_runtime::{
	traits::Zero, transaction_validity::TransactionPriority, InnerOf, PerThing, Perbill,
	RuntimeDebug,
};
use sp_std::prelude::*;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[macro_use]
pub(crate) mod macros;

pub mod signed;
pub mod unsigned;

/// The compact solution type used by this crate. This is provided from the [`ElectionDataProvider`]
/// implementer.
pub type CompactOf<T> = <<T as Config>::ElectionDataProvider as ElectionDataProvider<
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::BlockNumber,
>>::CompactSolution;

/// The voter index. Derived from [`CompactOf`].
pub type CompactVoterIndexOf<T> = <CompactOf<T> as CompactSolution>::Voter;
/// The target index. Derived from [`CompactOf`].
pub type CompactTargetIndexOf<T> = <CompactOf<T> as CompactSolution>::Target;
/// The accuracy of the election. Derived from [`CompactOf`].
pub type CompactAccuracyOf<T> = <CompactOf<T> as CompactSolution>::VoteWeight;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

type PositiveImbalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;

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
/// [`Module::feasibility_check`]
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
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
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

/// Witness data about the size of the election.
///
/// This is needed for proper weight calculation.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, Default)]
pub struct WitnessData {
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
	/// Desired number of winners to be elected for this round.
	pub desired_targets: u32,
}

/// The crate errors.
///
/// Note that this is different from the [`PalletError`].
#[derive(RuntimeDebug, Eq, PartialEq)]
pub enum Error {
	/// A feasibility error.
	Feasibility(FeasibilityError),
	/// An error in the on-chain fallback.
	OnChainFallback(crate::onchain::Error),
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	///
	/// This can only happen in the unsigned phase.
	PoolSubmissionFailed,
}

impl From<crate::onchain::Error> for Error {
	fn from(e: crate::onchain::Error) -> Self {
		Error::OnChainFallback(e)
	}
}

impl From<sp_npos_elections::Error> for Error {
	fn from(e: sp_npos_elections::Error) -> Self {
		Error::NposElections(e)
	}
}

impl From<FeasibilityError> for Error {
	fn from(e: FeasibilityError) -> Self {
		Error::Feasibility(e)
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
}

impl From<sp_npos_elections::Error> for FeasibilityError {
	fn from(e: sp_npos_elections::Error) -> Self {
		FeasibilityError::NposElection(e)
	}
}

pub trait WeightInfo {
	fn open_signed_phase() -> Weight;
	fn open_unsigned_phase() -> Weight;
	fn feasibility_check(v: u32, t: u32, a: u32, d: u32) -> Weight;
	fn submit(v: u32, t: u32, a: u32, d: u32) -> Weight;
	fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight;
}


impl WeightInfo for () {
	fn feasibility_check(_: u32, _: u32, _: u32, _: u32) -> Weight {
		Default::default()
	}
	fn submit(_: u32, _: u32, _: u32, _: u32) -> Weight {
		Default::default()
	}
	fn submit_unsigned(_: u32, _: u32, _: u32, _: u32) -> Weight {
		Default::default()
	}
	fn open_signed_phase() -> Weight {
		Default::default()
	}
	fn open_unsigned_phase() -> Weight {
		Default::default()
	}
}

pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<Self>>>,
{
	/// Event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;

	/// Currency type.
	type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

	/// Duration of the signed phase.
	type SignedPhase: Get<Self::BlockNumber>;
	/// Duration of the unsigned phase.
	type UnsignedPhase: Get<Self::BlockNumber>;
	/// Maximum number of singed submissions that can be queued.
	type MaxSignedSubmissions: Get<u32>;

	type SignedRewardBase: Get<BalanceOf<Self>>;
	type SignedRewardFactor: Get<Perbill>;
	type SignedRewardMax: Get<Option<BalanceOf<Self>>>;

	type SignedDepositBase: Get<BalanceOf<Self>>;
	type SignedDepositByte: Get<BalanceOf<Self>>;
	type SignedDepositWeight: Get<BalanceOf<Self>>;

	/// The minimum amount of improvement to the solution score that defines a solution as "better".
	type SolutionImprovementThreshold: Get<Perbill>;

	/// The priority of the unsigned transaction submitted in the unsigned-phase
	type UnsignedPriority: Get<TransactionPriority>;
	/// Maximum number of iteration of balancing that will be executed in the embedded miner of the
	/// pallet.
	type MinerMaxIterations: Get<u32>;
	/// Maximum weight that the miner should consume.
	type MinerMaxWeight: Get<Weight>;

	/// Handler for the slashed deposits.
	type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;
	/// Handler for the rewards.
	type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;

	/// Something that will provide the election data.
	type ElectionDataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;

	/// The weight of the pallet.
	type WeightInfo: WeightInfo;
}

decl_storage! {
	trait Store for Module<T: Config> as TwoPhaseElectionProvider where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {
		/// Internal counter for the number of rounds.
		///
		/// This is useful for de-duplication of transactions submitted to the pool, and general
		/// diagnostics of the module.
		///
		/// This is merely incremented once per every time that signed phase starts.
		pub Round get(fn round): u32 = 0;
		/// Current phase.
		pub CurrentPhase get(fn current_phase): Phase<T::BlockNumber> = Phase::Off;

		/// Sorted (worse -> best) list of unchecked, signed solutions.
		pub SignedSubmissions get(fn signed_submissions): Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>;

		/// Current best solution, signed or unsigned.
		pub QueuedSolution get(fn queued_solution): Option<ReadySolution<T::AccountId>>;

		/// Snapshot data of the round.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub Snapshot get(fn snapshot): Option<RoundSnapshot<T::AccountId>>;
	}
}

decl_event!(
	pub enum Event<T> where <T as frame_system::Config>::AccountId {
		/// A solution was stored with the given compute.
		///
		/// If the solution is signed, this means that it hasn't yet been processed. If the solution
		/// is unsigned, this means that it has also been processed.
		SolutionStored(ElectionCompute),
		/// The election has been finalized, with `Some` of the given computation, or else if the
		/// election failed, `None`.
		ElectionFinalized(Option<ElectionCompute>),
		/// An account has been rewarded for their signed submission being finalized.
		Rewarded(AccountId),
		/// An account has been slashed for submitting an invalid signed submission.
		Slashed(AccountId),
	}
);

frame_support::decl_error! {
	pub enum PalletError for Module<T: Config> where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {
		/// Submission was too early.
		EarlySubmission,
		/// Submission was too weak, score-wise.
		WeakSubmission,
		/// The queue was full, and the solution was not better than any of the existing ones.
		QueueFull,
		/// The origin failed to pay the deposit.
		CannotPayDeposit,
		/// WitnessData is invalid.
		InvalidWitness,
		/// Round number is invalid.
		InvalidRound,
	}
}

decl_module! {
	pub struct Module<T: Config> for enum Call
	where
		origin: T::Origin,
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
		type Error = PalletError<T>;
		fn deposit_event() = default;

		fn on_initialize(now: T::BlockNumber) -> Weight {
			let next_election = T::ElectionDataProvider::next_election_prediction(now);
			let next_election = next_election.max(now);

			let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
			let unsigned_deadline = T::UnsignedPhase::get();

			let remaining = next_election - now;
			match Self::current_phase() {
				Phase::Off if remaining <= signed_deadline && remaining > unsigned_deadline => {
					// signed phae can only start after Off.
					<CurrentPhase<T>>::put(Phase::Signed);
					Round::mutate(|r| *r +=1);
					Self::start_signed_phase();
					log!(info, "Starting signed phase at #{:?} , round {}.", now, Self::round());
					T::WeightInfo::open_signed_phase()
				},
				Phase::Signed | Phase::Off if remaining <= unsigned_deadline && remaining > 0u32.into() => {
					// unsigned phase can start after Off or Signed.
					let _ = Self::finalize_signed_phase();
					<CurrentPhase<T>>::put(Phase::Unsigned((true, now)));
					log!(info, "Starting unsigned phase at #{:?}.", now);
					T::WeightInfo::open_unsigned_phase()
				},
				_ => {
					Zero::zero()
				}
			}
		}

		fn offchain_worker(n: T::BlockNumber) {
			// We only run the OCW in the fist block of the unsigned phase.
			if
				Self::set_check_offchain_execution_status(n).is_ok() &&
				Self::current_phase().is_unsigned_open_at(n)
			{
				let _ = Self::mine_and_submit().map_err(|e| {
					log!(error, "error while submitting transaction in OCW: {:?}", e)
				});
			}
		}

		/// Submit a solution for the signed phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// The solution is potentially queued, based on the claimed score and processed at the end
		/// of the signed phase.
		///
		/// A deposit is reserved and recorded for the solution. Based on the outcome, the solution
		/// might be rewarded, slashed, or get all or a part of the deposit back.
		#[weight = T::WeightInfo::submit(0, 0, 0, 0)]
		fn submit(origin, solution: RawSolution<CompactOf<T>>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure solution is timely.
			ensure!(Self::current_phase().is_signed(), PalletError::<T>::EarlySubmission);

			// ensure round is correct.
			ensure!(Self::round() == solution.round, PalletError::<T>::InvalidRound);

			// NOTE: this is the only case where having separate snapshot would have been better
			// because could do just decode_len. But we can create abstractions to do this.

			// build witness.
			// defensive-only: if phase is signed, snapshot will exist.
			let RoundSnapshot { voters, targets, .. } = Self::snapshot().unwrap_or_default();
			let witness = WitnessData { voters: voters.len() as u32, targets: targets.len() as u32 };

			// ensure solution claims is better.
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index = Self::insert_submission(&who, &mut signed_submissions, solution, witness);
			ensure!(maybe_index.is_some(), PalletError::<T>::QueueFull);
			let index = maybe_index.expect("Option checked to be `Some`; qed.");

			// collect deposit. Thereafter, the function cannot fail.
			// Defensive -- index is valid.
			let deposit = signed_submissions.get(index).map(|s| s.deposit).unwrap_or_default();
			T::Currency::reserve(&who, deposit).map_err(|_| PalletError::<T>::CannotPayDeposit)?;

			// store the new signed submission.
			debug_assert!(signed_submissions.len() as u32 <= T::MaxSignedSubmissions::get());
			<SignedSubmissions<T>>::put(signed_submissions);

			Self::deposit_event(RawEvent::SolutionStored(ElectionCompute::Signed));
			Ok(None.into())
		}

		/// Submit a solution for the unsigned phase.
		///
		/// The dispatch origin fo this call must be __signed__.
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
		#[weight = T::WeightInfo::submit_unsigned(
			witness.voters,
			witness.targets,
			solution.compact.voters_count() as u32,
			solution.compact.unique_targets().len() as u32
		)]
		fn submit_unsigned(origin, solution: RawSolution<CompactOf<T>>, witness: WitnessData) {
			ensure_none(origin)?;

			// check phase and score.
			// NOTE: since we do this in pre-dispatch, we can just ignore it here.
			let _ = Self::unsigned_pre_dispatch_checks(&solution)?;

			// ensure witness was correct.
			let RoundSnapshot { voters, targets, .. } = Self::snapshot().unwrap_or_default();
			ensure!(voters.len() as u32 == witness.voters, PalletError::<T>::InvalidWitness);
			ensure!(targets.len() as u32 == witness.targets, PalletError::<T>::InvalidWitness);

			let ready =
				Self::feasibility_check(solution, ElectionCompute::Unsigned)
					.expect(
						"Invalid unsigned submission must produce invalid block and deprive \
						validator from their authoring reward."
					);

			// store the newly received solution.
			<QueuedSolution<T>>::put(ready);
			Self::deposit_event(RawEvent::SolutionStored(ElectionCompute::Unsigned));
		}
	}
}

impl<T: Config> Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
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
		let RawSolution { compact, score, .. } = solution;

		// winners are not directly encoded in the solution.
		let winners = compact.unique_targets();

		// read the entire snapshot. NOTE: could be optimized.
		let RoundSnapshot {
			voters: snapshot_voters,
			targets: snapshot_targets,
			desired_targets,
		} = Self::snapshot().ok_or(FeasibilityError::SnapshotUnavailable)?;

		ensure!(
			winners.len() as u32 == desired_targets,
			FeasibilityError::WrongWinnerCount,
		);

		// ----- Start building. First, we need some closures.
		let voter_at = crate::voter_at_fn!(snapshot_voters, T::AccountId, T);
		let target_at = crate::target_at_fn!(snapshot_targets, T::AccountId, T);

		// first, make sure that all the winners are sane.
		let winners = winners
			.into_iter()
			.map(|i| target_at(i).ok_or(FeasibilityError::InvalidWinner))
			.collect::<Result<Vec<T::AccountId>, FeasibilityError>>()?;

		// Then convert compact -> Assignment.
		let assignments = compact
			.into_assignment(voter_at, target_at)
			.map_err::<FeasibilityError, _>(Into::into)?;

		// Ensure that assignments is correct. We perform two checks: 1. local match against the
		// given snapshot, and check with the `ElectionDataProvider`.
		let _ = assignments
			.iter()
			.map(|Assignment { who, distribution }| {
				snapshot_voters.iter().find(|(v, _, _)| v == who).map_or(
					Err(FeasibilityError::InvalidVoter),
					|(_voter, _stake, targets)| {
						if distribution.iter().map(|(d, _)| d).all(|d| targets.contains(d))
							&& T::ElectionDataProvider::feasibility_check_assignment::<
								CompactAccuracyOf<T>,
							>(who, distribution)
						{
							Ok(())
						} else {
							Err(FeasibilityError::InvalidVote)
						}
					},
				)
			})
			.collect::<Result<(), FeasibilityError>>()?;

		// ----- Start building support. First, we need some more closures.
		let stake_of = stake_of_fn!(snapshot_voters, T::AccountId);

		// This might fail if the normalization fails. Very unlikely.
		let staked_assignments = assignment_ratio_to_staked_normalized(assignments, stake_of)
			.map_err::<FeasibilityError, _>(Into::into)?;
		// This might fail if one of the voter edges is pointing to a non-winner.
		let supports = sp_npos_elections::to_supports(&winners, &staked_assignments)
			.map_err::<FeasibilityError, _>(Into::into)?;

		// Finally, check that the claimed score was indeed correct.
		let known_score = supports.evaluate();
		ensure!(known_score == score, FeasibilityError::InvalidScore);

		// let supports = supports.flatten();
		Ok(ReadySolution {
			supports,
			compute,
			score,
		})
	}

	/// On-chain fallback of election.
	fn onchain_fallback() -> Result<Supports<T::AccountId>, Error> {
		// If the length of singed phase is zero, the signed phase never starts and thus snapshot is
		// never created.
		let get_snapshot_backup = || {
			let targets = T::ElectionDataProvider::targets();
			let voters = T::ElectionDataProvider::voters();
			let desired_targets = T::ElectionDataProvider::desired_targets();

			RoundSnapshot {
				voters,
				targets,
				desired_targets,
			}
		};

		let RoundSnapshot {
			desired_targets,
			voters,
			targets,
		} = Self::snapshot().unwrap_or_else(get_snapshot_backup);
		<OnChainSequentialPhragmen as ElectionProvider<T::AccountId>>::elect::<Perbill>(
			desired_targets as usize,
			targets,
			voters,
		)
		.map_err(Into::into)
	}
}

impl<T: Config> ElectionProvider<T::AccountId> for Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	const NEEDS_ELECT_DATA: bool = false;
	type Error = Error;

	fn elect<P: PerThing128>(
		_to_elect: usize,
		_targets: Vec<T::AccountId>,
		_voters: Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
	) -> Result<Supports<T::AccountId>, Self::Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>,
	{
		Self::queued_solution()
			.map_or_else(
				|| {

					Self::onchain_fallback()
						.map(|r| (r, ElectionCompute::OnChain))
						.map_err(Into::into)
				},
				|ReadySolution { supports, compute, ..}| Ok((supports, compute)),
			)
			.map(|(supports, compute)| {
				// reset phase.
				<CurrentPhase<T>>::put(Phase::Off);
				// clear snapshots.
				<Snapshot<T>>::kill();

				Self::deposit_event(RawEvent::ElectionFinalized(Some(compute)));
				log!(info, "Finalized election round with compute {:?}.", compute);
				supports
			})
			.map_err(|err| {
				Self::deposit_event(RawEvent::ElectionFinalized(None));
				log!(error, "Failed to finalize election round. Error = {:?}", err);
				err
			})
	}

	fn ongoing() -> bool {
		matches!(Self::current_phase(), Phase::Signed | Phase::Unsigned(_))
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, *};
	use sp_election_providers::ElectionProvider;
	use sp_npos_elections::Support;

	#[test]
	fn phase_rotation_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 0 ------- 15 -------------- 25 ------- 30 ------- ------- 45 ------- 55 ------- 60
			//           |                |
			//         Signed           Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert_eq!(TwoPhase::round(), 0);

			roll_to(4);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot().is_none());
			assert_eq!(TwoPhase::round(), 0);

			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(24);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(25);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));
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

			TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
				.unwrap();

			assert!(TwoPhase::current_phase().is_off());
			assert!(TwoPhase::snapshot().is_none());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(44);
			assert!(TwoPhase::current_phase().is_off());

			roll_to(45);
			assert!(TwoPhase::current_phase().is_signed());

			roll_to(55);
			assert!(TwoPhase::current_phase().is_unsigned_open_at(55));
		})
	}

	#[test]
	fn onchain_backup_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			roll_to(25);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 25)));

			// zilch solutions thus far.
			let supports =
				TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
					.unwrap();

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
			dbg!(TwoPhase::current_phase());
			assert!(TwoPhase::current_phase().is_unsigned_open_at(20));

			roll_to(30);
			assert!(TwoPhase::current_phase().is_unsigned_open_at(20));

			let _ =
				TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
					.unwrap();

			assert!(TwoPhase::current_phase().is_off());
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

			roll_to(30);
			assert!(TwoPhase::current_phase().is_signed());

			let _ =
				TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
					.unwrap();

			assert!(TwoPhase::current_phase().is_off());
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
			let _ =
				TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
					.unwrap();

			assert!(TwoPhase::current_phase().is_off());
		});
	}
}
