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
//! As the name suggests, this election provider has two distinct phases (see [`Phase`]), signed and
//! unsigned.
//!
//! ## Phases
//!
//! The timeline of pallet is as follows. At each block,
//! [`ElectionDataProvider::next_election_prediction`] is used to estimate the time remaining to the
//! next call to `elect`. Based on this, a phase is chosen. The timeline is as follows.
//!
//! ```ignore
//!                                                                    elect()
//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
//!   +-------------------------------------------------------------------+
//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
//!
//! Note that the unsigned phase starts `T::UnsignedPhase` blocks before the
//! `next_election_prediction`, but only ends when a call to `ElectionProvider::elect` happens.
//!
//! ```
//! ### Signed Phase
//!
//!	In the signed phase, solutions (of type [`RawSolution`]) are submitted and queued on chain. A
//! deposit is reserved, based on the size of the solution, for the cost of keeping this solution
//! on-chain for a number of blocks. A maximum of [`Trait::MaxSignedSubmissions`] solutions are
//! stored. The queue is always sorted based on score (worse -> best).
//!
//! Upon arrival of a new solution:
//!
//! 1. If the queue is not full, it is stored.
//! 2. If the queue is full but the submitted solution is better than one of the queued ones, the
//!    worse solution is discarded (TODO: what to do with the bond?) and the new solution is stored
//!    in the correct index.
//! 3. If the queue is full and the solution is not an improvement compared to any of the queued
//!    ones, it is instantly rejected and no additional bond is reserved.
//!
//! A signed solution cannot be reversed, taken back, updated, or retracted. In other words, the
//! origin can not bail out in any way.
//!
//! Upon the end of the signed phase, the solutions are examined from worse to best (i.e. `pop()`ed
//! until drained). Each solution undergoes an expensive [`Module::feasibility_check`], which ensure
//! the score claimed by this score was correct, among other checks. At each step, if the current
//! best solution is passes the feasibility check, it is considered to be the best one. The sender
//! of the origin is rewarded, and the rest of the queued solutions get their deposit back, without
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
//! TODO: what if length of some phase is zero?
//!
//! Note that both of the bottom solutions end up being discarded and get their deposit back,
//! despite one of them being invalid.
//!
//! ## Unsigned Phase
//!
//! If signed phase ends with a good solution, then the unsigned phase will be `active`
//! ([`Phase::Unsigned(true)`]), else the unsigned phase will be `passive`.
//!
//! TODO
//!
//! ### Fallback
//!
//! If we reach the end of both phases (i.e. call to `ElectionProvider::elect` happens) and no good
//! solution is queued, then we fallback to an on-chain election. The on-chain election is slow, and
//! contains to balancing or reduction post-processing.
//!
//! ## Correct Submission
//!
//! TODO
//!
//! ## Accuracy
//!
//! TODO
//!

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

#[cfg(any(feature = "runtime-benchmarks", test))]
pub mod benchmarking;
#[cfg(test)]
mod mock;
#[macro_use]
pub(crate) mod macros;

pub mod signed;
pub mod unsigned;

/// The compact solution type used by this crate. This is provided from the [`ElectionDataProvider`]
/// implementer.
pub type CompactOf<T> = <<T as Trait>::ElectionDataProvider as ElectionDataProvider<
	<T as frame_system::Trait>::AccountId,
	<T as frame_system::Trait>::BlockNumber,
>>::CompactSolution;

/// The voter index. Derived from [`CompactOf`].
pub type CompactVoterIndexOf<T> = <CompactOf<T> as CompactSolution>::Voter;
/// The target index. Derived from [`CompactOf`].
pub type CompactTargetIndexOf<T> = <CompactOf<T> as CompactSolution>::Target;
/// The accuracy of the election. Derived from [`CompactOf`].
pub type CompactAccuracyOf<T> = <CompactOf<T> as CompactSolution>::VoteWeight;

type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

type PositiveImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

/// Current phase of the pallet.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Phase<Bn> {
	/// Nothing, the election is not happening.
	Off,
	/// Signed phase is open.
	Signed,
	/// Unsigned phase is open.
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
/// Such a solution should never become effective in anyway before being checked by the
/// [`Module::feasibility_check`]
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct RawSolution<C> {
	/// Compact election edges.
	compact: C,
	/// The _claimed_ score of the solution.
	score: ElectionScore,
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

/// A checked and parsed solution, ready to be enacted.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct ReadySolution<A> {
	/// The final supports of the solution. This is target-major vector, storing each winners, total
	/// backing, and each individual backer.
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

/// The crate errors. Note that this is different from the [`PalletError`].
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
	NposElectionError(sp_npos_elections::Error),
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
		FeasibilityError::NposElectionError(e)
	}
}

/// The weights for this pallet.
pub trait WeightInfo {
	fn feasibility_check() -> Weight;
	fn submit() -> Weight;
	fn submit_unsigned() -> Weight;
}

impl WeightInfo for () {
	fn feasibility_check() -> Weight {
		Default::default()
	}
	fn submit() -> Weight {
		Default::default()
	}
	fn submit_unsigned() -> Weight {
		Default::default()
	}
}

pub trait Trait: frame_system::Trait + SendTransactionTypes<Call<Self>>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<Self>>>,
{
	/// Event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// Currency type.
	type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

	/// Duration of the signed phase.
	type SignedPhase: Get<Self::BlockNumber>;
	/// Duration of the unsigned phase.
	type UnsignedPhase: Get<Self::BlockNumber>;
	/// Maximum number of singed submissions that can be queued.
	type MaxSignedSubmissions: Get<u32>;

	// TODO: these need input from the research team
	type SignedRewardBase: Get<BalanceOf<Self>>;
	type SignedRewardFactor: Get<Perbill>;
	type SignedRewardMax: Get<Option<BalanceOf<Self>>>;
	type SignedDepositBase: Get<BalanceOf<Self>>;
	type SignedDepositByte: Get<BalanceOf<Self>>;
	type SignedDepositWeight: Get<BalanceOf<Self>>;

	/// The minimum amount of improvement to the solution score that defines a solution as "better".
	type SolutionImprovementThreshold: Get<Perbill>;

	type UnsignedMaxIterations: Get<u32>;
	type UnsignedPriority: Get<TransactionPriority>;

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
	trait Store for Module<T: Trait> as TwoPhaseElectionProvider where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {
		/// Internal counter ofr the number of rounds.
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

		/// Snapshot of all Voters.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub SnapshotTargets get(fn snapshot_targets): Option<Vec<T::AccountId>>;

		/// Snapshot of all targets.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub SnapshotVoters get(fn snapshot_voters): Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>>;

		/// Desired number of targets to elect.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub DesiredTargets get(fn desired_targets): u32;
	}
}

decl_event!(
	pub enum Event<T> where <T as frame_system::Trait>::AccountId {
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
	pub enum PalletError for Module<T: Trait> where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {
		/// Submission was too early.
		EarlySubmission,
		/// Submission was too weak, score-wise.
		WeakSubmission,
		/// The queue was full, and the solution was not better than any of the existing ones.
		QueueFull,
		/// The origin failed to pay the deposit.
		CannotPayDeposit,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call
	where
		origin: T::Origin,
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
		// TODO: replace with PalletError once we have it working.
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
					// check only for the signed phase.
					<CurrentPhase<T>>::put(Phase::Signed);
					Round::mutate(|r| *r +=1);
					Self::start_signed_phase();
					log!(info, "Starting signed phase at #{} , round {}", now, Self::round());
				},
				Phase::Signed if remaining <= unsigned_deadline && remaining > 0.into() => {
					// check the unsigned phase.
					// TODO: this is probably very bad as it is.. we should only assume we don't
					// want OCW solutions if the solutions is checked to be PJR as well. Probably a
					// good middle ground for now is to always let the unsigned phase be open.
					let found_solution = Self::finalize_signed_phase();
					<CurrentPhase<T>>::put(Phase::Unsigned((!found_solution, now)));
					log!(info, "Starting unsigned phase at #{}", now);
				},
				_ => {
					// Nothing. We wait in the unsigned phase until we receive the call to `elect`.
				}
			}

			Default::default()
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
		/// The solution potentially queued, based on the claimed score and processed at the end of
		/// the signed phase.
		///
		/// A deposit is reserved and recorded for the solution. Based on the outcome, the solution
		/// might be rewarded, slashed, or get all or a part of the deposit back.
		#[weight = T::WeightInfo::submit()]
		fn submit(origin, solution: RawSolution<CompactOf<T>>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure solution is timely.
			ensure!(Self::current_phase().is_signed(), PalletError::<T>::EarlySubmission);

			// ensure solution claims is better.
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index = Self::insert_submission(&who, &mut signed_submissions, solution);
			ensure!(maybe_index.is_some(), "QueueFull");
			let index = maybe_index.expect("Option checked to be `Some`; qed.");

			// collect deposit. Thereafter, the function cannot fail.
			let deposit = signed_submissions[index].deposit;
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
		#[weight = T::WeightInfo::submit_unsigned()]
		fn submit_unsigned(origin, solution: RawSolution<CompactOf<T>>) {
			ensure_none(origin)?;

			// check phase and score.
			// TODO: since we do this in pre-dispatch, we can just ignore it
			// here.
			let _ = Self::pre_dispatch_checks(&solution)?;

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

impl<T: Trait> Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	/// Checks the feasibility of a solution.
	///
	/// This checks the solution for the following:
	///
	/// 0. **all** of the used indices must be correct.
	/// 1. present correct number of winners.
	/// 2. any assignment is checked to match with `SnapshotVoters`.
	/// 3. for each assignment, the check of `ElectionDataProvider` is also examined.
	/// 4. the claimed score is valid.
	fn feasibility_check(
		solution: RawSolution<CompactOf<T>>,
		compute: ElectionCompute,
	) -> Result<ReadySolution<T::AccountId>, FeasibilityError> {
		let RawSolution { compact, score } = solution;

		// winners are not directly encoded in the solution.
		// TODO: dupe winner
		// TODO: dupe in compact.
		let winners = compact.unique_targets();

		// Ensure that we have received enough winners.
		ensure!(
			winners.len() as u32 == Self::desired_targets(),
			FeasibilityError::WrongWinnerCount
		);

		// ----- Start building. First, we need some closures.
		let snapshot_voters =
			Self::snapshot_voters().ok_or(FeasibilityError::SnapshotUnavailable)?;
		let snapshot_targets =
			Self::snapshot_targets().ok_or(FeasibilityError::SnapshotUnavailable)?;

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
					|(_, _, t)| {
						if distribution.iter().map(|(x, _)| x).all(|x| t.contains(x))
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
		dbg!(known_score, score);
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
		let desired_targets = Self::desired_targets() as usize;
		let voters = Self::snapshot_voters().ok_or(Error::SnapshotUnAvailable)?;
		let targets = Self::snapshot_targets().ok_or(Error::SnapshotUnAvailable)?;
		<OnChainSequentialPhragmen as ElectionProvider<T::AccountId>>::elect::<Perbill>(
			desired_targets,
			targets,
			voters,
		)
		.map_err(Into::into)
	}
}

impl<T: Trait> ElectionProvider<T::AccountId> for Module<T>
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
				<SnapshotVoters<T>>::kill();
				<SnapshotTargets<T>>::kill();

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
			// 0 ------- 5 -------------- 15 ------- 20
			//           |                |
			//         Signed           Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert_eq!(TwoPhase::round(), 0);

			roll_to(4);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot_voters().is_none());
			assert_eq!(TwoPhase::round(), 0);

			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot_voters().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(14);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot_voters().is_some());
			assert_eq!(TwoPhase::round(), 1);

			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(19);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(20);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));
			assert!(TwoPhase::snapshot_voters().is_some());

			// we close when upstream tells us to elect.
			roll_to(21);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));
			assert!(TwoPhase::snapshot_voters().is_some());

			TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
				.unwrap();
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot_voters().is_none());
			assert_eq!(TwoPhase::round(), 1);
		})
	}

	#[test]
	fn onchain_backup_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			roll_to(20);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

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
}
