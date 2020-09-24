use crate::{onchain::OnChainSequentialPhragmen, ElectionProvider, Error};
use codec::{Decode, Encode, HasCompact};
use frame_support::{
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
	weights::Weight,
};
use frame_system::{ensure_none, ensure_signed};
use sp_npos_elections::{
	generate_solution_type, is_score_better, ElectionScore, ExtendedBalance, FlatSupportMap,
	VoteWeight,
};
use sp_runtime::{traits::Zero, PerThing, PerU16, Perbill, RuntimeDebug};
use sp_std::{mem::size_of, prelude::*};

pub trait ElectionDataProvider<AccountId, B> {
	fn targets() -> (Vec<AccountId>, Weight);
	fn voters() -> (Vec<(AccountId, VoteWeight, Vec<AccountId>)>, Weight);
	fn desired_targets() -> (u32, Weight);
	fn next_election_prediction() -> (B, Weight);
}

type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

type PositiveImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

/// Accuracy used for on-chain election.
pub type ChainAccuracy = Perbill;

/// Accuracy used for off-chain election. This better be small.
pub type OffchainAccuracy = PerU16;

/// Data type used to index nominators in the compact type
pub type VoterIndex = u32;

/// Data type used to index validators in the compact type.
pub type TargetIndex = u16;

// Ensure the size of both TargetIndex and VoterIndex. They both need to be well below usize.
static_assertions::const_assert!(size_of::<TargetIndex>() <= size_of::<usize>());
static_assertions::const_assert!(size_of::<VoterIndex>() <= size_of::<usize>());
static_assertions::const_assert!(size_of::<TargetIndex>() <= size_of::<u32>());
static_assertions::const_assert!(size_of::<VoterIndex>() <= size_of::<u32>());

// TODO: deal with 16 being defined here.
generate_solution_type!(
	#[compact]
	pub struct CompactAssignments::<VoterIndex, TargetIndex, OffchainAccuracy>(16)
);

#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Phase {
	Off,
	Signed,
	Unsigned(bool),
}

impl Default for Phase {
	fn default() -> Self {
		Phase::Off
	}
}

impl Phase {
	pub fn is_signed(&self) -> bool {
		matches!(self, Phase::Signed)
	}

	pub fn is_unsigned(&self) -> bool {
		matches!(self, Phase::Unsigned(_))
	}

	pub fn is_unsigned_open(&self) -> bool {
		matches!(self, Phase::Unsigned(true))
	}

	pub fn is_off(&self) -> bool {
		matches!(self, Phase::Off)
	}
}

#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum ElectionCompute {
	OnChain,
	Signed,
	Unsigned,
}

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct RawSolution<AccountId> {
	winners: Vec<AccountId>,
	compact: CompactAssignments,
	score: ElectionScore,
}

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct SignedSubmission<AccountId, Balance: HasCompact> {
	who: AccountId,
	deposit: Balance,
	reward: Balance,
	solution: RawSolution<AccountId>,
}

/// A parsed solution, ready to be enacted.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct ReadySolution<AccountId> {
	winners: Vec<AccountId>,
	supports: FlatSupportMap<AccountId>,
}

pub trait WeightInfo {}

pub trait Trait: frame_system::Trait {
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

	type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

	type SignedPhase: Get<Self::BlockNumber>;
	type UnsignedPhase: Get<Self::BlockNumber>;

	type MaxSignedSubmissions: Get<u32>;

	type SignedRewardBase: Get<BalanceOf<Self>>;
	type SignedRewardFactor: Get<BalanceOf<Self>>;

	type SolutionImprovementThreshold: Get<Perbill>;

	type SubmissionBondBase: Get<BalanceOf<Self>>;
	type SubmissionBondByte: Get<BalanceOf<Self>>;

	type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;
	type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;

	type ElectionDataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;

	type WeightInfo: WeightInfo;
}

decl_storage! {
	trait Store for Module<T: Trait> as TwoPhaseElectionProvider {
		/// Current phase.
		pub CurrentPhase get(fn current_phase): Phase = Phase::Off;

		/// Sorted list of unchecked, signed solutions.
		pub SignedSubmissions get(fn signed_submissions): Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>;

		/// Current, best, unsigned solution.
		pub QueuedSolution get(fn queued_solution): Option<ReadySolution<T::AccountId>>;

		/// Raw targets.
		/// Snapshot of all Voters. The indices if this will be used in election.
		pub SnapshotTargets get(fn snapshot_targets): Vec<T::AccountId>;

		/// Raw voters.
		/// Snapshot of all targets. The indices if this will be used in election.
		pub SnapshotVoters get(fn snapshot_voters): Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>;

		/// Desired number of targets to elect
		pub DesiredTargets get(fn desired_targets): u32;
	}
}

decl_event!(
	pub enum Event {
		SolutionStored(ElectionCompute),
		ElectionFinalized(ElectionCompute),
	}
);

decl_error! {
	pub enum PalletError for Module<T: Trait> {
		EarlySubmission,
		LowScoreSubmission,
		SubmissionQueuedFull,
		CannotPayDeposit,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		fn on_initialize(now: T::BlockNumber) -> Weight {
			let (next_election, weight) = T::ElectionDataProvider::next_election_prediction();
			// TODO: document this invariant.
			let next_election = next_election.max(now);

			let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
			let unsigned_deadline = T::UnsignedPhase::get();

			let remaining = next_election - now;
			match Self::current_phase() {
				Phase::Off => {
					// check only for the signed phase. Note that next
					if remaining < signed_deadline {
						let w = Self::start_signed_phase();
					}
				},
				Phase::Signed => {
					// check the unsigned phase.
					if remaining < unsigned_deadline {
						let (found_solution, w) = Self::finalize_signed_phase();
						CurrentPhase::put(Phase::Unsigned(!found_solution));
					}
				},
				Phase::Unsigned(_) => {
					// Nothing. We wait in the unsigned phase until we receive the call to `elect`.
				}
			}


			Default::default()
		}

		fn offchain_worker(n: T::BlockNumber) {

		}

		#[weight = 0]
		fn submit(origin, solution: RawSolution<T::AccountId>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure solution is timely.
			ensure!(Self::current_phase().is_signed(), PalletError::<T>::EarlySubmission);

			// ensure queued is not full.
			let queue_size = <SignedSubmissions<T>>::decode_len().unwrap_or_default() as u32;
			ensure!(
				queue_size < T::MaxSignedSubmissions::get(),
				PalletError::<T>::SubmissionQueuedFull,
			);

			// ensure solution claims is better.
			let mut signed_submissions = Self::signed_submissions();
			let improvement = signed_submissions.last().map_or(
				true,
				|best: &SignedSubmission<_, _>| -> bool {
					is_score_better(
						solution.score,
						best.solution.score,
						T::SolutionImprovementThreshold::get()
					)
				}
			);
			ensure!(improvement, PalletError::<T>::LowScoreSubmission);

			// ensure... what else?
			// TODO

			// collect deposit. Thereafter, the function cannot fail.
			let deposit = Self::deposit_for(&solution);
			T::Currency::reserve(&who, deposit).map_err(|_| PalletError::<T>::CannotPayDeposit)?;

			// amount to be rewarded if this solution is accepted.
			let reward = Self::reward_for(&solution);

			signed_submissions.push(SignedSubmission { who, deposit, reward, solution });
			<SignedSubmissions<T>>::put(signed_submissions);

			Ok(None.into())
		}

		#[weight = 0]
		fn submit_unsigned(origin, solution: RawSolution<T::AccountId>) {
			ensure_none(origin)?;
			unimplemented!()
		}
	}
}

impl<T: Trait> Module<T> {
	fn start_signed_phase() -> Weight {
		let (targets, w1) = T::ElectionDataProvider::targets();
		// TODO: this module is not aware at all of self-vote. Clarify this.
		let (voters, w2) = T::ElectionDataProvider::voters();
		let (desired_targets, w3) = T::ElectionDataProvider::desired_targets();

		<SnapshotTargets<T>>::put(targets);
		<SnapshotVoters<T>>::put(voters);
		DesiredTargets::put(desired_targets);

		CurrentPhase::put(Phase::Signed);
		Default::default()
	}

	/// Returns true if we have a good solution in the signed phase.
	fn finalize_signed_phase() -> (bool, Weight) {
		let mut all_submission: Vec<SignedSubmission<_, _>> = <SignedSubmissions<T>>::take();
		let mut found_solution = false;

		while let Some(best) = all_submission.pop() {
			let SignedSubmission {
				solution,
				who,
				deposit,
				reward,
			} = best;
			match Self::feasibility_check(solution) {
				(Ok(ready_solution), w) => {
					<QueuedSolution<T>>::put(ready_solution);

					// unreserve deposit.
					let _remaining = T::Currency::unreserve(&who, deposit);
					debug_assert!(_remaining.is_zero());

					// Reward.
					let positive_imbalance = T::Currency::deposit_creating(&who, reward);
					T::RewardHandler::on_unbalanced(positive_imbalance);

					found_solution = true;
					break;
				}
				(Err(_), w) => {
					let (negative_imbalance, _remaining) =
						T::Currency::slash_reserved(&who, deposit);
					debug_assert!(_remaining.is_zero());
					T::SlashHandler::on_unbalanced(negative_imbalance);
				}
			}
		}

		// Any unprocessed solution is not pointless to even ponder upon. Feasible or malicious,
		// they didn't end up being used. Unreserve the bonds.
		all_submission.into_iter().for_each(|not_processed| {
			let SignedSubmission { who, deposit, .. } = not_processed;
			let _remaining = T::Currency::unreserve(&who, deposit);
			debug_assert!(_remaining.is_zero());
		});

		(found_solution, Default::default())
	}

	fn feasibility_check(
		solution: RawSolution<T::AccountId>,
	) -> (Result<ReadySolution<T::AccountId>, ()>, Weight) {
		unimplemented!()
	}

	fn deposit_for(solution: &RawSolution<T::AccountId>) -> BalanceOf<T> {
		unimplemented!()
	}

	fn reward_for(solution: &RawSolution<T::AccountId>) -> BalanceOf<T> {
		T::SignedRewardBase::get()
	}

	fn onchain_fallback() -> Result<FlatSupportMap<T::AccountId>, crate::Error> {
		let desired_targets = Self::desired_targets() as usize;
		let voters = Self::snapshot_voters();
		let targets = Self::snapshot_targets();
		<OnChainSequentialPhragmen as ElectionProvider<T::AccountId>>::elect::<ChainAccuracy>(
			desired_targets,
			targets,
			voters,
		)
	}
}

impl<T: Trait> crate::ElectionProvider<T::AccountId> for Module<T> {
	fn elect<P: PerThing>(
		_to_elect: usize,
		_targets: Vec<T::AccountId>,
		_voters: Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
	) -> Result<FlatSupportMap<T::AccountId>, crate::Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	{
		CurrentPhase::put(Phase::Off);
		Self::queued_solution().map_or_else(
			|| Self::onchain_fallback(),
			|ReadySolution { supports, .. }| Ok(supports),
		)
	}

	fn ongoing() -> bool {
		matches!(Self::current_phase(), Phase::Signed | Phase::Unsigned(_))
	}
}

#[cfg(test)]
mod tests {

	mod signed {
		#[test]
		fn cannot_submit_too_early() {}

		#[test]
		fn should_pay_deposit() {}

		#[test]
		fn cannot_submit_worse() {}

		#[test]
		fn good_solution_is_rewarded() {}

		#[test]
		fn bad_solution_is_slashed() {}

		#[test]
		fn suppressed_solution_gets_bond_back() {}

		#[test]
		fn all_in_one() {
			// a combination of:
			// - good_solution_is_rewarded
			// - bad_solution_is_slashed
			// - suppressed_solution_gets_bond_back
		}
	}

	mod unsigned {}
}
