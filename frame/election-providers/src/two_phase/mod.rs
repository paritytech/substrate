use crate::{onchain::OnChainSequentialPhragmen, ElectionDataProvider, ElectionProvider, Error};
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

#[cfg(test)]
mod mock;
pub mod signed;
pub mod unsigned;

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

/// Data type used to index nominators in the compact type.
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

#[macro_export]
macro_rules! voter_at_fn {
	($voters:ident, $acc:ty) => {
		|who: &$acc| -> Option<$crate::two_phase::VoterIndex> {
					$voters
						.iter()
						.position(|(x, _, _)| x == who)
						.and_then(|i| <usize as $crate::TryInto<$crate::two_phase::VoterIndex>>::try_into(i).ok())
					}
	};
}

#[macro_export]
macro_rules! target_at_fn {
	($targets:ident, $acc:ty) => {
		|who: &$acc| -> Option<$crate::two_phase::TargetIndex> {
					$targets
						.iter()
						.position(|x| x == who)
						.and_then(|i| <usize as $crate::TryInto<$crate::two_phase::TargetIndex>>::try_into(i).ok())
					}
	};
}

// TODO: these can use a cache.
// TODO: move these to test if they are not used.. They most likely will be used in offchain.
#[macro_export]
macro_rules! stake_of_fn {
	($voters:ident, $acc:ty) => {
		|who: &$acc| -> $crate::VoteWeight {
																											$voters
																												.iter()
																												.find(|(x, _, _)| x == who)
																												.map(|(_, x, _)| *x)
																												.unwrap_or_default()
																											}
	};
}

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

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
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
impl WeightInfo for () {}

pub trait Trait: frame_system::Trait {
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

	type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;

	type SignedPhase: Get<Self::BlockNumber>;
	type UnsignedPhase: Get<Self::BlockNumber>;

	type MaxSignedSubmissions: Get<u32>;

	type SignedRewardBase: Get<BalanceOf<Self>>;
	type SignedRewardFactor: Get<Perbill>;

	type SignedDepositBase: Get<BalanceOf<Self>>;
	type SignedDepositByte: Get<BalanceOf<Self>>;
	type SignedDepositWeight: Get<BalanceOf<Self>>;

	type SolutionImprovementThreshold: Get<Perbill>;

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

		/// Snapshot of all Voters. The indices if this will be used in election.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub SnapshotTargets get(fn snapshot_targets): Option<Vec<T::AccountId>>;

		/// Snapshot of all targets. The indices if this will be used in election.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub SnapshotVoters get(fn snapshot_voters): Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>>;

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
			let next_election = T::ElectionDataProvider::next_election_prediction(now);
			// TODO: document this invariant.
			let next_election = next_election.max(now);

			let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
			let unsigned_deadline = T::UnsignedPhase::get();

			let remaining = next_election - now;
			match Self::current_phase() {
				Phase::Off if remaining <= signed_deadline && remaining > unsigned_deadline => {
					// check only for the signed phase.
					CurrentPhase::put(Phase::Signed);
					Self::start_signed_phase();
				},
				Phase::Signed if remaining <= unsigned_deadline && remaining > 0.into() => {
					// check the unsigned phase.
					let found_solution = Self::finalize_signed_phase();
					CurrentPhase::put(Phase::Unsigned(!found_solution));
				},
				_ => {
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
				queue_size <= T::MaxSignedSubmissions::get(),
				PalletError::<T>::SubmissionQueuedFull,
			);

			// ensure solution claims is better.
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index = Self::insert_submission(&who, &mut signed_submissions, solution);
			ensure!(maybe_index.is_some(), PalletError::<T>::LowScoreSubmission);
			let index = maybe_index.expect("Option checked to be `Some`; qed.");

			// ensure... what else?
			// TODO

			// collect deposit. Thereafter, the function cannot fail.
			let deposit = signed_submissions[index].deposit;
			T::Currency::reserve(&who, deposit).map_err(|_| PalletError::<T>::CannotPayDeposit)?;

			// store the new signed submission.
			debug_assert_eq!(signed_submissions.len() as u32, queue_size + 1);
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

// General stuff
impl<T: Trait> Module<T> {
	fn feasibility_check(
		solution: RawSolution<T::AccountId>,
	) -> Result<ReadySolution<T::AccountId>, ()> {
		unimplemented!()
	}

	fn onchain_fallback() -> Result<FlatSupportMap<T::AccountId>, crate::Error> {
		let desired_targets = Self::desired_targets() as usize;
		let voters = Self::snapshot_voters().ok_or(crate::Error::SnapshotUnAvailable)?;
		let targets = Self::snapshot_targets().ok_or(crate::Error::SnapshotUnAvailable)?;
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
		Self::queued_solution()
			.map_or_else(
				|| Self::onchain_fallback(),
				|ReadySolution { supports, .. }| Ok(supports),
			)
			.map(|result| {
				// reset phase.
				CurrentPhase::put(Phase::Off);
				// clear snapshots.
				<SnapshotVoters<T>>::kill();
				<SnapshotTargets<T>>::kill();
				result
			})
	}

	fn ongoing() -> bool {
		matches!(Self::current_phase(), Phase::Signed | Phase::Unsigned(_))
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, *};
	use crate::ElectionProvider;
	use frame_support::traits::OnInitialize;
	use sp_npos_elections::Support;

	#[test]
	fn phase_rotation_works() {
		ExtBuilder::default().build_and_execute(|| {
			// 0 ------- 5 -------------- 15 ------- 20
			//           |                |
			//         Signed           Unsigned

			assert_eq!(System::block_number(), 0);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);

			roll_to(4);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot_voters().is_none());

			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(14);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned(true));
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(19);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned(true));
			assert!(TwoPhase::snapshot_voters().is_some());

			roll_to(20);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned(true));
			assert!(TwoPhase::snapshot_voters().is_some());

			// we close when upstream tells us to elect.
			roll_to(21);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned(true));
			assert!(TwoPhase::snapshot_voters().is_some());

			TwoPhase::elect::<sp_runtime::Perbill>(2, Default::default(), Default::default())
				.unwrap();
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			assert!(TwoPhase::snapshot_voters().is_none());
		})
	}

	#[test]
	fn onchain_backup_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			roll_to(20);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned(true));

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
	fn can_only_submit_threshold_better() {}
}
