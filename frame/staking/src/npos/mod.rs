// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! A NPoS flavoured validator selection component for the staking system.

use crate::SessionInterface;
use frame_election_provider_support::{
	data_provider, ElectionDataProvider, SortedListProvider, VoteWeight, VoterOf,
};
use frame_support::{
	dispatch::Codec,
	pallet_prelude::*,
	traits::{
		Currency, CurrencyToVote, DefensiveSaturating, EnsureOrigin, EstimateNextNewSession, Get,
		LockIdentifier, LockableCurrency, OnUnbalanced, UnixTime,
	},
	weights::Weight,
};
use frame_system::{ensure_root, ensure_signed, pallet_prelude::*};
use sp_runtime::{
	traits::{Bounded, CheckedSub, SaturatedConversion, StaticLookup, Zero},
	DispatchError, Perbill, Percent,
};
use sp_staking::{EraIndex, SessionIndex};
use sp_std::{cmp::max, prelude::*};

pub mod types;
pub use pallet::*;
pub use types::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Number of sessions per era.
		#[pallet::constant]
		type SessionsPerEra: Get<SessionIndex>;

		/// The staking balance.
		type Currency: LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;

		/// Time used for computing era duration.
		///
		/// It is guaranteed to start being called from the first `on_finalize`. Thus value at
		/// genesis is not used.
		type UnixTime: UnixTime;

		/// Convert a balance into a number used for election calculation. This must fit into a
		/// `u64` but is allowed to be sensibly lossy. The `u64` is used to communicate with the
		/// [`frame_election_provider_support`] crate which accepts u64 numbers and does operations
		/// in 128.
		/// Consequently, the backward convert is used convert the u128s from sp-elections back to a
		/// [`BalanceOf`].
		type CurrencyToVote: CurrencyToVote<BalanceOf<Self>>;

		/// Something that provides the election functionality.
		type ElectionProvider: frame_election_provider_support::ElectionProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
			// we only accept an election provider that has staking as data provider.
			DataProvider = Pallet<Self>,
		>;

		/// Something that provides the election functionality at genesis.
		type GenesisElectionProvider: frame_election_provider_support::ElectionProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
			DataProvider = Pallet<Self>,
		>;

		/// Interface for interacting with a session pallet.
		type SessionInterface: SessionInterface<Self::AccountId>;

		/// Something that can estimate the next session change, accurately or as a best effort
		/// guess.
		type NextNewSession: EstimateNextNewSession<Self::BlockNumber>;

		/// The maximum number of nominators rewarded for each validator.
		///
		/// For each validator only the `$MaxNominatorRewardedPerValidator` biggest stakers can
		/// claim their reward. This used to limit the i/o cost for the nominator payout.
		#[pallet::constant]
		type MaxNominatorRewardedPerValidator: Get<u32>;

		/// Something that provides a best-effort sorted list of voters aka electing nominators,
		/// used for NPoS election.
		///
		/// The changes to nominators are reported to this. Moreover, each validator's self-vote is
		/// also reported as one independent vote.
		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
	}

	#[pallet::type_value]
	pub(crate) fn HistoryDepthOnEmpty() -> u32 {
		84u32
	}

	/// Number of eras to keep in history.
	///
	/// Information is kept for eras in `[current_era - history_depth; current_era]`.
	///
	/// Must be more than the number of eras delayed by session otherwise. I.e. active era must
	/// always be in history. I.e. `active_era > current_era - history_depth` must be
	/// guaranteed.
	#[pallet::storage]
	#[pallet::getter(fn history_depth)]
	pub(crate) type HistoryDepth<T> = StorageValue<_, u32, ValueQuery, HistoryDepthOnEmpty>;

	/// The ideal number of staking participants.
	#[pallet::storage]
	#[pallet::getter(fn validator_count)]
	pub type ValidatorCount<T> = StorageValue<_, u32, ValueQuery>;

	/// Minimum number of staking participants before emergency conditions are imposed.
	#[pallet::storage]
	#[pallet::getter(fn minimum_validator_count)]
	pub type MinimumValidatorCount<T> = StorageValue<_, u32, ValueQuery>;

	/// Any validators that may never be slashed or forcibly kicked. It's a Vec since they're
	/// easy to initialize and the performance hit is minimal (we expect no more than four
	/// invulnerables) and restricted to testnets.
	#[pallet::storage]
	#[pallet::getter(fn invulnerables)]
	pub type Invulnerables<T: Config> = StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// The current era index.
	///
	/// This is the latest planned era, depending on how the Session pallet queues the validator
	/// set, it might be active or not.
	#[pallet::storage]
	#[pallet::getter(fn current_era)]
	pub type CurrentEra<T> = StorageValue<_, EraIndex>;

	/// The session index at which the era start for the last `HISTORY_DEPTH` eras.
	///
	/// Note: This tracks the starting session (i.e. session index when era start being active)
	/// for the eras in `[CurrentEra - HISTORY_DEPTH, CurrentEra]`.
	#[pallet::storage]
	#[pallet::getter(fn eras_start_session_index)]
	pub type ErasStartSessionIndex<T> = StorageMap<_, Twox64Concat, EraIndex, SessionIndex>;

	/// Exposure of validator at era.
	///
	/// This is keyed first by the era index to allow bulk deletion and then the stash account.
	///
	/// Is it removed after `HISTORY_DEPTH` eras.
	/// If stakers hasn't been set or has been removed then empty exposure is returned.
	#[pallet::storage]
	#[pallet::getter(fn eras_stakers)]
	pub type ErasStakers<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		EraIndex,
		Twox64Concat,
		T::AccountId,
		Exposure<T::AccountId, BalanceOf<T>>,
		ValueQuery,
	>;

	/// Clipped Exposure of validator at era.
	///
	/// This is similar to [`ErasStakers`] but number of nominators exposed is reduced to the
	/// `T::MaxNominatorRewardedPerValidator` biggest stakers.
	/// (Note: the field `total` and `own` of the exposure remains unchanged).
	/// This is used to limit the i/o cost for the nominator payout.
	///
	/// This is keyed fist by the era index to allow bulk deletion and then the stash account.
	///
	/// Is it removed after `HISTORY_DEPTH` eras.
	/// If stakers hasn't been set or has been removed then empty exposure is returned.
	#[pallet::storage]
	#[pallet::getter(fn eras_stakers_clipped)]
	pub type ErasStakersClipped<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		EraIndex,
		Twox64Concat,
		T::AccountId,
		Exposure<T::AccountId, BalanceOf<T>>,
		ValueQuery,
	>;

	/// The total amount staked for the last `HISTORY_DEPTH` eras.
	/// If total hasn't been set or has been removed then 0 stake is returned.
	#[pallet::storage]
	#[pallet::getter(fn eras_total_stake)]
	pub type ErasTotalStake<T: Config> =
		StorageMap<_, Twox64Concat, EraIndex, BalanceOf<T>, ValueQuery>;

	/// Mode of era forcing.
	#[pallet::storage]
	#[pallet::getter(fn force_era)]
	pub type ForceEra<T> = StorageValue<_, Forcing, ValueQuery>;

	/// The last planned session scheduled by the session pallet.
	///
	/// This is basically in sync with the call to [`pallet_session::SessionManager::new_session`].
	#[pallet::storage]
	#[pallet::getter(fn current_planned_session)]
	pub type CurrentPlannedSession<T> = StorageValue<_, SessionIndex, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub history_depth: u32,
		pub validator_count: u32,
		pub minimum_validator_count: u32,
		pub invulnerables: Vec<T::AccountId>,
		pub force_era: Forcing,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig {
				history_depth: 84u32,
				validator_count: Default::default(),
				minimum_validator_count: Default::default(),
				invulnerables: Default::default(),
				force_era: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			HistoryDepth::<T>::put(self.history_depth);
			ValidatorCount::<T>::put(self.validator_count);
			MinimumValidatorCount::<T>::put(self.minimum_validator_count);
			Invulnerables::<T>::put(&self.invulnerables);
			ForceEra::<T>::put(self.force_era);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		StakersElected,
		/// An account has bonded this amount. \[stash, amount\]
		///
		/// NOTE: This event is only emitted when funds are bonded via a dispatchable. Notably,
		/// it will not be emitted for staking rewards when they are added to stake.
		Bonded(T::AccountId, BalanceOf<T>),
		/// An account has unbonded this amount. \[stash, amount\]
		Unbonded(T::AccountId, BalanceOf<T>),
		/// An account has called `withdraw_unbonded` and removed unbonding chunks worth `Balance`
		/// from the unlocking queue. \[stash, amount\]
		Withdrawn(T::AccountId, BalanceOf<T>),
		/// A nominator has been kicked from a validator. \[nominator, stash\]
		Kicked(T::AccountId, T::AccountId),
		/// The election failed. No new era is planned.
		StakingElectionFailed,
		/// An account has stopped participating as either a validator or nominator.
		/// \[stash\]
		Chilled(T::AccountId),
		/// The stakers' rewards are getting paid. \[era_index, validator_stash\]
		PayoutStarted(EraIndex, T::AccountId),
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Not a controller account.
		NotController,
		/// Not a stash account.
		NotStash,
		/// Stash is already bonded.
		AlreadyBonded,
		/// Controller is already paired.
		AlreadyPaired,
		/// Targets cannot be empty.
		EmptyTargets,
		/// Duplicate index.
		DuplicateIndex,
		/// Slash record index out of bounds.
		InvalidSlashIndex,
		/// Cannot have a validator or nominator role, with value less than the minimum defined by
		/// governance (see `MinValidatorBond` and `MinNominatorBond`). If unbonding is the
		/// intention, `chill` first to remove one's role as validator/nominator.
		InsufficientBond,
		/// Can not schedule more unlock chunks.
		NoMoreChunks,
		/// Can not rebond without unlocking chunks.
		NoUnlockChunk,
		/// Attempting to target a stash that still has funds.
		FundedTarget,
		/// Invalid era to reward.
		InvalidEraToReward,
		/// Invalid number of nominations.
		InvalidNumberOfNominations,
		/// Items are not sorted and unique.
		NotSortedAndUnique,
		/// Rewards for this era have already been claimed for this validator.
		AlreadyClaimed,
		/// Incorrect previous history depth input provided.
		IncorrectHistoryDepth,
		/// Incorrect number of slashing spans provided.
		IncorrectSlashingSpans,
		/// Internal state has become somehow corrupted and the operation cannot continue.
		BadState,
		/// Too many nomination targets supplied.
		TooManyTargets,
		/// A nomination target was supplied that was blocked or otherwise not a validator.
		BadTarget,
		/// The user has enough bond and thus cannot be chilled forcefully by an external person.
		CannotChillOther,
		/// There are too many nominators in the system. Governance needs to adjust the staking
		/// settings to keep things safe for the runtime.
		TooManyNominators,
		/// There are too many validators in the system. Governance needs to adjust the staking
		/// settings to keep things safe for the runtime.
		TooManyValidators,
		/// Commission is too low. Must be at least `MinCommission`.
		CommissionTooLow,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			// TODO:LOGIC
			// ensure that we funnel the correct value to the `DataProvider::MaxVotesPerVoter`;
			// assert_eq!(
			// 	T::MaxNominations::get(),
			// 	<Self as ElectionDataProvider>::MaxVotesPerVoter::get()
			// );
			// // and that MaxNominations is always greater than 1, since we count on this.
			// assert!(!T::MaxNominations::get().is_zero());
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Sets the ideal number of validators.
		///
		/// The dispatch origin must be Root.
		#[pallet::weight(0)]
		pub fn set_validator_count(
			origin: OriginFor<T>,
			#[pallet::compact] new: u32,
		) -> DispatchResult {
			ensure_root(origin)?;
			ValidatorCount::<T>::put(new);
			Ok(())
		}

		/// Increments the ideal number of validators.
		///
		/// The dispatch origin must be Root.
		#[pallet::weight(0)]
		pub fn increase_validator_count(
			origin: OriginFor<T>,
			#[pallet::compact] additional: u32,
		) -> DispatchResult {
			ensure_root(origin)?;
			ValidatorCount::<T>::mutate(|n| *n += additional);
			Ok(())
		}

		/// Scale up the ideal number of validators by a factor.
		///
		/// The dispatch origin must be Root.
		#[pallet::weight(0)]
		pub fn scale_validator_count(origin: OriginFor<T>, factor: Percent) -> DispatchResult {
			ensure_root(origin)?;
			ValidatorCount::<T>::mutate(|n| *n += factor * *n);
			Ok(())
		}

		/// Force there to be no new eras indefinitely.
		///
		/// The dispatch origin must be Root.
		///
		/// # Warning
		///
		/// The election process starts multiple blocks before the end of the era.
		/// Thus the election process may be ongoing when this is called. In this case the
		/// election will continue until the next era is triggered.
		#[pallet::weight(0)]
		pub fn force_no_eras(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			ForceEra::<T>::put(Forcing::ForceNone);
			Ok(())
		}

		/// Force there to be a new era at the end of the next session. After this, it will be
		/// reset to normal (non-forced) behaviour.
		///
		/// The dispatch origin must be Root.
		///
		/// # Warning
		///
		/// The election process starts multiple blocks before the end of the era.
		/// If this is called just before a new era is triggered, the election process may not
		/// have enough blocks to get a result.
		///
		/// # <weight>
		/// - No arguments.
		/// - Weight: O(1)
		/// - Write ForceEra
		/// # </weight>
		#[pallet::weight(0)]
		pub fn force_new_era(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			ForceEra::<T>::put(Forcing::ForceNew);
			Ok(())
		}

		/// Force there to be a new era at the end of sessions indefinitely.
		///
		/// The dispatch origin must be Root.
		///
		/// # Warning
		///
		/// The election process starts multiple blocks before the end of the era.
		/// If this is called just before a new era is triggered, the election process may not
		/// have enough blocks to get a result.
		#[pallet::weight(0)]
		pub fn force_new_era_always(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			ForceEra::<T>::put(Forcing::ForceAlways);
			Ok(())
		}

		/// Set the validators who cannot be slashed (if any).
		///
		/// The dispatch origin must be Root.
		#[pallet::weight(0)]
		pub fn set_invulnerables(
			origin: OriginFor<T>,
			invulnerables: Vec<T::AccountId>,
		) -> DispatchResult {
			ensure_root(origin)?;
			<Invulnerables<T>>::put(invulnerables);
			Ok(())
		}

		/// Set `HistoryDepth` value. This function will delete any history information
		/// when `HistoryDepth` is reduced.
		///
		/// Parameters:
		/// - `new_history_depth`: The new history depth you would like to set.
		/// - `era_items_deleted`: The number of items that will be deleted by this dispatch. This
		///   should report all the storage items that will be deleted by clearing old era history.
		///   Needed to report an accurate weight for the dispatch. Trusted by `Root` to report an
		///   accurate number.
		///
		/// Origin must be root.
		///
		/// # <weight>
		/// - E: Number of history depths removed, i.e. 10 -> 7 = 3
		/// - Weight: O(E)
		/// - DB Weight:
		///     - Reads: Current Era, History Depth
		///     - Writes: History Depth
		///     - Clear Prefix Each: Era Stakers, EraStakersClipped, ErasValidatorPrefs
		///     - Writes Each: ErasValidatorReward, ErasRewardPoints, ErasTotalStake,
		///       ErasStartSessionIndex
		/// # </weight>
		#[pallet::weight(0)]
		pub fn set_history_depth(
			origin: OriginFor<T>,
			#[pallet::compact] new_history_depth: EraIndex,
			#[pallet::compact] _era_items_deleted: u32,
		) -> DispatchResult {
			ensure_root(origin)?;
			if let Some(current_era) = Self::current_era() {
				HistoryDepth::<T>::mutate(|history_depth| {
					let last_kept = current_era.checked_sub(*history_depth).unwrap_or(0);
					let new_last_kept = current_era.checked_sub(new_history_depth).unwrap_or(0);
					for era_index in last_kept..new_last_kept {
						Self::clear_era_information(era_index);
					}
					*history_depth = new_history_depth
				})
			}
			Ok(())
		}
	}
}

/// The maximum number of iterations that we do whilst iterating over `T::VoterList` in
/// `get_npos_voters`.
///
/// In most cases, if we want n items, we iterate exactly n times. In rare cases, if a voter is
/// invalid (for any reason) the iteration continues. With this constant, we iterate at most 2 * n
/// times and then give up.
const NPOS_MAX_ITERATIONS_COEFFICIENT: u32 = 2;

impl<T: Config> Pallet<T> {
	/// Clear all era information for given era.
	pub(crate) fn clear_era_information(era_index: EraIndex) {
		<ErasStakers<T>>::remove_prefix(era_index, None);
		<ErasStakersClipped<T>>::remove_prefix(era_index, None);
		// TODO:LOGIC
		// <ErasValidatorPrefs<T>>::remove_prefix(era_index, None);
		// <ErasValidatorReward<T>>::remove(era_index);
		// <ErasRewardPoints<T>>::remove(era_index);
		<ErasTotalStake<T>>::remove(era_index);
		ErasStartSessionIndex::<T>::remove(era_index);
	}

	/// Get all of the voters that are eligible for the npos election.
	///
	/// `maybe_max_len` can imposes a cap on the number of voters returned;
	///
	/// This function is self-weighing as [`DispatchClass::Mandatory`].
	///
	/// ### Slashing
	///
	/// All votes that have been submitted before the last non-zero slash of the corresponding
	/// target are *auto-chilled*, but still count towards the limit imposed by `maybe_max_len`.
	pub fn get_npos_voters(maybe_max_len: Option<usize>) -> Vec<VoterOf<Self>> {
		let max_allowed_len = {
			let all_voter_count = T::VoterList::count() as usize;
			maybe_max_len.unwrap_or(all_voter_count).min(all_voter_count)
		};

		let mut all_voters = Vec::<_>::with_capacity(max_allowed_len);

		// cache a few things.
		let weight_of = Self::weight_of_fn();
		let slashing_spans = <SlashingSpans<T>>::iter().collect::<BTreeMap<_, _>>();

		let mut voters_seen = 0u32;
		let mut validators_taken = 0u32;
		let mut nominators_taken = 0u32;

		let mut sorted_voters = T::VoterList::iter();
		while all_voters.len() < max_allowed_len &&
			voters_seen < (NPOS_MAX_ITERATIONS_COEFFICIENT * max_allowed_len as u32)
		{
			let voter = match sorted_voters.next() {
				Some(voter) => {
					voters_seen.saturating_inc();
					voter
				},
				None => break,
			};

			if let Some(Nominations { submitted_in, mut targets, suppressed: _ }) =
				<Nominators<T>>::get(&voter)
			{
				// if this voter is a nominator:
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});
				if !targets.len().is_zero() {
					all_voters.push((voter.clone(), weight_of(&voter), targets));
					nominators_taken.saturating_inc();
				}
			} else if Validators::<T>::contains_key(&voter) {
				// if this voter is a validator:
				let self_vote = (
					voter.clone(),
					weight_of(&voter),
					vec![voter.clone()]
						.try_into()
						.expect("`MaxVotesPerVoter` must be greater than or equal to 1"),
				);
				all_voters.push(self_vote);
				validators_taken.saturating_inc();
			} else {
				// this can only happen if: 1. there a bug in the bags-list (or whatever is the
				// sorted list) logic and the state of the two pallets is no longer compatible, or
				// because the nominators is not decodable since they have more nomination than
				// `T::MaxNominations`. The latter can rarely happen, and is not really an emergency
				// or bug if it does.
				log!(
					warn,
					"DEFENSIVE: invalid item in `VoterList`: {:?}, this nominator probably has too many nominations now",
					voter
				)
			}
		}

		// all_voters should have not re-allocated.
		debug_assert!(all_voters.capacity() == max_allowed_len);

		Self::register_weight(T::WeightInfo::get_npos_voters(
			validators_taken,
			nominators_taken,
			slashing_spans.len() as u32,
		));

		log!(
			info,
			"generated {} npos voters, {} from validators and {} nominators",
			all_voters.len(),
			validators_taken,
			nominators_taken
		);

		all_voters
	}

	/// Get the targets for an upcoming npos election.
	///
	/// This function is self-weighing as [`DispatchClass::Mandatory`].
	pub fn get_npos_targets() -> Vec<T::AccountId> {
		let mut validator_count = 0u32;
		let targets = Validators::<T>::iter()
			.map(|(v, _)| {
				validator_count.saturating_inc();
				v
			})
			.collect::<Vec<_>>();

		Self::register_weight(T::WeightInfo::get_npos_targets(validator_count));

		targets
	}
}

impl<T: Config> ElectionDataProvider for Pallet<T> {
	type AccountId = T::AccountId;
	type BlockNumber = BlockNumberFor<T>;
	type MaxVotesPerVoter = T::MaxNominations;

	fn desired_targets() -> data_provider::Result<u32> {
		Self::register_weight(T::DbWeight::get().reads(1));
		Ok(Self::validator_count())
	}

	fn electing_voters(maybe_max_len: Option<usize>) -> data_provider::Result<Vec<VoterOf<Self>>> {
		// This can never fail -- if `maybe_max_len` is `Some(_)` we handle it.
		let voters = Self::get_npos_voters(maybe_max_len);
		debug_assert!(maybe_max_len.map_or(true, |max| voters.len() <= max));

		Ok(voters)
	}

	fn electable_targets(maybe_max_len: Option<usize>) -> data_provider::Result<Vec<T::AccountId>> {
		let target_count = T::VoterList::count();

		// We can't handle this case yet -- return an error.
		if maybe_max_len.map_or(false, |max_len| target_count > max_len as u32) {
			return Err("Target snapshot too big")
		}

		Ok(Self::get_npos_targets())
	}

	fn next_election_prediction(now: T::BlockNumber) -> T::BlockNumber {
		let current_era = Self::current_era().unwrap_or(0);
		let current_session = Self::current_planned_session();
		let current_era_start_session_index =
			Self::eras_start_session_index(current_era).unwrap_or(0);
		// Number of session in the current era or the maximum session per era if reached.
		let era_progress = current_session
			.saturating_sub(current_era_start_session_index)
			.min(T::SessionsPerEra::get());

		let until_this_session_end = T::NextNewSession::estimate_next_new_session(now)
			.0
			.unwrap_or_default()
			.saturating_sub(now);

		let session_length = T::NextNewSession::average_session_length();

		let sessions_left: T::BlockNumber = match ForceEra::<T>::get() {
			Forcing::ForceNone => Bounded::max_value(),
			Forcing::ForceNew | Forcing::ForceAlways => Zero::zero(),
			Forcing::NotForcing if era_progress >= T::SessionsPerEra::get() => Zero::zero(),
			Forcing::NotForcing => T::SessionsPerEra::get()
				.saturating_sub(era_progress)
				// One session is computed in this_session_end.
				.saturating_sub(1)
				.into(),
		};

		now.saturating_add(
			until_this_session_end.saturating_add(sessions_left.saturating_mul(session_length)),
		)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_voter(
		voter: T::AccountId,
		weight: VoteWeight,
		targets: BoundedVec<T::AccountId, Self::MaxVotesPerVoter>,
	) {
		todo!();
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_target(target: T::AccountId) {
		todo!()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn clear() {
		todo!()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn put_snapshot(
		voters: Vec<VoterOf<Self>>,
		targets: Vec<T::AccountId>,
		target_stake: Option<VoteWeight>,
	) {
		todo!()
	}
}
