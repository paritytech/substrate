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

//! Staking FRAME Pallet.

use frame_election_provider_support::{
	ElectionProvider, ElectionProviderBase, SortedListProvider, VoteWeight,
};
use frame_support::{
	dispatch::Codec,
	pallet_prelude::*,
	traits::{
		Currency, CurrencyToVote, Defensive, DefensiveResult, DefensiveSaturating, EnsureOrigin,
		EstimateNextNewSession, Get, LockIdentifier, LockableCurrency, OnUnbalanced, TryCollect,
		UnixTime,
	},
	weights::Weight,
	BoundedVec,
};
use frame_system::{ensure_root, ensure_signed, pallet_prelude::*};
use sp_runtime::{
	traits::{CheckedSub, SaturatedConversion, StaticLookup, Zero},
	ArithmeticError, Perbill, Percent,
};
use sp_staking::{EraIndex, SessionIndex};
use sp_std::prelude::*;

mod impls;

pub use impls::*;

use crate::{
	slashing, weights::WeightInfo, AccountIdLookupOf, ActiveEraInfo, BalanceOf, EraPayout,
	EraRewardPoints, Exposure, Forcing, NegativeImbalanceOf, Nominations, PositiveImbalanceOf,
	RewardDestination, SessionInterface, StakingLedger, UnappliedSlash, UnlockChunk,
	ValidatorPrefs,
};

const STAKING_ID: LockIdentifier = *b"staking ";
// The speculative number of spans are used as an input of the weight annotation of
// [`Call::unbond`], as the post dipatch weight may depend on the number of slashing span on the
// account which is not provided as an input. The value set should be conservative but sensible.
pub(crate) const SPECULATIVE_NUM_SPANS: u32 = 32;

#[frame_support::pallet]
pub mod pallet {
	use frame_election_provider_support::ElectionDataProvider;

	use crate::BenchmarkingConfig;

	use super::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(13);

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	/// Possible operations on the configuration values of this pallet.
	#[derive(TypeInfo, Debug, Clone, Encode, Decode, PartialEq)]
	pub enum ConfigOp<T: Default + Codec> {
		/// Don't change.
		Noop,
		/// Set the given value.
		Set(T),
		/// Remove from storage.
		Remove,
	}

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The staking balance.
		type Currency: LockableCurrency<
			Self::AccountId,
			Moment = Self::BlockNumber,
			Balance = Self::CurrencyBalance,
		>;
		/// Just the `Currency::Balance` type; we have this item to allow us to constrain it to
		/// `From<u64>`.
		type CurrencyBalance: sp_runtime::traits::AtLeast32BitUnsigned
			+ codec::FullCodec
			+ Copy
			+ MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ Default
			+ From<u64>
			+ TypeInfo
			+ MaxEncodedLen;
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
		type ElectionProvider: ElectionProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
			// we only accept an election provider that has staking as data provider.
			DataProvider = Pallet<Self>,
		>;
		/// Something that provides the election functionality at genesis.
		type GenesisElectionProvider: ElectionProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
			DataProvider = Pallet<Self>,
		>;

		/// Maximum number of nominations per nominator.
		#[pallet::constant]
		type MaxNominations: Get<u32>;

		/// Number of eras to keep in history.
		///
		/// Following information is kept for eras in `[current_era -
		/// HistoryDepth, current_era]`: `ErasStakers`, `ErasStakersClipped`,
		/// `ErasValidatorPrefs`, `ErasValidatorReward`, `ErasRewardPoints`,
		/// `ErasTotalStake`, `ErasStartSessionIndex`,
		/// `StakingLedger.claimed_rewards`.
		///
		/// Must be more than the number of eras delayed by session.
		/// I.e. active era must always be in history. I.e. `active_era >
		/// current_era - history_depth` must be guaranteed.
		///
		/// If migrating an existing pallet from storage value to config value,
		/// this should be set to same value or greater as in storage.
		///
		/// Note: `HistoryDepth` is used as the upper bound for the `BoundedVec`
		/// item `StakingLedger.claimed_rewards`. Setting this value lower than
		/// the existing value can lead to inconsistencies in the
		/// `StakingLedger` and will need to be handled properly in a migration.
		/// The test `reducing_history_depth_abrupt` shows this effect.
		#[pallet::constant]
		type HistoryDepth: Get<u32>;

		/// Tokens have been minted and are unused for validator-reward.
		/// See [Era payout](./index.html#era-payout).
		type RewardRemainder: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Handler for the unbalanced reduction when slashing a staker.
		type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// Handler for the unbalanced increment when rewarding a staker.
		/// NOTE: in most cases, the implementation of `OnUnbalanced` should modify the total
		/// issuance.
		type Reward: OnUnbalanced<PositiveImbalanceOf<Self>>;

		/// Number of sessions per era.
		#[pallet::constant]
		type SessionsPerEra: Get<SessionIndex>;

		/// Number of eras that staked funds must remain bonded for.
		#[pallet::constant]
		type BondingDuration: Get<EraIndex>;

		/// Number of eras that slashes are deferred by, after computation.
		///
		/// This should be less than the bonding duration. Set to 0 if slashes
		/// should be applied immediately, without opportunity for intervention.
		#[pallet::constant]
		type SlashDeferDuration: Get<EraIndex>;

		/// The origin which can manage less critical staking parameters that does not require root.
		///
		/// Supported actions: (1) cancel deferred slash, (2) set minimum commission.
		type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Interface for interacting with a session pallet.
		type SessionInterface: SessionInterface<Self::AccountId>;

		/// The payout for validators and the system for the current era.
		/// See [Era payout](./index.html#era-payout).
		type EraPayout: EraPayout<BalanceOf<Self>>;

		/// Something that can estimate the next session change, accurately or as a best effort
		/// guess.
		type NextNewSession: EstimateNextNewSession<Self::BlockNumber>;

		/// The maximum number of nominators rewarded for each validator.
		///
		/// For each validator only the `$MaxNominatorRewardedPerValidator` biggest stakers can
		/// claim their reward. This used to limit the i/o cost for the nominator payout.
		#[pallet::constant]
		type MaxNominatorRewardedPerValidator: Get<u32>;

		/// The fraction of the validator set that is safe to be offending.
		/// After the threshold is reached a new era will be forced.
		type OffendingValidatorsThreshold: Get<Perbill>;

		/// Something that provides a best-effort sorted list of voters aka electing nominators,
		/// used for NPoS election.
		///
		/// The changes to nominators are reported to this. Moreover, each validator's self-vote is
		/// also reported as one independent vote.
		///
		/// To keep the load off the chain as much as possible, changes made to the staked amount
		/// via rewards and slashes are not reported and thus need to be manually fixed by the
		/// staker. In case of `bags-list`, this always means using `rebag` and `putInFrontOf`.
		///
		/// Invariant: what comes out of this list will always be a nominator.
		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;

		/// WIP: This is a noop as of now, the actual business logic that's described below is going
		/// to be introduced in a follow-up PR.
		///
		/// Something that provides a best-effort sorted list of targets aka electable validators,
		/// used for NPoS election.
		///
		/// The changes to the approval stake of each validator are reported to this. This means any
		/// change to:
		/// 1. The stake of any validator or nominator.
		/// 2. The targets of any nominator
		/// 3. The role of any staker (e.g. validator -> chilled, nominator -> validator, etc)
		///
		/// Unlike `VoterList`, the values in this list are always kept up to date with reward and
		/// slash as well, and thus represent the accurate approval stake of all account being
		/// nominated by nominators.
		///
		/// Note that while at the time of nomination, all targets are checked to be real
		/// validators, they can chill at any point, and their approval stakes will still be
		/// recorded. This implies that what comes out of iterating this list MIGHT NOT BE AN ACTIVE
		/// VALIDATOR.
		type TargetList: SortedListProvider<Self::AccountId, Score = BalanceOf<Self>>;

		/// The maximum number of `unlocking` chunks a [`StakingLedger`] can
		/// have. Effectively determines how many unique eras a staker may be
		/// unbonding in.
		///
		/// Note: `MaxUnlockingChunks` is used as the upper bound for the
		/// `BoundedVec` item `StakingLedger.unlocking`. Setting this value
		/// lower than the existing value can lead to inconsistencies in the
		/// `StakingLedger` and will need to be handled properly in a runtime
		/// migration. The test `reducing_max_unlocking_chunks_abrupt` shows
		/// this effect.
		#[pallet::constant]
		type MaxUnlockingChunks: Get<u32>;

		/// A hook called when any staker is slashed. Mostly likely this can be a no-op unless
		/// other pallets exist that are affected by slashing per-staker.
		type OnStakerSlash: sp_staking::OnStakerSlash<Self::AccountId, BalanceOf<Self>>;

		/// Some parameters of the benchmarking.
		type BenchmarkingConfig: BenchmarkingConfig;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// The ideal number of active validators.
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
	#[pallet::unbounded]
	pub type Invulnerables<T: Config> = StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// Map from all locked "stash" accounts to the controller account.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn bonded)]
	pub type Bonded<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, T::AccountId>;

	/// The minimum active bond to become and maintain the role of a nominator.
	#[pallet::storage]
	pub type MinNominatorBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The minimum active bond to become and maintain the role of a validator.
	#[pallet::storage]
	pub type MinValidatorBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The minimum active nominator stake of the last successful election.
	#[pallet::storage]
	pub type MinimumActiveStake<T> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The minimum amount of commission that validators can set.
	///
	/// If set to `0`, no limit exists.
	#[pallet::storage]
	pub type MinCommission<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
	#[pallet::storage]
	#[pallet::getter(fn ledger)]
	pub type Ledger<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, StakingLedger<T>>;

	/// Where the reward payment should be made. Keyed by stash.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn payee)]
	pub type Payee<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, RewardDestination<T::AccountId>, ValueQuery>;

	/// The map from (wannabe) validator stash key to the preferences of that validator.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn validators)]
	pub type Validators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, ValidatorPrefs, ValueQuery>;

	/// The maximum validator count before we stop allowing new validators to join.
	///
	/// When this value is not set, no limits are enforced.
	#[pallet::storage]
	pub type MaxValidatorsCount<T> = StorageValue<_, u32, OptionQuery>;

	/// The map from nominator stash key to their nomination preferences, namely the validators that
	/// they wish to support.
	///
	/// Note that the keys of this storage map might become non-decodable in case the
	/// [`Config::MaxNominations`] configuration is decreased. In this rare case, these nominators
	/// are still existent in storage, their key is correct and retrievable (i.e. `contains_key`
	/// indicates that they exist), but their value cannot be decoded. Therefore, the non-decodable
	/// nominators will effectively not-exist, until they re-submit their preferences such that it
	/// is within the bounds of the newly set `Config::MaxNominations`.
	///
	/// This implies that `::iter_keys().count()` and `::iter().count()` might return different
	/// values for this map. Moreover, the main `::count()` is aligned with the former, namely the
	/// number of keys that exist.
	///
	/// Lastly, if any of the nominators become non-decodable, they can be chilled immediately via
	/// [`Call::chill_other`] dispatchable by anyone.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn nominators)]
	pub type Nominators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Nominations<T>>;

	/// The maximum nominator count before we stop allowing new validators to join.
	///
	/// When this value is not set, no limits are enforced.
	#[pallet::storage]
	pub type MaxNominatorsCount<T> = StorageValue<_, u32, OptionQuery>;

	/// The current era index.
	///
	/// This is the latest planned era, depending on how the Session pallet queues the validator
	/// set, it might be active or not.
	#[pallet::storage]
	#[pallet::getter(fn current_era)]
	pub type CurrentEra<T> = StorageValue<_, EraIndex>;

	/// The active era information, it holds index and start.
	///
	/// The active era is the era being currently rewarded. Validator set of this era must be
	/// equal to [`SessionInterface::validators`].
	#[pallet::storage]
	#[pallet::getter(fn active_era)]
	pub type ActiveEra<T> = StorageValue<_, ActiveEraInfo>;

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
	#[pallet::unbounded]
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
	#[pallet::unbounded]
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

	/// Similar to `ErasStakers`, this holds the preferences of validators.
	///
	/// This is keyed first by the era index to allow bulk deletion and then the stash account.
	///
	/// Is it removed after `HISTORY_DEPTH` eras.
	// If prefs hasn't been set or has been removed then 0 commission is returned.
	#[pallet::storage]
	#[pallet::getter(fn eras_validator_prefs)]
	pub type ErasValidatorPrefs<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		EraIndex,
		Twox64Concat,
		T::AccountId,
		ValidatorPrefs,
		ValueQuery,
	>;

	/// The total validator era payout for the last `HISTORY_DEPTH` eras.
	///
	/// Eras that haven't finished yet or has been removed doesn't have reward.
	#[pallet::storage]
	#[pallet::getter(fn eras_validator_reward)]
	pub type ErasValidatorReward<T: Config> = StorageMap<_, Twox64Concat, EraIndex, BalanceOf<T>>;

	/// Rewards for the last `HISTORY_DEPTH` eras.
	/// If reward hasn't been set or has been removed then 0 reward is returned.
	#[pallet::storage]
	#[pallet::unbounded]
	#[pallet::getter(fn eras_reward_points)]
	pub type ErasRewardPoints<T: Config> =
		StorageMap<_, Twox64Concat, EraIndex, EraRewardPoints<T::AccountId>, ValueQuery>;

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

	/// The percentage of the slash that is distributed to reporters.
	///
	/// The rest of the slashed value is handled by the `Slash`.
	#[pallet::storage]
	#[pallet::getter(fn slash_reward_fraction)]
	pub type SlashRewardFraction<T> = StorageValue<_, Perbill, ValueQuery>;

	/// The amount of currency given to reporters of a slash event which was
	/// canceled by extraordinary circumstances (e.g. governance).
	#[pallet::storage]
	#[pallet::getter(fn canceled_payout)]
	pub type CanceledSlashPayout<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// All unapplied slashes that are queued for later.
	#[pallet::storage]
	#[pallet::unbounded]
	pub type UnappliedSlashes<T: Config> = StorageMap<
		_,
		Twox64Concat,
		EraIndex,
		Vec<UnappliedSlash<T::AccountId, BalanceOf<T>>>,
		ValueQuery,
	>;

	/// A mapping from still-bonded eras to the first session index of that era.
	///
	/// Must contains information for eras for the range:
	/// `[active_era - bounding_duration; active_era]`
	#[pallet::storage]
	#[pallet::unbounded]
	pub(crate) type BondedEras<T: Config> =
		StorageValue<_, Vec<(EraIndex, SessionIndex)>, ValueQuery>;

	/// All slashing events on validators, mapped by era to the highest slash proportion
	/// and slash value of the era.
	#[pallet::storage]
	pub(crate) type ValidatorSlashInEra<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		EraIndex,
		Twox64Concat,
		T::AccountId,
		(Perbill, BalanceOf<T>),
	>;

	/// All slashing events on nominators, mapped by era to the highest slash value of the era.
	#[pallet::storage]
	pub(crate) type NominatorSlashInEra<T: Config> =
		StorageDoubleMap<_, Twox64Concat, EraIndex, Twox64Concat, T::AccountId, BalanceOf<T>>;

	/// Slashing spans for stash accounts.
	#[pallet::storage]
	#[pallet::getter(fn slashing_spans)]
	#[pallet::unbounded]
	pub type SlashingSpans<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, slashing::SlashingSpans>;

	/// Records information about the maximum slash of a stash within a slashing span,
	/// as well as how much reward has been paid out.
	#[pallet::storage]
	pub(crate) type SpanSlash<T: Config> = StorageMap<
		_,
		Twox64Concat,
		(T::AccountId, slashing::SpanIndex),
		slashing::SpanRecord<BalanceOf<T>>,
		ValueQuery,
	>;

	/// The last planned session scheduled by the session pallet.
	///
	/// This is basically in sync with the call to [`pallet_session::SessionManager::new_session`].
	#[pallet::storage]
	#[pallet::getter(fn current_planned_session)]
	pub type CurrentPlannedSession<T> = StorageValue<_, SessionIndex, ValueQuery>;

	/// Indices of validators that have offended in the active era and whether they are currently
	/// disabled.
	///
	/// This value should be a superset of disabled validators since not all offences lead to the
	/// validator being disabled (if there was no slash). This is needed to track the percentage of
	/// validators that have offended in the current era, ensuring a new era is forced if
	/// `OffendingValidatorsThreshold` is reached. The vec is always kept sorted so that we can find
	/// whether a given validator has previously offended using binary search. It gets cleared when
	/// the era ends.
	#[pallet::storage]
	#[pallet::unbounded]
	#[pallet::getter(fn offending_validators)]
	pub type OffendingValidators<T: Config> = StorageValue<_, Vec<(u32, bool)>, ValueQuery>;

	/// The threshold for when users can start calling `chill_other` for other validators /
	/// nominators. The threshold is compared to the actual number of validators / nominators
	/// (`CountFor*`) in the system compared to the configured max (`Max*Count`).
	#[pallet::storage]
	pub(crate) type ChillThreshold<T: Config> = StorageValue<_, Percent, OptionQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub validator_count: u32,
		pub minimum_validator_count: u32,
		pub invulnerables: Vec<T::AccountId>,
		pub force_era: Forcing,
		pub slash_reward_fraction: Perbill,
		pub canceled_payout: BalanceOf<T>,
		pub stakers:
			Vec<(T::AccountId, T::AccountId, BalanceOf<T>, crate::StakerStatus<T::AccountId>)>,
		pub min_nominator_bond: BalanceOf<T>,
		pub min_validator_bond: BalanceOf<T>,
		pub max_validator_count: Option<u32>,
		pub max_nominator_count: Option<u32>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig {
				validator_count: Default::default(),
				minimum_validator_count: Default::default(),
				invulnerables: Default::default(),
				force_era: Default::default(),
				slash_reward_fraction: Default::default(),
				canceled_payout: Default::default(),
				stakers: Default::default(),
				min_nominator_bond: Default::default(),
				min_validator_bond: Default::default(),
				max_validator_count: None,
				max_nominator_count: None,
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			ValidatorCount::<T>::put(self.validator_count);
			MinimumValidatorCount::<T>::put(self.minimum_validator_count);
			Invulnerables::<T>::put(&self.invulnerables);
			ForceEra::<T>::put(self.force_era);
			CanceledSlashPayout::<T>::put(self.canceled_payout);
			SlashRewardFraction::<T>::put(self.slash_reward_fraction);
			MinNominatorBond::<T>::put(self.min_nominator_bond);
			MinValidatorBond::<T>::put(self.min_validator_bond);
			if let Some(x) = self.max_validator_count {
				MaxValidatorsCount::<T>::put(x);
			}
			if let Some(x) = self.max_nominator_count {
				MaxNominatorsCount::<T>::put(x);
			}

			for &(ref stash, ref controller, balance, ref status) in &self.stakers {
				crate::log!(
					trace,
					"inserting genesis staker: {:?} => {:?} => {:?}",
					stash,
					balance,
					status
				);
				assert!(
					T::Currency::free_balance(stash) >= balance,
					"Stash does not have enough balance to bond."
				);
				frame_support::assert_ok!(<Pallet<T>>::bond(
					T::RuntimeOrigin::from(Some(stash.clone()).into()),
					T::Lookup::unlookup(controller.clone()),
					balance,
					RewardDestination::Staked,
				));
				frame_support::assert_ok!(match status {
					crate::StakerStatus::Validator => <Pallet<T>>::validate(
						T::RuntimeOrigin::from(Some(controller.clone()).into()),
						Default::default(),
					),
					crate::StakerStatus::Nominator(votes) => <Pallet<T>>::nominate(
						T::RuntimeOrigin::from(Some(controller.clone()).into()),
						votes.iter().map(|l| T::Lookup::unlookup(l.clone())).collect(),
					),
					_ => Ok(()),
				});
				assert!(
					ValidatorCount::<T>::get() <=
						<T::ElectionProvider as ElectionProviderBase>::MaxWinners::get()
				);
			}

			// all voters are reported to the `VoterList`.
			assert_eq!(
				T::VoterList::count(),
				Nominators::<T>::count() + Validators::<T>::count(),
				"not all genesis stakers were inserted into sorted list provider, something is wrong."
			);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The era payout has been set; the first balance is the validator-payout; the second is
		/// the remainder from the maximum amount of reward.
		EraPaid { era_index: EraIndex, validator_payout: BalanceOf<T>, remainder: BalanceOf<T> },
		/// The nominator has been rewarded by this amount.
		Rewarded { stash: T::AccountId, amount: BalanceOf<T> },
		/// A staker (validator or nominator) has been slashed by the given amount.
		Slashed { staker: T::AccountId, amount: BalanceOf<T> },
		/// A slash for the given validator, for the given percentage of their stake, at the given
		/// era as been reported.
		SlashReported { validator: T::AccountId, fraction: Perbill, slash_era: EraIndex },
		/// An old slashing report from a prior era was discarded because it could
		/// not be processed.
		OldSlashingReportDiscarded { session_index: SessionIndex },
		/// A new set of stakers was elected.
		StakersElected,
		/// An account has bonded this amount. \[stash, amount\]
		///
		/// NOTE: This event is only emitted when funds are bonded via a dispatchable. Notably,
		/// it will not be emitted for staking rewards when they are added to stake.
		Bonded { stash: T::AccountId, amount: BalanceOf<T> },
		/// An account has unbonded this amount.
		Unbonded { stash: T::AccountId, amount: BalanceOf<T> },
		/// An account has called `withdraw_unbonded` and removed unbonding chunks worth `Balance`
		/// from the unlocking queue.
		Withdrawn { stash: T::AccountId, amount: BalanceOf<T> },
		/// A nominator has been kicked from a validator.
		Kicked { nominator: T::AccountId, stash: T::AccountId },
		/// The election failed. No new era is planned.
		StakingElectionFailed,
		/// An account has stopped participating as either a validator or nominator.
		Chilled { stash: T::AccountId },
		/// The stakers' rewards are getting paid.
		PayoutStarted { era_index: EraIndex, validator_stash: T::AccountId },
		/// A validator has set their preferences.
		ValidatorPrefsSet { stash: T::AccountId, prefs: ValidatorPrefs },
		/// A new force era mode was set.
		ForceEra { mode: Forcing },
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
		/// There are too many validator candidates in the system. Governance needs to adjust the
		/// staking settings to keep things safe for the runtime.
		TooManyValidators,
		/// Commission is too low. Must be at least `MinCommission`.
		CommissionTooLow,
		/// Some bound is not met.
		BoundNotMet,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_now: BlockNumberFor<T>) -> Weight {
			// just return the weight of the on_finalize.
			T::DbWeight::get().reads(1)
		}

		fn on_finalize(_n: BlockNumberFor<T>) {
			// Set the start of the first era.
			if let Some(mut active_era) = Self::active_era() {
				if active_era.start.is_none() {
					let now_as_millis_u64 = T::UnixTime::now().as_millis().saturated_into::<u64>();
					active_era.start = Some(now_as_millis_u64);
					// This write only ever happens once, we don't include it in the weight in
					// general
					ActiveEra::<T>::put(active_era);
				}
			}
			// `on_finalize` weight is tracked in `on_initialize`
		}

		fn integrity_test() {
			// ensure that we funnel the correct value to the `DataProvider::MaxVotesPerVoter`;
			assert_eq!(
				T::MaxNominations::get(),
				<Self as ElectionDataProvider>::MaxVotesPerVoter::get()
			);
			// and that MaxNominations is always greater than 1, since we count on this.
			assert!(!T::MaxNominations::get().is_zero());

			// ensure election results are always bounded with the same value
			assert!(
				<T::ElectionProvider as ElectionProviderBase>::MaxWinners::get() ==
					<T::GenesisElectionProvider as ElectionProviderBase>::MaxWinners::get()
			);

			sp_std::if_std! {
				sp_io::TestExternalities::new_empty().execute_with(||
					assert!(
						T::SlashDeferDuration::get() < T::BondingDuration::get() || T::BondingDuration::get() == 0,
						"As per documentation, slash defer duration ({}) should be less than bonding duration ({}).",
						T::SlashDeferDuration::get(),
						T::BondingDuration::get(),
					)
				);
			}
		}

		#[cfg(feature = "try-runtime")]
		fn try_state(n: BlockNumberFor<T>) -> Result<(), &'static str> {
			Self::do_try_state(n)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will
		/// be the account that controls it.
		///
		/// `value` must be more than the `minimum_balance` specified by `T::Currency`.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash account.
		///
		/// Emits `Bonded`.
		/// # <weight>
		/// - Independent of the arguments. Moderate complexity.
		/// - O(1).
		/// - Three extra DB entries.
		///
		/// NOTE: Two of the storage writes (`Self::bonded`, `Self::payee`) are _never_ cleaned
		/// unless the `origin` falls below _existential deposit_ and gets removed as dust.
		/// ------------------
		/// # </weight>
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::bond())]
		pub fn bond(
			origin: OriginFor<T>,
			controller: AccountIdLookupOf<T>,
			#[pallet::compact] value: BalanceOf<T>,
			payee: RewardDestination<T::AccountId>,
		) -> DispatchResult {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::contains_key(&stash) {
				return Err(Error::<T>::AlreadyBonded.into())
			}

			let controller = T::Lookup::lookup(controller)?;

			if <Ledger<T>>::contains_key(&controller) {
				return Err(Error::<T>::AlreadyPaired.into())
			}

			// Reject a bond which is considered to be _dust_.
			if value < T::Currency::minimum_balance() {
				return Err(Error::<T>::InsufficientBond.into())
			}

			frame_system::Pallet::<T>::inc_consumers(&stash).map_err(|_| Error::<T>::BadState)?;

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate and remove once you unbond __everything__.
			<Bonded<T>>::insert(&stash, &controller);
			<Payee<T>>::insert(&stash, payee);

			let current_era = CurrentEra::<T>::get().unwrap_or(0);
			let history_depth = T::HistoryDepth::get();
			let last_reward_era = current_era.saturating_sub(history_depth);

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);
			Self::deposit_event(Event::<T>::Bonded { stash: stash.clone(), amount: value });
			let item = StakingLedger {
				stash,
				total: value,
				active: value,
				unlocking: Default::default(),
				claimed_rewards: (last_reward_era..current_era)
					.try_collect()
					// Since last_reward_era is calculated as `current_era -
					// HistoryDepth`, following bound is always expected to be
					// satisfied.
					.defensive_map_err(|_| Error::<T>::BoundNotMet)?,
			};
			Self::update_ledger(&controller, &item);
			Ok(())
		}

		/// Add some extra amount that have appeared in the stash `free_balance` into the balance up
		/// for staking.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash, not the controller.
		///
		/// Use this if there are additional funds in your stash account that you wish to bond.
		/// Unlike [`bond`](Self::bond) or [`unbond`](Self::unbond) this function does not impose
		/// any limitation on the amount that can be added.
		///
		/// Emits `Bonded`.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - O(1).
		/// # </weight>
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::bond_extra())]
		pub fn bond_extra(
			origin: OriginFor<T>,
			#[pallet::compact] max_additional: BalanceOf<T>,
		) -> DispatchResult {
			let stash = ensure_signed(origin)?;

			let controller = Self::bonded(&stash).ok_or(Error::<T>::NotStash)?;
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;

			let stash_balance = T::Currency::free_balance(&stash);
			if let Some(extra) = stash_balance.checked_sub(&ledger.total) {
				let extra = extra.min(max_additional);
				ledger.total += extra;
				ledger.active += extra;
				// Last check: the new active amount of ledger must be more than ED.
				ensure!(
					ledger.active >= T::Currency::minimum_balance(),
					Error::<T>::InsufficientBond
				);

				// NOTE: ledger must be updated prior to calling `Self::weight_of`.
				Self::update_ledger(&controller, &ledger);
				// update this staker in the sorted list, if they exist in it.
				if T::VoterList::contains(&stash) {
					let _ =
						T::VoterList::on_update(&stash, Self::weight_of(&ledger.stash)).defensive();
				}

				Self::deposit_event(Event::<T>::Bonded { stash, amount: extra });
			}
			Ok(())
		}

		/// Schedule a portion of the stash to be unlocked ready for transfer out after the bond
		/// period ends. If this leaves an amount actively bonded less than
		/// T::Currency::minimum_balance(), then it is increased to the full amount.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// Once the unlock period is done, you can call `withdraw_unbonded` to actually move
		/// the funds out of management ready for transfer.
		///
		/// No more than a limited number of unlocking chunks (see `MaxUnlockingChunks`)
		/// can co-exists at the same time. If there are no unlocking chunks slots available
		/// [`Call::withdraw_unbonded`] is called to remove some of the chunks (if possible).
		///
		/// If a user encounters the `InsufficientBond` error when calling this extrinsic,
		/// they should call `chill` first in order to free up their bonded funds.
		///
		/// Emits `Unbonded`.
		///
		/// See also [`Call::withdraw_unbonded`].
		#[pallet::call_index(2)]
		#[pallet::weight(
            T::WeightInfo::withdraw_unbonded_kill(SPECULATIVE_NUM_SPANS).saturating_add(T::WeightInfo::unbond()))
        ]
		pub fn unbond(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let controller = ensure_signed(origin)?;
			let unlocking = Self::ledger(&controller)
				.map(|l| l.unlocking.len())
				.ok_or(Error::<T>::NotController)?;

			// if there are no unlocking chunks available, try to withdraw chunks older than
			// `BondingDuration` to proceed with the unbonding.
			let maybe_withdraw_weight = {
				if unlocking == T::MaxUnlockingChunks::get() as usize {
					let real_num_slashing_spans =
						Self::slashing_spans(&controller).map_or(0, |s| s.iter().count());
					Some(Self::do_withdraw_unbonded(&controller, real_num_slashing_spans as u32)?)
				} else {
					None
				}
			};

			// we need to fetch the ledger again because it may have been mutated in the call
			// to `Self::do_withdraw_unbonded` above.
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let mut value = value.min(ledger.active);

			ensure!(
				ledger.unlocking.len() < T::MaxUnlockingChunks::get() as usize,
				Error::<T>::NoMoreChunks,
			);

			if !value.is_zero() {
				ledger.active -= value;

				// Avoid there being a dust balance left in the staking system.
				if ledger.active < T::Currency::minimum_balance() {
					value += ledger.active;
					ledger.active = Zero::zero();
				}

				let min_active_bond = if Nominators::<T>::contains_key(&ledger.stash) {
					MinNominatorBond::<T>::get()
				} else if Validators::<T>::contains_key(&ledger.stash) {
					MinValidatorBond::<T>::get()
				} else {
					Zero::zero()
				};

				// Make sure that the user maintains enough active bond for their role.
				// If a user runs into this error, they should chill first.
				ensure!(ledger.active >= min_active_bond, Error::<T>::InsufficientBond);

				// Note: in case there is no current era it is fine to bond one era more.
				let era = Self::current_era().unwrap_or(0) + T::BondingDuration::get();
				if let Some(mut chunk) =
					ledger.unlocking.last_mut().filter(|chunk| chunk.era == era)
				{
					// To keep the chunk count down, we only keep one chunk per era. Since
					// `unlocking` is a FiFo queue, if a chunk exists for `era` we know that it will
					// be the last one.
					chunk.value = chunk.value.defensive_saturating_add(value)
				} else {
					ledger
						.unlocking
						.try_push(UnlockChunk { value, era })
						.map_err(|_| Error::<T>::NoMoreChunks)?;
				};
				// NOTE: ledger must be updated prior to calling `Self::weight_of`.
				Self::update_ledger(&controller, &ledger);

				// update this staker in the sorted list, if they exist in it.
				if T::VoterList::contains(&ledger.stash) {
					let _ = T::VoterList::on_update(&ledger.stash, Self::weight_of(&ledger.stash))
						.defensive();
				}

				Self::deposit_event(Event::<T>::Unbonded { stash: ledger.stash, amount: value });
			}

			let actual_weight = if let Some(withdraw_weight) = maybe_withdraw_weight {
				Some(T::WeightInfo::unbond().saturating_add(withdraw_weight))
			} else {
				Some(T::WeightInfo::unbond())
			};

			Ok(actual_weight.into())
		}

		/// Remove any unlocked chunks from the `unlocking` queue from our management.
		///
		/// This essentially frees up that balance to be used by the stash account to do
		/// whatever it wants.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller.
		///
		/// Emits `Withdrawn`.
		///
		/// See also [`Call::unbond`].
		///
		/// # <weight>
		/// Complexity O(S) where S is the number of slashing spans to remove
		/// NOTE: Weight annotation is the kill scenario, we refund otherwise.
		/// # </weight>
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::withdraw_unbonded_kill(*num_slashing_spans))]
		pub fn withdraw_unbonded(
			origin: OriginFor<T>,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let controller = ensure_signed(origin)?;

			let actual_weight = Self::do_withdraw_unbonded(&controller, num_slashing_spans)?;
			Ok(Some(actual_weight).into())
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::validate())]
		pub fn validate(origin: OriginFor<T>, prefs: ValidatorPrefs) -> DispatchResult {
			let controller = ensure_signed(origin)?;

			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;

			ensure!(ledger.active >= MinValidatorBond::<T>::get(), Error::<T>::InsufficientBond);
			let stash = &ledger.stash;

			// ensure their commission is correct.
			ensure!(prefs.commission >= MinCommission::<T>::get(), Error::<T>::CommissionTooLow);

			// Only check limits if they are not already a validator.
			if !Validators::<T>::contains_key(stash) {
				// If this error is reached, we need to adjust the `MinValidatorBond` and start
				// calling `chill_other`. Until then, we explicitly block new validators to protect
				// the runtime.
				if let Some(max_validators) = MaxValidatorsCount::<T>::get() {
					ensure!(
						Validators::<T>::count() < max_validators,
						Error::<T>::TooManyValidators
					);
				}
			}

			Self::do_remove_nominator(stash);
			Self::do_add_validator(stash, prefs.clone());
			Self::deposit_event(Event::<T>::ValidatorPrefsSet { stash: ledger.stash, prefs });

			Ok(())
		}

		/// Declare the desire to nominate `targets` for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - The transaction's complexity is proportional to the size of `targets` (N)
		/// which is capped at CompactAssignments::LIMIT (T::MaxNominations).
		/// - Both the reads and writes follow a similar pattern.
		/// # </weight>
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::nominate(targets.len() as u32))]
		pub fn nominate(
			origin: OriginFor<T>,
			targets: Vec<AccountIdLookupOf<T>>,
		) -> DispatchResult {
			let controller = ensure_signed(origin)?;

			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			ensure!(ledger.active >= MinNominatorBond::<T>::get(), Error::<T>::InsufficientBond);
			let stash = &ledger.stash;

			// Only check limits if they are not already a nominator.
			if !Nominators::<T>::contains_key(stash) {
				// If this error is reached, we need to adjust the `MinNominatorBond` and start
				// calling `chill_other`. Until then, we explicitly block new nominators to protect
				// the runtime.
				if let Some(max_nominators) = MaxNominatorsCount::<T>::get() {
					ensure!(
						Nominators::<T>::count() < max_nominators,
						Error::<T>::TooManyNominators
					);
				}
			}

			ensure!(!targets.is_empty(), Error::<T>::EmptyTargets);
			ensure!(targets.len() <= T::MaxNominations::get() as usize, Error::<T>::TooManyTargets);

			let old = Nominators::<T>::get(stash).map_or_else(Vec::new, |x| x.targets.into_inner());

			let targets: BoundedVec<_, _> = targets
				.into_iter()
				.map(|t| T::Lookup::lookup(t).map_err(DispatchError::from))
				.map(|n| {
					n.and_then(|n| {
						if old.contains(&n) || !Validators::<T>::get(&n).blocked {
							Ok(n)
						} else {
							Err(Error::<T>::BadTarget.into())
						}
					})
				})
				.collect::<Result<Vec<_>, _>>()?
				.try_into()
				.map_err(|_| Error::<T>::TooManyNominators)?;

			let nominations = Nominations {
				targets,
				// Initial nominations are considered submitted at era 0. See `Nominations` doc.
				submitted_in: Self::current_era().unwrap_or(0),
				suppressed: false,
			};

			Self::do_remove_validator(stash);
			Self::do_add_nominator(stash, nominations);
			Ok(())
		}

		/// Declare no desire to either validate or nominate.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains one read.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::chill())]
		pub fn chill(origin: OriginFor<T>) -> DispatchResult {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			Self::chill_stash(&ledger.stash);
			Ok(())
		}

		/// (Re-)set the payment target for a controller.
		///
		/// Effects will be felt instantly (as soon as this function is completed successfully).
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains a limited number of reads.
		/// - Writes are limited to the `origin` account key.
		/// ---------
		/// - Weight: O(1)
		/// - DB Weight:
		///     - Read: Ledger
		///     - Write: Payee
		/// # </weight>
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::set_payee())]
		pub fn set_payee(
			origin: OriginFor<T>,
			payee: RewardDestination<T::AccountId>,
		) -> DispatchResult {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = &ledger.stash;
			<Payee<T>>::insert(stash, payee);
			Ok(())
		}

		/// (Re-)set the controller of a stash.
		///
		/// Effects will be felt instantly (as soon as this function is completed successfully).
		///
		/// The dispatch origin for this call must be _Signed_ by the stash, not the controller.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains a limited number of reads.
		/// - Writes are limited to the `origin` account key.
		/// ----------
		/// Weight: O(1)
		/// DB Weight:
		/// - Read: Bonded, Ledger New Controller, Ledger Old Controller
		/// - Write: Bonded, Ledger New Controller, Ledger Old Controller
		/// # </weight>
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::set_controller())]
		pub fn set_controller(
			origin: OriginFor<T>,
			controller: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let stash = ensure_signed(origin)?;
			let old_controller = Self::bonded(&stash).ok_or(Error::<T>::NotStash)?;
			let controller = T::Lookup::lookup(controller)?;
			if <Ledger<T>>::contains_key(&controller) {
				return Err(Error::<T>::AlreadyPaired.into())
			}
			if controller != old_controller {
				<Bonded<T>>::insert(&stash, &controller);
				if let Some(l) = <Ledger<T>>::take(&old_controller) {
					<Ledger<T>>::insert(&controller, l);
				}
			}
			Ok(())
		}

		/// Sets the ideal number of validators.
		///
		/// The dispatch origin must be Root.
		///
		/// # <weight>
		/// Weight: O(1)
		/// Write: Validator Count
		/// # </weight>
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::set_validator_count())]
		pub fn set_validator_count(
			origin: OriginFor<T>,
			#[pallet::compact] new: u32,
		) -> DispatchResult {
			ensure_root(origin)?;
			// ensure new validator count does not exceed maximum winners
			// support by election provider.
			ensure!(
				new <= <T::ElectionProvider as ElectionProviderBase>::MaxWinners::get(),
				Error::<T>::TooManyValidators
			);
			ValidatorCount::<T>::put(new);
			Ok(())
		}

		/// Increments the ideal number of validators upto maximum of
		/// `ElectionProviderBase::MaxWinners`.
		///
		/// The dispatch origin must be Root.
		///
		/// # <weight>
		/// Same as [`Self::set_validator_count`].
		/// # </weight>
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::set_validator_count())]
		pub fn increase_validator_count(
			origin: OriginFor<T>,
			#[pallet::compact] additional: u32,
		) -> DispatchResult {
			ensure_root(origin)?;
			let old = ValidatorCount::<T>::get();
			let new = old.checked_add(additional).ok_or(ArithmeticError::Overflow)?;
			ensure!(
				new <= <T::ElectionProvider as ElectionProviderBase>::MaxWinners::get(),
				Error::<T>::TooManyValidators
			);

			ValidatorCount::<T>::put(new);
			Ok(())
		}

		/// Scale up the ideal number of validators by a factor upto maximum of
		/// `ElectionProviderBase::MaxWinners`.
		///
		/// The dispatch origin must be Root.
		///
		/// # <weight>
		/// Same as [`Self::set_validator_count`].
		/// # </weight>
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::set_validator_count())]
		pub fn scale_validator_count(origin: OriginFor<T>, factor: Percent) -> DispatchResult {
			ensure_root(origin)?;
			let old = ValidatorCount::<T>::get();
			let new = old.checked_add(factor.mul_floor(old)).ok_or(ArithmeticError::Overflow)?;

			ensure!(
				new <= <T::ElectionProvider as ElectionProviderBase>::MaxWinners::get(),
				Error::<T>::TooManyValidators
			);

			ValidatorCount::<T>::put(new);
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
		///
		/// # <weight>
		/// - No arguments.
		/// - Weight: O(1)
		/// - Write: ForceEra
		/// # </weight>
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::force_no_eras())]
		pub fn force_no_eras(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			Self::set_force_era(Forcing::ForceNone);
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
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::force_new_era())]
		pub fn force_new_era(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			Self::set_force_era(Forcing::ForceNew);
			Ok(())
		}

		/// Set the validators who cannot be slashed (if any).
		///
		/// The dispatch origin must be Root.
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::set_invulnerables(invulnerables.len() as u32))]
		pub fn set_invulnerables(
			origin: OriginFor<T>,
			invulnerables: Vec<T::AccountId>,
		) -> DispatchResult {
			ensure_root(origin)?;
			<Invulnerables<T>>::put(invulnerables);
			Ok(())
		}

		/// Force a current staker to become completely unstaked, immediately.
		///
		/// The dispatch origin must be Root.
		#[pallet::call_index(15)]
		#[pallet::weight(T::WeightInfo::force_unstake(*num_slashing_spans))]
		pub fn force_unstake(
			origin: OriginFor<T>,
			stash: T::AccountId,
			num_slashing_spans: u32,
		) -> DispatchResult {
			ensure_root(origin)?;

			// Remove all staking-related information.
			Self::kill_stash(&stash, num_slashing_spans)?;

			// Remove the lock.
			T::Currency::remove_lock(STAKING_ID, &stash);
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
		#[pallet::call_index(16)]
		#[pallet::weight(T::WeightInfo::force_new_era_always())]
		pub fn force_new_era_always(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			Self::set_force_era(Forcing::ForceAlways);
			Ok(())
		}

		/// Cancel enactment of a deferred slash.
		///
		/// Can be called by the `T::AdminOrigin`.
		///
		/// Parameters: era and indices of the slashes for that era to kill.
		#[pallet::call_index(17)]
		#[pallet::weight(T::WeightInfo::cancel_deferred_slash(slash_indices.len() as u32))]
		pub fn cancel_deferred_slash(
			origin: OriginFor<T>,
			era: EraIndex,
			slash_indices: Vec<u32>,
		) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;

			ensure!(!slash_indices.is_empty(), Error::<T>::EmptyTargets);
			ensure!(is_sorted_and_unique(&slash_indices), Error::<T>::NotSortedAndUnique);

			let mut unapplied = <Self as Store>::UnappliedSlashes::get(&era);
			let last_item = slash_indices[slash_indices.len() - 1];
			ensure!((last_item as usize) < unapplied.len(), Error::<T>::InvalidSlashIndex);

			for (removed, index) in slash_indices.into_iter().enumerate() {
				let index = (index as usize) - removed;
				unapplied.remove(index);
			}

			<Self as Store>::UnappliedSlashes::insert(&era, &unapplied);
			Ok(())
		}

		/// Pay out all the stakers behind a single validator for a single era.
		///
		/// - `validator_stash` is the stash account of the validator. Their nominators, up to
		///   `T::MaxNominatorRewardedPerValidator`, will also receive their rewards.
		/// - `era` may be any era between `[current_era - history_depth; current_era]`.
		///
		/// The origin of this call must be _Signed_. Any account can call this function, even if
		/// it is not one of the stakers.
		///
		/// # <weight>
		/// - Time complexity: at most O(MaxNominatorRewardedPerValidator).
		/// - Contains a limited number of reads and writes.
		/// -----------
		/// N is the Number of payouts for the validator (including the validator)
		/// Weight:
		/// - Reward Destination Staked: O(N)
		/// - Reward Destination Controller (Creating): O(N)
		///
		///   NOTE: weights are assuming that payouts are made to alive stash account (Staked).
		///   Paying even a dead controller is cheaper weight-wise. We don't do any refunds here.
		/// # </weight>
		#[pallet::call_index(18)]
		#[pallet::weight(T::WeightInfo::payout_stakers_alive_staked(
			T::MaxNominatorRewardedPerValidator::get()
		))]
		pub fn payout_stakers(
			origin: OriginFor<T>,
			validator_stash: T::AccountId,
			era: EraIndex,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			Self::do_payout_stakers(validator_stash, era)
		}

		/// Rebond a portion of the stash scheduled to be unlocked.
		///
		/// The dispatch origin must be signed by the controller.
		///
		/// # <weight>
		/// - Time complexity: O(L), where L is unlocking chunks
		/// - Bounded by `MaxUnlockingChunks`.
		/// - Storage changes: Can't increase storage, only decrease it.
		/// # </weight>
		#[pallet::call_index(19)]
		#[pallet::weight(T::WeightInfo::rebond(T::MaxUnlockingChunks::get() as u32))]
		pub fn rebond(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			ensure!(!ledger.unlocking.is_empty(), Error::<T>::NoUnlockChunk);

			let initial_unlocking = ledger.unlocking.len() as u32;
			let (ledger, rebonded_value) = ledger.rebond(value);
			// Last check: the new active amount of ledger must be more than ED.
			ensure!(ledger.active >= T::Currency::minimum_balance(), Error::<T>::InsufficientBond);

			Self::deposit_event(Event::<T>::Bonded {
				stash: ledger.stash.clone(),
				amount: rebonded_value,
			});

			// NOTE: ledger must be updated prior to calling `Self::weight_of`.
			Self::update_ledger(&controller, &ledger);
			if T::VoterList::contains(&ledger.stash) {
				let _ = T::VoterList::on_update(&ledger.stash, Self::weight_of(&ledger.stash))
					.defensive();
			}

			let removed_chunks = 1u32 // for the case where the last iterated chunk is not removed
				.saturating_add(initial_unlocking)
				.saturating_sub(ledger.unlocking.len() as u32);
			Ok(Some(T::WeightInfo::rebond(removed_chunks)).into())
		}

		/// Remove all data structures concerning a staker/stash once it is at a state where it can
		/// be considered `dust` in the staking system. The requirements are:
		///
		/// 1. the `total_balance` of the stash is below existential deposit.
		/// 2. or, the `ledger.total` of the stash is below existential deposit.
		///
		/// The former can happen in cases like a slash; the latter when a fully unbonded account
		/// is still receiving staking rewards in `RewardDestination::Staked`.
		///
		/// It can be called by anyone, as long as `stash` meets the above requirements.
		///
		/// Refunds the transaction fees upon successful execution.
		#[pallet::call_index(20)]
		#[pallet::weight(T::WeightInfo::reap_stash(*num_slashing_spans))]
		pub fn reap_stash(
			origin: OriginFor<T>,
			stash: T::AccountId,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;

			let ed = T::Currency::minimum_balance();
			let reapable = T::Currency::total_balance(&stash) < ed ||
				Self::ledger(Self::bonded(stash.clone()).ok_or(Error::<T>::NotStash)?)
					.map(|l| l.total)
					.unwrap_or_default() < ed;
			ensure!(reapable, Error::<T>::FundedTarget);

			Self::kill_stash(&stash, num_slashing_spans)?;
			T::Currency::remove_lock(STAKING_ID, &stash);

			Ok(Pays::No.into())
		}

		/// Remove the given nominations from the calling validator.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// - `who`: A list of nominator stash accounts who are nominating this validator which
		///   should no longer be nominating this validator.
		///
		/// Note: Making this call only makes sense if you first set the validator preferences to
		/// block any further nominations.
		#[pallet::call_index(21)]
		#[pallet::weight(T::WeightInfo::kick(who.len() as u32))]
		pub fn kick(origin: OriginFor<T>, who: Vec<AccountIdLookupOf<T>>) -> DispatchResult {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = &ledger.stash;

			for nom_stash in who
				.into_iter()
				.map(T::Lookup::lookup)
				.collect::<Result<Vec<T::AccountId>, _>>()?
				.into_iter()
			{
				Nominators::<T>::mutate(&nom_stash, |maybe_nom| {
					if let Some(ref mut nom) = maybe_nom {
						if let Some(pos) = nom.targets.iter().position(|v| v == stash) {
							nom.targets.swap_remove(pos);
							Self::deposit_event(Event::<T>::Kicked {
								nominator: nom_stash.clone(),
								stash: stash.clone(),
							});
						}
					}
				});
			}

			Ok(())
		}

		/// Update the various staking configurations .
		///
		/// * `min_nominator_bond`: The minimum active bond needed to be a nominator.
		/// * `min_validator_bond`: The minimum active bond needed to be a validator.
		/// * `max_nominator_count`: The max number of users who can be a nominator at once. When
		///   set to `None`, no limit is enforced.
		/// * `max_validator_count`: The max number of users who can be a validator at once. When
		///   set to `None`, no limit is enforced.
		/// * `chill_threshold`: The ratio of `max_nominator_count` or `max_validator_count` which
		///   should be filled in order for the `chill_other` transaction to work.
		/// * `min_commission`: The minimum amount of commission that each validators must maintain.
		///   This is checked only upon calling `validate`. Existing validators are not affected.
		///
		/// RuntimeOrigin must be Root to call this function.
		///
		/// NOTE: Existing nominators and validators will not be affected by this update.
		/// to kick people under the new limits, `chill_other` should be called.
		// We assume the worst case for this call is either: all items are set or all items are
		// removed.
		#[pallet::call_index(22)]
		#[pallet::weight(
			T::WeightInfo::set_staking_configs_all_set()
				.max(T::WeightInfo::set_staking_configs_all_remove())
		)]
		pub fn set_staking_configs(
			origin: OriginFor<T>,
			min_nominator_bond: ConfigOp<BalanceOf<T>>,
			min_validator_bond: ConfigOp<BalanceOf<T>>,
			max_nominator_count: ConfigOp<u32>,
			max_validator_count: ConfigOp<u32>,
			chill_threshold: ConfigOp<Percent>,
			min_commission: ConfigOp<Perbill>,
		) -> DispatchResult {
			ensure_root(origin)?;

			macro_rules! config_op_exp {
				($storage:ty, $op:ident) => {
					match $op {
						ConfigOp::Noop => (),
						ConfigOp::Set(v) => <$storage>::put(v),
						ConfigOp::Remove => <$storage>::kill(),
					}
				};
			}

			config_op_exp!(MinNominatorBond<T>, min_nominator_bond);
			config_op_exp!(MinValidatorBond<T>, min_validator_bond);
			config_op_exp!(MaxNominatorsCount<T>, max_nominator_count);
			config_op_exp!(MaxValidatorsCount<T>, max_validator_count);
			config_op_exp!(ChillThreshold<T>, chill_threshold);
			config_op_exp!(MinCommission<T>, min_commission);
			Ok(())
		}
		/// Declare a `controller` to stop participating as either a validator or nominator.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_, but can be called by anyone.
		///
		/// If the caller is the same as the controller being targeted, then no further checks are
		/// enforced, and this function behaves just like `chill`.
		///
		/// If the caller is different than the controller being targeted, the following conditions
		/// must be met:
		///
		/// * `controller` must belong to a nominator who has become non-decodable,
		///
		/// Or:
		///
		/// * A `ChillThreshold` must be set and checked which defines how close to the max
		///   nominators or validators we must reach before users can start chilling one-another.
		/// * A `MaxNominatorCount` and `MaxValidatorCount` must be set which is used to determine
		///   how close we are to the threshold.
		/// * A `MinNominatorBond` and `MinValidatorBond` must be set and checked, which determines
		///   if this is a person that should be chilled because they have not met the threshold
		///   bond required.
		///
		/// This can be helpful if bond requirements are updated, and we need to remove old users
		/// who do not satisfy these requirements.
		#[pallet::call_index(23)]
		#[pallet::weight(T::WeightInfo::chill_other())]
		pub fn chill_other(origin: OriginFor<T>, controller: T::AccountId) -> DispatchResult {
			// Anyone can call this function.
			let caller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = ledger.stash;

			// In order for one user to chill another user, the following conditions must be met:
			//
			// * `controller` belongs to a nominator who has become non-decodable,
			//
			// Or
			//
			// * A `ChillThreshold` is set which defines how close to the max nominators or
			//   validators we must reach before users can start chilling one-another.
			// * A `MaxNominatorCount` and `MaxValidatorCount` which is used to determine how close
			//   we are to the threshold.
			// * A `MinNominatorBond` and `MinValidatorBond` which is the final condition checked to
			//   determine this is a person that should be chilled because they have not met the
			//   threshold bond required.
			//
			// Otherwise, if caller is the same as the controller, this is just like `chill`.

			if Nominators::<T>::contains_key(&stash) && Nominators::<T>::get(&stash).is_none() {
				Self::chill_stash(&stash);
				return Ok(())
			}

			if caller != controller {
				let threshold = ChillThreshold::<T>::get().ok_or(Error::<T>::CannotChillOther)?;
				let min_active_bond = if Nominators::<T>::contains_key(&stash) {
					let max_nominator_count =
						MaxNominatorsCount::<T>::get().ok_or(Error::<T>::CannotChillOther)?;
					let current_nominator_count = Nominators::<T>::count();
					ensure!(
						threshold * max_nominator_count < current_nominator_count,
						Error::<T>::CannotChillOther
					);
					MinNominatorBond::<T>::get()
				} else if Validators::<T>::contains_key(&stash) {
					let max_validator_count =
						MaxValidatorsCount::<T>::get().ok_or(Error::<T>::CannotChillOther)?;
					let current_validator_count = Validators::<T>::count();
					ensure!(
						threshold * max_validator_count < current_validator_count,
						Error::<T>::CannotChillOther
					);
					MinValidatorBond::<T>::get()
				} else {
					Zero::zero()
				};

				ensure!(ledger.active < min_active_bond, Error::<T>::CannotChillOther);
			}

			Self::chill_stash(&stash);
			Ok(())
		}

		/// Force a validator to have at least the minimum commission. This will not affect a
		/// validator who already has a commission greater than or equal to the minimum. Any account
		/// can call this.
		#[pallet::call_index(24)]
		#[pallet::weight(T::WeightInfo::force_apply_min_commission())]
		pub fn force_apply_min_commission(
			origin: OriginFor<T>,
			validator_stash: T::AccountId,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let min_commission = MinCommission::<T>::get();
			Validators::<T>::try_mutate_exists(validator_stash, |maybe_prefs| {
				maybe_prefs
					.as_mut()
					.map(|prefs| {
						(prefs.commission < min_commission)
							.then(|| prefs.commission = min_commission)
					})
					.ok_or(Error::<T>::NotStash)
			})?;
			Ok(())
		}

		/// Sets the minimum amount of commission that each validators must maintain.
		///
		/// This call has lower privilege requirements than `set_staking_config` and can be called
		/// by the `T::AdminOrigin`. Root can always call this.
		#[pallet::call_index(25)]
		#[pallet::weight(T::WeightInfo::set_min_commission())]
		pub fn set_min_commission(origin: OriginFor<T>, new: Perbill) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;
			MinCommission::<T>::put(new);
			Ok(())
		}
	}
}

/// Check that list is sorted and has no duplicates.
fn is_sorted_and_unique(list: &[u32]) -> bool {
	list.windows(2).all(|w| w[0] < w[1])
}
