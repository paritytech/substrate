// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! # Stakers pallet.
//!
//! This is the base pallet for the entire staking sub-system, and deals with the existence and
//! modifications of the actors that play a role in the staking system, e.g. the `stakers`.
//!
//! Stakers can wear either of the following hats:
//!
//! 1. chilled: Also known as simply *bonded*. This is the he default state of being a staker with
//!    no particular activity.
//! 2. validators: Someone who intents to a candidate for the validator selection.
//! 3. nominator: Someone who is intending their opinion on a subset of validators that they wish to
//!    see active.

use frame_support::{
	dispatch::Codec,
	pallet_prelude::*,
	traits::{
		Currency, DefensiveSaturating, Get, LockIdentifier, LockableCurrency, WithdrawReasons,
	},
};
use frame_system::ensure_signed;
use sp_runtime::{
	traits::{CheckedSub, StaticLookup, Zero},
	DispatchError, Perbill, Percent,
};
use sp_staking::EraIndex;
use sp_std::prelude::*;
pub const STAKING_ID: LockIdentifier = *b"staking ";

pub mod types;
pub use pallet::*;
use types::*;

pub trait ValidatorSelection {
	fn current_era() -> EraIndex;
}

pub trait Stakers {
	type MaxNominations: Get<u32>;
}

pub trait OnStakersUpdated<AccountId, Balance> {
	fn on_bonded() {}
	fn on_unbonded() {}
	fn on_nominated() {}
	fn on_validated() {}
	fn on_chilled() {}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

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

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The staking balance.
		type Currency: LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;

		/// Maximum number of nominations per nominator.
		#[pallet::constant]
		type MaxNominations: Get<u32>;

		/// Number of eras that staked funds must remain bonded for.
		#[pallet::constant]
		type BondingDuration: Get<EraIndex>;

		/// The maximum number of `unlocking` chunks a [`StakingLedger`] can have. Effectively
		/// determines how many unique eras a staker may be unbonding in.
		#[pallet::constant]
		type MaxUnlockingChunks: Get<u32>;

		type OnStakersUpdated: OnStakersUpdated<Self::AccountId, BalanceOf<Self>>;
		type ValidatorSelection: ValidatorSelection;
	}

	/// Map from all locked "stash" accounts to the controller account.
	#[pallet::storage]
	#[pallet::getter(fn bonded)]
	pub type Bonded<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, T::AccountId>;

	/// The minimum active bond to become and maintain the role of a nominator.
	#[pallet::storage]
	pub type MinNominatorBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The minimum active bond to become and maintain the role of a validator.
	#[pallet::storage]
	pub type MinValidatorBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The minimum amount of commission that validators can set.
	///
	/// If set to `0`, no limit exists.
	#[pallet::storage]
	pub type MinCommission<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
	#[pallet::storage]
	#[pallet::getter(fn ledger)]
	pub type Ledger<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, StakingLedger<T>>;

	/// The map from (wannabe) validator stash key to the preferences of that validator.
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
	#[pallet::storage]
	#[pallet::getter(fn nominators)]
	pub type Nominators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Nominations<T>>;

	/// The maximum nominator count before we stop allowing new validators to join.
	///
	/// When this value is not set, no limits are enforced.
	#[pallet::storage]
	pub type MaxNominatorsCount<T> = StorageValue<_, u32, OptionQuery>;

	/// The threshold for when users can start calling `chill_other` for other validators /
	/// nominators. The threshold is compared to the actual number of validators / nominators
	/// (`CountFor*`) in the system compared to the configured max (`Max*Count`).
	#[pallet::storage]
	pub(crate) type ChillThreshold<T: Config> = StorageValue<_, Percent, OptionQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub validator_count: u32,
		pub minimum_validator_count: u32,
		pub min_nominator_bond: BalanceOf<T>,
		pub min_validator_bond: BalanceOf<T>,
		pub max_validator_count: Option<u32>,
		pub max_nominator_count: Option<u32>,
		pub stakers:
			Vec<(T::AccountId, T::AccountId, BalanceOf<T>, crate::StakerStatus<T::AccountId>)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			// TODO: can't this be simplified.
			GenesisConfig {
				validator_count: Default::default(),
				minimum_validator_count: Default::default(),
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
					T::Currency::free_balance(&stash) >= balance,
					"Stash does not have enough balance to bond."
				);
				frame_support::assert_ok!(<Pallet<T>>::bond(
					T::Origin::from(Some(stash.clone()).into()),
					T::Lookup::unlookup(controller.clone()),
					balance,
				));
				frame_support::assert_ok!(match status {
					crate::StakerStatus::Validator => <Pallet<T>>::validate(
						T::Origin::from(Some(controller.clone()).into()),
						Default::default(),
					),
					crate::StakerStatus::Nominator(votes) => <Pallet<T>>::nominate(
						T::Origin::from(Some(controller.clone()).into()),
						votes.iter().map(|l| T::Lookup::unlookup(l.clone())).collect(),
					),
					_ => Ok(()),
				});
			}
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		Bonded(T::AccountId, BalanceOf<T>),
		/// An account has unbonded this amount. \[stash, amount\]
		Unbonded(T::AccountId, BalanceOf<T>),
		/// An account has called `withdraw_unbonded` and removed unbonding chunks worth `Balance`
		/// from the unlocking queue. \[stash, amount\]
		Withdrawn(T::AccountId, BalanceOf<T>),
		/// A nominator has been kicked from a validator. \[nominator, stash\]
		Kicked(T::AccountId, T::AccountId),
		/// An account has stopped participating as either a validator or nominator \[stash\]
		Chilled(T::AccountId),
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
		/// Cannot have a validator or nominator role, with value less than the minimum defined by
		/// governance (see `MinValidatorBond` and `MinNominatorBond`). If unbonding is the
		/// intention, `chill` first to remove one's role as validator/nominator.
		InsufficientBond,
		/// Can not schedule more unlock chunks.
		NoMoreChunks,
		BadState,
		/// Can not rebond without unlocking chunks.
		NoUnlockChunk,
		/// Attempting to target a stash that still has funds.
		FundedTarget,
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
		/// ------------------
		/// # </weight>
		#[pallet::weight(0)]
		pub fn bond(
			origin: OriginFor<T>,
			controller: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] value: BalanceOf<T>,
		) -> DispatchResult {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::contains_key(&stash) {
				Err(Error::<T>::AlreadyBonded)?
			}

			let controller = T::Lookup::lookup(controller)?;

			if <Ledger<T>>::contains_key(&controller) {
				Err(Error::<T>::AlreadyPaired)?
			}

			// Reject a bond which is considered to be _dust_.
			if value < T::Currency::minimum_balance() {
				Err(Error::<T>::InsufficientBond)?
			}

			frame_system::Pallet::<T>::inc_consumers(&stash).map_err(|_| Error::<T>::BadState)?;

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate and remove once you unbond __everything__.
			<Bonded<T>>::insert(&stash, &controller);

			// TODO:LOGIC: move this to a new storage item in the rewards pallet.
			// <Payee<T>>::insert(&stash, payee);
			// let current_era = CurrentEra::<T>::get().unwrap_or(0);
			// let history_depth = Self::history_depth();
			// let last_reward_era = current_era.saturating_sub(history_depth);

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);
			Self::deposit_event(Event::<T>::Bonded(stash.clone(), value));
			let item =
				StakingLedger { stash, total: value, active: value, unlocking: Default::default() };
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
		#[pallet::weight(0)]
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
				Self::deposit_event(Event::<T>::Bonded(stash.clone(), extra));
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
		/// can co-exists at the same time. In that case, [`Call::withdraw_unbonded`] need
		/// to be called first to remove some of the chunks (if possible).
		///
		/// If a user encounters the `InsufficientBond` error when calling this extrinsic,
		/// they should call `chill` first in order to free up their bonded funds.
		///
		/// Emits `Unbonded`.
		///
		/// See also [`Call::withdraw_unbonded`].
		#[pallet::weight(0)]
		pub fn unbond(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
		) -> DispatchResult {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			ensure!(
				ledger.unlocking.len() < T::MaxUnlockingChunks::get() as usize,
				Error::<T>::NoMoreChunks,
			);

			let mut value = value.min(ledger.active);

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
				let era = T::ValidatorSelection::current_era() + T::BondingDuration::get();
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
				Self::deposit_event(Event::<T>::Unbonded(ledger.stash, value));
			}
			Ok(())
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
		#[pallet::weight(0)]
		pub fn withdraw_unbonded(
			origin: OriginFor<T>,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let (stash, old_total) = (ledger.stash.clone(), ledger.total);
			ledger = ledger.consolidate_unlocked(T::ValidatorSelection::current_era());

			let post_info_weight = if ledger.unlocking.is_empty() &&
				ledger.active < T::Currency::minimum_balance()
			{
				// This account must have called `unbond()` with some value that caused the active
				// portion to fall below existential deposit + will have no more unlocking chunks
				// left. We can now safely remove all staking-related information.
				Self::kill_stash(&stash, num_slashing_spans)?;
				// Remove the lock.
				T::Currency::remove_lock(STAKING_ID, &stash);
				// This is worst case scenario, so we use the full weight and return None
				None
			} else {
				// This was the consequence of a partial unbond. just update the ledger and move on.
				Self::update_ledger(&controller, &ledger);

				// This is only an update, so we use less overall weight.
				// Some(T::WeightInfo::withdraw_unbonded_update(num_slashing_spans))
				Some(0)
			};

			// `old_total` should never be less than the new total because
			// `consolidate_unlocked` strictly subtracts balance.
			if ledger.total < old_total {
				// Already checked that this won't overflow by entry condition.
				let value = old_total - ledger.total;
				Self::deposit_event(Event::<T>::Withdrawn(stash, value));
			}

			Ok(post_info_weight.into())
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		#[pallet::weight(0)]
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
			Self::do_add_validator(stash, prefs);
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
		#[pallet::weight(0)]
		pub fn nominate(
			origin: OriginFor<T>,
			targets: Vec<<T::Lookup as StaticLookup>::Source>,
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
				submitted_in: T::ValidatorSelection::current_era(),
				suppressed: false,
			};

			Self::do_remove_validator(stash);
			Self::do_add_nominator(stash, nominations);
			Ok(())
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
		#[pallet::weight(0)]
		pub fn kick(
			origin: OriginFor<T>,
			who: Vec<<T::Lookup as StaticLookup>::Source>,
		) -> DispatchResult {
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
							Self::deposit_event(Event::<T>::Kicked(
								nom_stash.clone(),
								stash.clone(),
							));
						}
					}
				});
			}

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
		#[pallet::weight(0)]
		pub fn chill(origin: OriginFor<T>) -> DispatchResult {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			Self::chill_stash(&ledger.stash);
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
		#[pallet::weight(0)]
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

		/// (Re-)set the controller of a stash.
		///
		/// Effects will be felt at the beginning of the next era.
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
		#[pallet::weight(0)]
		pub fn set_controller(
			origin: OriginFor<T>,
			controller: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let stash = ensure_signed(origin)?;
			let old_controller = Self::bonded(&stash).ok_or(Error::<T>::NotStash)?;
			let controller = T::Lookup::lookup(controller)?;
			if <Ledger<T>>::contains_key(&controller) {
				Err(Error::<T>::AlreadyPaired)?
			}
			if controller != old_controller {
				<Bonded<T>>::insert(&stash, &controller);
				if let Some(l) = <Ledger<T>>::take(&old_controller) {
					<Ledger<T>>::insert(&controller, l);
				}
			}
			Ok(())
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
		#[pallet::weight(0)]
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

			Self::deposit_event(Event::<T>::Bonded(ledger.stash.clone(), rebonded_value));

			// NOTE: ledger must be updated prior to calling `Self::weight_of`.
			Self::update_ledger(&controller, &ledger);

			let removed_chunks = 1u32 // for the case where the last iterated chunk is not removed
				.saturating_add(initial_unlocking)
				.saturating_sub(ledger.unlocking.len() as u32);
			// Ok(Some(T::WeightInfo::rebond(removed_chunks)).into())
			Ok(Some(0).into())
		}

		/// Remove all data structures concerning a staker/stash once it is at a state where it can
		/// be considered `dust` in the staking system. The requirements are:
		///
		/// 1. the `total_balance` of the stash is below existential deposit.
		/// 2. or, the `ledger.total` of the stash is below existential deposit.
		///
		/// It can be called by anyone, as long as `stash` meets the above requirements.
		///
		/// Refunds the transaction fees upon successful execution.
		#[pallet::weight(0)]
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

		/// Force a validator to have at least the minimum commission. This will not affect a
		/// validator who already has a commission greater than or equal to the minimum. Any account
		/// can call this.
		#[pallet::weight(0)]
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

		/// Force a current staker to become completely unstaked, immediately.
		///
		/// The dispatch origin must be Root.
		#[pallet::weight(0)]
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
		/// Origin must be Root to call this function.
		///
		/// NOTE: Existing nominators and validators will not be affected by this update.
		/// to kick people under the new limits, `chill_other` should be called.
		// We assume the worst case for this call is either: all items are set or all items are
		// removed.
		#[pallet::weight(0)]
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
	}

	impl<T: Config> Pallet<T> {
		/// Update the ledger for a controller.
		///
		/// This will also update the stash lock.
		pub(crate) fn update_ledger(controller: &T::AccountId, ledger: &StakingLedger<T>) {
			// TODO: update voter list if needed.
			T::Currency::set_lock(STAKING_ID, &ledger.stash, ledger.total, WithdrawReasons::all());
			<Ledger<T>>::insert(controller, ledger);
		}

		/// Chill a stash account.
		pub(crate) fn chill_stash(stash: &T::AccountId) {
			let chilled_as_validator = Self::do_remove_validator(stash);
			let chilled_as_nominator = Self::do_remove_nominator(stash);
			if chilled_as_validator || chilled_as_nominator {
				Self::deposit_event(Event::<T>::Chilled(stash.clone()));
			}
		}

		/// Remove all associated data of a stash account from the staking system.
		///
		/// Assumes storage is upgraded before calling.
		///
		/// This is called:
		/// - after a `withdraw_unbonded()` call that frees all of a stash's bonded balance.
		/// - through `reap_stash()` if the balance has fallen to zero (through slashing).
		pub(crate) fn kill_stash(stash: &T::AccountId, num_slashing_spans: u32) -> DispatchResult {
			let controller = <Bonded<T>>::get(stash).ok_or(Error::<T>::NotStash)?;

			// slashing::clear_stash_metadata::<T>(stash, num_slashing_spans)?;
			// <Payee<T>>::remove(stash);

			<Bonded<T>>::remove(stash);
			<Ledger<T>>::remove(&controller);

			Self::do_remove_validator(stash);
			Self::do_remove_nominator(stash);

			frame_system::Pallet::<T>::dec_consumers(stash);

			Ok(())
		}

		/// This function will add a nominator to the `Nominators` storage map,
		/// and `VoterList`.
		///
		/// If the nominator already exists, their nominations will be updated.
		///
		/// NOTE: you must ALWAYS use this function to add nominator or update their targets. Any
		/// access to `Nominators` or `VoterList` outside of this function is almost certainly
		/// wrong.
		pub fn do_add_nominator(who: &T::AccountId, nominations: Nominations<T>) {
			// if !Nominators::<T>::contains_key(who) {
			// maybe update sorted list.
			// let _ = T::VoterList::on_insert(who.clone(), Self::weight_of(who))
			// 	.defensive_unwrap_or_default();
			// }
			Nominators::<T>::insert(who, nominations);

			// debug_assert_eq!(
			// 	Nominators::<T>::count() + Validators::<T>::count(),
			// 	T::VoterList::count()
			// );
			// debug_assert_eq!(T::VoterList::sanity_check(), Ok(()));
		}

		/// This function will remove a nominator from the `Nominators` storage map,
		/// and `VoterList`.
		///
		/// Returns true if `who` was removed from `Nominators`, otherwise false.
		///
		/// NOTE: you must ALWAYS use this function to remove a nominator from the system. Any
		/// access to `Nominators` or `VoterList` outside of this function is almost certainly
		/// wrong.
		pub fn do_remove_nominator(who: &T::AccountId) -> bool {
			let outcome = if Nominators::<T>::contains_key(who) {
				Nominators::<T>::remove(who);
				// T::VoterList::on_remove(who);
				true
			} else {
				false
			};

			// debug_assert_eq!(T::VoterList::sanity_check(), Ok(()));
			// debug_assert_eq!(
			// 	Nominators::<T>::count() + Validators::<T>::count(),
			// 	T::VoterList::count()
			// );

			outcome
		}

		/// This function will add a validator to the `Validators` storage map.
		///
		/// If the validator already exists, their preferences will be updated.
		///
		/// NOTE: you must ALWAYS use this function to add a validator to the system. Any access to
		/// `Validators` or `VoterList` outside of this function is almost certainly
		/// wrong.
		pub fn do_add_validator(who: &T::AccountId, prefs: ValidatorPrefs) {
			// if !Validators::<T>::contains_key(who) {
			// 	// maybe update sorted list.
			// 	let _ = T::VoterList::on_insert(who.clone(), Self::weight_of(who))
			// 		.defensive_unwrap_or_default();
			// }
			Validators::<T>::insert(who, prefs);

			// debug_assert_eq!(
			// 	Nominators::<T>::count() + Validators::<T>::count(),
			// 	T::VoterList::count()
			// );
			// debug_assert_eq!(T::VoterList::sanity_check(), Ok(()));
		}

		/// This function will remove a validator from the `Validators` storage map.
		///
		/// Returns true if `who` was removed from `Validators`, otherwise false.
		///
		/// NOTE: you must ALWAYS use this function to remove a validator from the system. Any
		/// access to `Validators` or `VoterList` outside of this function is almost certainly
		/// wrong.
		pub fn do_remove_validator(who: &T::AccountId) -> bool {
			let outcome = if Validators::<T>::contains_key(who) {
				Validators::<T>::remove(who);
				// T::VoterList::on_remove(who);
				true
			} else {
				false
			};

			// debug_assert_eq!(T::VoterList::sanity_check(), Ok(()));
			// debug_assert_eq!(
			// 	Nominators::<T>::count() + Validators::<T>::count(),
			// 	T::VoterList::count()
			// );

			outcome
		}
	}
}
