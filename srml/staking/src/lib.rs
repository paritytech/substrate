// Copyright 2017-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.



// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Staking manager: Periodically determines the best set of validators.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::{prelude::*, cmp};
use parity_codec::HasCompact;
use parity_codec_derive::{Encode, Decode};
use srml_support::{Parameter, StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result};
use srml_support::{decl_module, decl_event, decl_storage, ensure};
use srml_support::traits::{Currency, OnDilution, EnsureAccountLiquid, OnFreeBalanceZero};
use session::OnSessionChange;
use primitives::Perbill;
use primitives::traits::{Zero, One, Bounded, As, StaticLookup};
use system::ensure_signed;

mod mock;

mod tests;

const RECENT_OFFLINE_COUNT: usize = 32;
const DEFAULT_MINIMUM_VALIDATOR_COUNT: u32 = 4;
const MAX_NOMINATIONS = 16;

#[derive(PartialEq, Clone)]
#[cfg_attr(test, derive(Debug))]
pub enum LockStatus<BlockNumber: Parameter> {
	Liquid,
	LockedUntil(BlockNumber),
	Bonded,
}

#[derive(PartialEq, Eq, Copy, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Payee {
	/// Pay into the stash account, increasing the amount at stake accordingly.
	Stash,
	/// Pay into the controller account.
	Controller,
}

impl Default for Payee {
	fn default() -> Self {
		Payee::Stash
	}
}

/// Preference of what happens on a slash event.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidatorPrefs<Balance: HasCompact> {
	/// Validator should ensure this many more slashes than is necessary before being unstaked.
	#[codec(compact)]
	pub unstake_threshold: u32,
	/// Reward that validator takes up-front; only the rest is split between themselves and nominators.
	#[codec(compact)]
	pub validator_payment: Balance,
	/// Should reward be paid into the stash or the controller account?
	pub payee: Payee,
}

impl<B: Default + HasCompact + Copy> Default for ValidatorPrefs<B> {
	fn default() -> Self {
		ValidatorPrefs {
			unstake_threshold: 3,
			validator_payment: Default::default(),
			payee: Default::default(),
		}
	}
}

/// The ledger of a (bonded) stash.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct StakingLedger<AccountId, Balance, BlockNumber> {
	/// The stash account whose balance is actually locked and at stake.
	pub stash: AccountId,
	/// The total amount of the stash's balance that will be at stake in any forthcoming
	/// rounds.
	pub active: Balance,
	/// Any balance that is becoming (or has become) free, which may be transferred out
	/// of the stash.
	pub inactive: Vec<(Balance, BlockNumber)>,
}

/// A snapshot of the stake backing a single validator in the system.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Exposure<AccountId, Balance> {
	/// The total balance backing this validator.
	pub total: Balance,
	/// The validator's own stash that is exposed.
	pub own: Balance,
	/// The portions of nominators stashes that are exposed.
	pub others: Vec<(AccountId, Balance)>,
}

/// Capacity in which a bonded account is participating.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Capacity<AccountId> {
	/// Do nothing.
	Idle,
	/// We are nominating.
	Nominator(Vec<AccountId>),
	/// We want to be a validator.
	Validator,
}

impl<AccountId> Default for Capacity<AccountId> {
	fn default() -> Self {
		Capacity::Nominator(vec![])
	}
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait: system::Trait + session::Trait {
	/// The staking balance.
	type Currency: Currency<Self::AccountId>;

	/// Some tokens minted.
	type OnRewardMinted: OnDilution<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Staking {

		/// The ideal number of staking participants.
		pub ValidatorCount get(validator_count) config(): u32;
		/// Minimum number of staking participants before emergency conditions are imposed.
		pub MinimumValidatorCount get(minimum_validator_count) config(): u32 = DEFAULT_MINIMUM_VALIDATOR_COUNT;
		/// The length of a staking era in sessions.
		pub SessionsPerEra get(sessions_per_era) config(): T::BlockNumber = T::BlockNumber::sa(1000);
		/// Maximum reward, per validator, that is provided per acceptable session.
		pub SessionReward get(session_reward) config(): Perbill = Perbill::from_billionths(60);
		/// Slash, per validator that is taken for the first time they are found to be offline.
		pub OfflineSlash get(offline_slash) config(): Perbill = Perbill::from_millionths(1000); // Perbill::from_fraction() is only for std, so use from_millionths().
		/// Number of instances of offline reports before slashing begins for validators.
		pub OfflineSlashGrace get(offline_slash_grace) config(): u32;
		/// The length of the bonding duration in blocks.
		pub BondingDuration get(bonding_duration) config(): T::BlockNumber = T::BlockNumber::sa(1000);

		// TODO: remove once Alex/CC updated #1785
		pub Invulerables get(invulerables) config(): Vec<T::AccountId>;

		/// Any validators that may never be slashed or forcibly kicked. It's a Vec since they're easy to initialise
		/// and the performance hit is minimal (we expect no more than four invulnerables) and restricted to testnets.
		pub Invulnerables get(invulnerables) config(): Vec<T::AccountId>;

		/// Map from all locked "stash" accounts to the controller account.
		pub Bonded get(bonded): map T::AccountId => Option<T::AccountId>;
		/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
		pub Ledger get(ledger): map T::AccountId => Option<StakingLedger<T::AccountId, BalanceOf<T>, T::BlockNumber>>;

		/// Preferences that a validator has.
		pub ValidatorPreferences get(validator_preferences): map T::AccountId => ValidatorPrefs<BalanceOf<T>>;

		//==============================================================================================================================

		// The desired capacity in which a controller wants to operate.
		pub Desired get(desired): linked_map AccountId => Capacity<T::AccountId>;

		/// Nominators for a particular account that is in action right now. You can't iterate through validators here,
		/// but you can find them in the `sessions` module.
		pub Stakers get(stakers): map T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		// The historical validators and their nominations for a given era. Stored as a hash of the encoded
		// `(T::AccountId, Vec<(T::AccountId, BalanceOf<T>)>)`, which is the key and value of the `CurrentNominatorsFor`,
		// under a key that is the tuple of `era` and `validator index`.
		// 
		// Every era change, this will be appended with the contents of `CurrentNominatorsFor`, and the oldest entry removed down to
		// a specific number of entries (probably around 90 for a 3 month history). To remove all items for era N, just start at
		// validator index 0: (N, 0) and remove the item, incrementing the index until it's a `None`.
//		pub HistoricalStakers get(historical_stakers): map (T::BlockNumber, u32) => Option<H256>;

		//==============================================================================================================================

		/// The current era index.
		pub CurrentEra get(current_era) config(): T::BlockNumber;

		/// Maximum reward, per validator, that is provided per acceptable session.
		pub CurrentSessionReward get(current_session_reward) config(): BalanceOf<T>;
		/// Slash, per validator that is taken for the first time they are found to be offline.
		pub CurrentOfflineSlash get(current_offline_slash) config(): BalanceOf<T>;

		/// The accumulated reward for the current era. Reset to zero at the beginning of the era and
		/// increased for every successfully finished session.
		pub CurrentEraReward get(current_era_reward) config(): BalanceOf<T>;

		/// The next value of sessions per era.
		pub NextSessionsPerEra get(next_sessions_per_era): Option<T::BlockNumber>;
		/// The session index at which the era length last changed.
		pub LastEraLengthChange get(last_era_length_change): T::BlockNumber;

		/// The highest and lowest staked validator slashable balances.
		pub SlotStake get(slot_range): BalanceOf<T>;

		/// The number of times a given validator has been reported offline. This gets decremented by one each era that passes.
		pub SlashCount get(slash_count): map T::AccountId => u32;

		/// We are forcing a new era.
		pub ForcingNewEra get(forcing_new_era): Option<()>;

		/// Most recent `RECENT_OFFLINE_COUNT` instances. (who it was, when it was reported, how many instances they were offline for).
		pub RecentlyOffline get(recently_offline): Vec<(T::AccountId, T::BlockNumber, u32)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will be the
		/// account that controls it.
		fn bond_stash(origin, controller: <T::Lookup as StaticLookup>::Source, #[compact] value: BalanceOf<T>) {
			let stash = ensure_signed(origin)?;

			if Self::bond(&stash).is_some() {
				return Err("stash already bonded")
			}

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate.
			<Bonded<T>>::insert(&stash, controller.clone());

			let stash_balance = <balances::Module<T>>::free_balance(&stash);
			let value = value.min(stash_balance);
			let remaining_free = stash_balance - value;
			let inactive = match remaining_free.is_zero() {
				false => vec![(remaining_free, <system::Module<T>>::block_number())],
				true => vec![],
			};

			<Ledger<T>>::insert(&T::Lookup::lookup(controller), StakingLedger { stash, active: value, inactive });
		}

		/// Schedule a portion of the stash to be unlocked ready for transfer out after the bond
		/// period ends. If this leaves an amount actively bonded less than 
		/// <balances::Module<T>>::existential_deposit(), then it is increased to the full amount.
		fn unlock(origin, #[compact] value: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;

			let mut value = value.min(ledger.active);

			if !value.is_zero() {
				ledger.active -= value;

				/// Avoid there being a dust balance left in the staking system.
				let ed = <balances::Module<T>>::existential_deposit();
				if ledger.active - value < ed {
					value += ledger.active;
					ledger.active = Zero::zero();
				}

				let now = <system::Module<T>>::block_number();
				ledger.inactive.push((value, now + Self::bonding_duration()));
				<Ledger<T>>::insert(&controller, ledger);
			}
		}

		/// Transfer some `value` of unlocked funds from the stash to `destination` account.
		fn transfer_unlocked(origin, destination: <T::Lookup as StaticLookup>::Source) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;

			let now = <system::Module<T>>::block_number();

			let mut total = Zero::zero();
			l.inactive = l.inactive.iter()
				.filter(|(how_much, when)| if now < when {
					true
				} else {
					total += how_much;
					false
				})
				.collect();

			<balances::Module<T>>::decrease_free_balance(&l.stash, total)?;
			<balances::Module<T>>::increase_free_balance_creating(&T::Lookup::lookup(destination), total);
			<Ledger<T>>::insert(&controller, ledger);
		}

		/// Add any extra amounts that have appeared in the stash free_balance into the balance up for
		/// staking.
		fn note_additional(origin) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;

			let stash_balance = <balances::Module<T>>::free_balance(&stash);
			let inactive_balance = ledger.inactive.iter().map(|(v, _)| v).sum();

			if stash_balance > inactive_balance + ledger.active {
				let extra = stash_balance - inactive_balance - ledger.active;
				let now = <system::Module<T>>::block_number();
				ledger.inactive.push((extra, now));
				<Ledger<T>>::insert(&controller, ledger);
			}
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		fn validate(origin) {
			let controller = ensure_signed(origin)?;
			let mut _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			Desired<T>::insert(controller, Capacity::Validator);
		}

		/// Declare the desire to nominate `targets` for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		fn nominate(origin, targets: Vec<<T::Lookup as StaticLookup>::Source>) {
			let controller = ensure_signed(origin)?;
			let mut _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let targets = target.into_iter()
				.take(MAX_NOMINATIONS)
				.map(T::Lookup::lookup)
				.collect::<Result<Vec<T::AccountId>, &'static str>>()?;

			Desired<T>::insert(controller, Capacity::Nominator(targets));
		}

		/// Declare no desire to either validate or nominate.
		///
		/// Effects will be felt at the beginning of the next era.
		fn chill(origin) {
			let controller = ensure_signed(origin)?;
			let mut _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			Desired<T>::insert(controller, Capacity::Idle);
		}

		/// Set the given account's preference for slashing behaviour should they be a validator.
		///
		/// An error (no-op) if `Self::intentions()[intentions_index] != origin`.
		fn register_preferences(
			origin,
			#[compact] intentions_index: u32,
			prefs: ValidatorPrefs<BalanceOf<T>>
		) {
			let controller = ensure_signed(origin)?;
			let mut _ledger = Self::ledger(&controller).ok_or("not a controller")?;

			<ValidatorPreferences<T>>::insert(controller, prefs);
		}

		/// Set the number of sessions in an era.
		fn set_sessions_per_era(#[compact] new: T::BlockNumber) {
			<NextSessionsPerEra<T>>::put(new);
		}

		/// The length of the bonding duration in eras.
		fn set_bonding_duration(#[compact] new: T::BlockNumber) {
			<BondingDuration<T>>::put(new);
		}

		/// The ideal number of validators.
		fn set_validator_count(#[compact] new: u32) {
			<ValidatorCount<T>>::put(new);
		}

		/// Force there to be a new era. This also forces a new session immediately after.
		/// `apply_rewards` should be true for validators to get the session reward.
		fn force_new_era(apply_rewards: bool) -> Result {
			Self::apply_force_new_era(apply_rewards)
		}

		/// Set the offline slash grace period.
		fn set_offline_slash_grace(#[compact] new: u32) {
			<OfflineSlashGrace<T>>::put(new);
		}

		/// Set the validators who cannot be slashed (if any).
		fn set_invulnerables(validators: Vec<T::AccountId>) {
			<Invulnerables<T>>::put(validators);
		}
	}
}

/// An event in this module.
decl_event!(
	pub enum Event<T> where Balance = BalanceOf<T>, <T as system::Trait>::AccountId {
		/// All validators have been rewarded by the given balance.
		Reward(Balance),
		/// One validator (and their nominators) has been given a offline-warning (they're still
		/// within their grace). The accrued number of slashes is recorded, too.
		OfflineWarning(AccountId, u32),
		/// One validator (and their nominators) has been slashed by the given amount.
		OfflineSlash(AccountId, Balance),
	}
);

impl<T: Trait> Module<T> {
	// Just force_new_era without origin check.
	fn apply_force_new_era(apply_rewards: bool) -> Result {
		<ForcingNewEra<T>>::put(());
		<session::Module<T>>::apply_force_new_session(apply_rewards)
	}

	// PUBLIC IMMUTABLES

	/// The length of a staking era in blocks.
	pub fn era_length() -> T::BlockNumber {
		Self::sessions_per_era() * <session::Module<T>>::length()
	}

	/// Balance of a (potential) validator that includes all nominators.
	pub fn nomination_balance(who: &T::AccountId) -> BalanceOf<T> {
		Self::nominators_for(who).iter()
			.map(T::Currency::total_balance)
			.fold(Zero::zero(), |acc, x| acc + x)
	}

	/// The stashed funds whose staking activities are controlled by `controller` and
	/// which are actively in stake right now.
	pub fn stash_balance(controller: &T::AccountId) -> BalanceOf<T> {
		Self::ledger(controller)
			.map_or_else(Zero::zero, |l| l.active)
	}

	/// The total balance that can be slashed from a validator controller account as of
	/// right now.
	pub fn slashable_balance(who: &T::AccountId) -> BalanceOf<T> {
		Self::stakers(who).total
	}

	/// Get the current validators.
	pub fn validators() -> Vec<T::AccountId> {
		session::Module::<T>::validators()
	}

	// PUBLIC MUTABLES (DANGEROUS)
	
	// TODO: switch out `backing_balance` for `Stakers`.

	/// Slash a given validator by a specific amount. Removes the slash from their balance by preference,
	/// and reduces the nominators' balance if needed.
	fn slash_validator(v: &T::AccountId, slash: BalanceOf<T>) {
		// The exposure (backing stake) information of the validator to be slashed.
		let exposure = Self::stakers(v);
		// The amount we are actually going to slash (can't be bigger than thair total exposure)
		let slash = slash.min(exposure.total);
		// The amount we'll slash from the validator's stash directly.
		let own_slash = exposure.own.min(slash);
		let own_slash = own_slash - T::Currency::slash(v, own_slash).unwrap_or_default();
		// The amount remaining that we can't slash from the validator, that must be taken from the nominators.
		let rest_slash = slash - own_slash;

		if !rest.is_zero() {
			// The total to be slashed from the nominators.
			let total = exposure.total - exposure.own;
			if !total.is_zero() {
				let safe_mul_rational = |b| b * rest / total;// FIXME #1572 avoid overflow
				for (them, their_exposure) in exposure.others.iter() {
					let _ = T::Currency::slash(them, safe_mul_rational(their_exposure));	// best effort - not much that can be done on fail.
				}
			}
		}
	}

	/// Reward a given validator by a specific amount. Add the reward to their, and their nominators'
	/// balance, pro-rata based on their exposure, after having removed the validator's pre-payout cut.
	fn reward_validator(who: &T::AccountId, reward: BalanceOf<T>) {
		let off_the_table = reward.min(Self::validator_preferences(who).validator_payment);
		let reward = reward - off_the_table;
		let validator_cut = if reward.is_zero() {
			Zero::zero()
		} else {
			let exposure = Self::stakers(who);
			let total = exposure.total.max(One::one());
			let safe_mul_rational = |b| b * reward / total;// FIXME #1572:  avoid overflow
			for (them, their_exposure) in exposure.others.iter() {
				let _ = T::Currency::reward(them, safe_mul_rational(their_exposure));
			}
			safe_mul_rational(exposure.own)
		};
		let _ = T::Currency::reward(who, validator_cut + off_the_table);
	}

	/// Actually carry out the unvalidate operation.
	/// Assumes `intentions()[intentions_index] == who`.
	fn apply_unvalidate(who: &T::AccountId) {
		<Desired<T>>::insert(who, Capacity::Idle);
	}

	/// Get the reward for the session, assuming it ends with this block.
	fn this_session_reward(actual_elapsed: T::Moment) -> BalanceOf<T> {
		let ideal_elapsed = <session::Module<T>>::ideal_session_duration();
		if ideal_elapsed.is_zero() {
			return Self::current_session_reward();
		}
		let per65536: u64 = (T::Moment::sa(65536u64) * ideal_elapsed.clone() / actual_elapsed.max(ideal_elapsed)).as_();
		Self::current_session_reward() * BalanceOf::<T>::sa(per65536) / BalanceOf::<T>::sa(65536u64)
	}

	/// Session has just changed. We need to determine whether we pay a reward, slash and/or
	/// move to a new era.
	fn new_session(actual_elapsed: T::Moment, should_reward: bool) {
		if should_reward {
			// accumulate good session reward
			let reward = Self::this_session_reward(actual_elapsed);
			<CurrentEraReward<T>>::mutate(|r| r += reward);
		}

		let session_index = <session::Module<T>>::current_index();
		if <ForcingNewEra<T>>::take().is_some()
			|| ((session_index - Self::last_era_length_change()) % Self::sessions_per_era()).is_zero()
		{
			Self::new_era();
		}
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens immediately before a session change to ensure that new validators
	/// get a chance to set their session keys.
	fn new_era() {
		// Payout
		let reward = <CurrentEraReward<T>>::take();
		if !reward.is_zero() {
			let validators = <session::Module<T>>::validators();
			for v in validators.iter() {
				Self::reward_validator(v, reward);
			}
			Self::deposit_event(RawEvent::Reward(reward));
			let total_minted = reward * <BalanceOf<T> as As<usize>>::sa(validators.len());
			let total_rewarded_stake = Self::slot_stake() * <BalanceOf<T> as As<usize>>::sa(validators.len());
			T::OnRewardMinted::on_dilution(total_minted, total_rewarded_stake);
		}

		// Increment current era.
		<CurrentEra<T>>::put(&(<CurrentEra<T>>::get() + One::one()));

		// Enact era length change.
		if let Some(next_spe) = Self::next_sessions_per_era() {
			if next_spe != Self::sessions_per_era() {
				<SessionsPerEra<T>>::put(&next_spe);
				<LastEraLengthChange<T>>::put(&<session::Module<T>>::current_index());
			}
		}

		// Reassign all Stakers.

		// TODO: Can probably pre-process a lot of complexity out of these two for-loops,
		// particularly the need to keep everything in a BTreeMap.

		// Map of (would-be) validator account to amount of stake backing it.
		let mut candidates: Vec<(T::AccountId, Exposure)> = Default::default();
		for (who, capacity) in <Desired<T>>::enumerate() {
			match capacity {
				Validator => {
					let stash_balance = Self::stash_balance(&who);
					candidates.push((who, Exposure { total: stash_balance, own: stash_balance, others: vec![] }));
				}
				_ => {}
			}
		}
		canidates.sort_unstable_by_key(|i| &i.0);
		for (who, capacity) in <Desired<T>>::enumerate() {
			match capacity {
				Nominator(nominees) => {
					// For this trivial nominator mapping, we just assume that nominators always
					// have themselves assigned to the first validator in their list.
					let chosen = if nominees.len() > 0 {
						candidates[0]
					} else {
						continue
					};
					if let Ok(index) = candidates.binary_search_by_key(&who, |i| &i.0) {
						let stash_balance = Self::stash_balance(&who);
						candidates[index].1.total += stash_balance;
						candidates[index].1.others.push((who, stash_balance));
					}
				}
				_ => {}
			}
		}

		// Clear Stakers.
		for v in <session::Module<T>>::validators().iter() {
			<Stakers<T>>::remove(v);
			let slash_count = <SlashCount<T>>::take(v);
			if slash_count > 1 {
				<SlashCount<T>>::insert(v, slash_count - 1);
			}
		}

		candidates.sort_unstable_by(|(a, b)| a.1.total > b.1.total);
		candidates.truncate(Self::validator_count() as usize);

		let slot_stake = candidates.last().map(|i| i.1.total).unwrap_or_default();
		<SlotStake<T>>::put(&slot_stake);

		for (who, exposure) in &candidates {
			<Stakers<T>>::insert(who, exposure);
		}
		<session::Module<T>>::set_validators(
			candidates.into_iter().map(|i| i.0).collect::<Vec<_>>()
		);

		// Update the balances for slashing/rewarding according to the stakes.
		<CurrentOfflineSlash<T>>::put(Self::offline_slash() * slot_stake);
		<CurrentSessionReward<T>>::put(Self::session_reward() * slot_stake);
	}

	/// Call when a validator is determined to be offline. `count` is the
	/// number of offences the validator has committed.
	pub fn on_offline_validator(v: T::AccountId, count: usize) {
		use primitives::traits::{CheckedAdd, CheckedShl};

		// Early exit if validator is invulnerable.
		if Self::invulnerables().contains(&v) {
			return
		}
		// TODO: remove once Alex/CC updated #1785
		if Self::invulerables().contains(&v) {
			return
		}

		let slash_count = Self::slash_count(&v);
		let new_slash_count = slash_count + count as u32;
		<SlashCount<T>>::insert(&v, new_slash_count);
		let grace = Self::offline_slash_grace();

		if RECENT_OFFLINE_COUNT > 0 {
			let item = (v.clone(), <system::Module<T>>::block_number(), count as u32);
			<RecentlyOffline<T>>::mutate(|v| if v.len() >= RECENT_OFFLINE_COUNT {
				let index = v.iter()
					.enumerate()
					.min_by_key(|(_, (_, block, _))| block)
					.expect("v is non-empty; qed")
					.0;
				v[index] = item;
			} else {
				v.push(item);
			});
		}

		let event = if new_slash_count > grace {
			let slash = {
				let base_slash = Self::current_offline_slash();
				let instances = slash_count - grace;

				let mut total_slash = BalanceOf::<T>::default();
				for i in instances..(instances + count as u32) {
					if let Some(total) = base_slash.checked_shl(i)
							.and_then(|slash| total_slash.checked_add(&slash)) {
						total_slash = total;
					} else {
						// reset slash count only up to the current
						// instance. the total slash overflows the unit for
						// balance in the system therefore we can slash all
						// the slashable balance for the account
						<SlashCount<T>>::insert(v.clone(), slash_count + i);
						total_slash = Self::slashable_balance(&v);
						break;
					}
				}

				total_slash
			};

			let _ = Self::slash_validator(&v, slash);

			let next_slash = match slash.checked_shl(1) {
				Some(slash) => slash,
				None => Self::slashable_balance(&v),
			};

			let instances = new_slash_count - grace;
			if instances > Self::validator_preferences(&v).unstake_threshold
				|| Self::slashable_balance(&v) < next_slash
				|| next_slash <= slash
			{
				if let Some(pos) = Self::intentions().into_iter().position(|x| &x == &v) {
					Self::apply_unvalidate(&v, pos)
						.expect("pos derived correctly from Self::intentions(); \
								 apply_unvalidate can only fail if pos wrong; \
								 Self::intentions() doesn't change; qed");
				}
				let _ = Self::apply_force_new_era(false);
			}
			RawEvent::OfflineSlash(v.clone(), slash)
		} else {
			RawEvent::OfflineWarning(v.clone(), slash_count)
		};

		Self::deposit_event(event);
	}
}

impl<T: Trait> OnSessionChange<T::Moment> for Module<T> {
	fn on_session_change(elapsed: T::Moment, should_reward: bool) {
		Self::new_session(elapsed, should_reward);
	}
}

impl<T: Trait> EnsureAccountLiquid<T::AccountId> for Module<T> {
	fn ensure_account_can_transfer(who: &T::AccountId) -> Result {
		if <Bonded<T>>::exists(who) {
			Err("stash accounts are frozen")
		} else {
			Ok(())
		}
	}

	fn ensure_account_can_pay(who: &T::AccountId) -> Result {
		Self::ensure_account_can_transfer(who)
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		if let Some(controller) = <Bonded<T>>::take(who) {
			<Ledger<T>>::kill(&controller);
			<ValidatorPreferences<T>>::remove(&controller);
			<SlashCount<T>>::remove(&controller);
			<Desired<T>>::remove(&controller);
		}
	}
}

impl<T: Trait> consensus::OnOfflineReport<Vec<u32>> for Module<T> {
	fn handle_report(reported_indices: Vec<u32>) {
		for validator_index in reported_indices {
			let v = <session::Module<T>>::validators()[validator_index as usize].clone();
			Self::on_offline_validator(v, 1);
		}
	}
}
