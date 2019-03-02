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

use rstd::{prelude::*, result};
use parity_codec::HasCompact;
use parity_codec_derive::{Encode, Decode};
use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result};
use srml_support::{decl_module, decl_event, decl_storage, ensure};
use srml_support::traits::{
	Currency, OnDilution, EnsureAccountLiquid, OnFreeBalanceZero, WithdrawReason, ArithmeticType
};
use session::OnSessionChange;
use primitives::Perbill;
use primitives::traits::{Zero, One, As, StaticLookup, Saturating};
use system::ensure_signed;

mod mock;

mod tests;

const RECENT_OFFLINE_COUNT: usize = 32;
const DEFAULT_MINIMUM_VALIDATOR_COUNT: u32 = 4;
const MAX_NOMINATIONS: usize = 16;
const MAX_UNSTAKE_THRESHOLD: u32 = 10;

/// A destination account for payment.
#[derive(PartialEq, Eq, Copy, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum RewardDestination {
	/// Pay into the stash account, increasing the amount at stake accordingly.
	Staked,
	/// Pay into the stash account, not increasing the amount at stake.
	Stash,
	/// Pay into the controller account.
	Controller,
}

impl Default for RewardDestination {
	fn default() -> Self {
		RewardDestination::Staked
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
}

impl<B: Default + HasCompact + Copy> Default for ValidatorPrefs<B> {
	fn default() -> Self {
		ValidatorPrefs {
			unstake_threshold: 3,
			validator_payment: Default::default(),
		}
	}
}

/// Just a Balance/BlockNumber tuple to encode when a chunk of funds will be unlocked.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct UnlockChunk<Balance: HasCompact, BlockNumber: HasCompact> {
	/// Amount of funds to be unlocked.
	#[codec(compact)]
	value: Balance,
	/// Era number at which point it'll be unlocked.
	#[codec(compact)]
	era: BlockNumber,
}

/// The ledger of a (bonded) stash.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct StakingLedger<AccountId, Balance: HasCompact, BlockNumber: HasCompact> {
	/// The stash account whose balance is actually locked and at stake.
	pub stash: AccountId,
	/// The total amount of the stash's balance that we are currently accounting for.
	/// It's just `active` plus all the `unlocking` balances.
	#[codec(compact)]
	pub total: Balance,
	/// The total amount of the stash's balance that will be at stake in any forthcoming
	/// rounds.
	#[codec(compact)]
	pub active: Balance,
	/// Any balance that is becoming free, which may eventually be transferred out
	/// of the stash (assuming it doesn't get slashed first).
	pub unlocking: Vec<UnlockChunk<Balance, BlockNumber>>,
}

impl<AccountId, Balance: HasCompact + Copy + Saturating, BlockNumber: HasCompact + PartialOrd> StakingLedger<AccountId, Balance, BlockNumber> {
	/// Remove entries from `unlocking` that are sufficiently old and reduce the
	/// total by the sum of their balances.
	fn consolidate_unlocked(self, current_era: BlockNumber) -> Self {
		let mut total = self.total;
		let unlocking = self.unlocking.into_iter()
			.filter(|chunk| if chunk.era > current_era {
				true
			} else {
				total = total.saturating_sub(chunk.value);
				false
			})
			.collect();
		Self { total, active: self.active, stash: self.stash, unlocking }
	}
}

/// The amount of exposure (to slashing) than an individual nominator has.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct IndividualExposure<AccountId, Balance: HasCompact> {
	/// Which nominator.
	who: AccountId,
	/// Amount of funds exposed.
	#[codec(compact)]
	value: Balance,
}

/// A snapshot of the stake backing a single validator in the system.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Exposure<AccountId, Balance: HasCompact> {
	/// The total balance backing this validator.
	#[codec(compact)]
	pub total: Balance,
	/// The validator's own stash that is exposed.
	#[codec(compact)]
	pub own: Balance,
	/// The portions of nominators stashes that are exposed.
	pub others: Vec<IndividualExposure<AccountId, Balance>>,
}

type BalanceOf<T> = <<T as Trait>::Currency as ArithmeticType>::Type;

pub trait Trait: system::Trait + session::Trait {
	/// The staking balance.
	type Currency: ArithmeticType + Currency<Self::AccountId, Balance=BalanceOf<Self>>;

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
		pub Invulerables get(invulerables): Vec<T::AccountId>;

		/// Any validators that may never be slashed or forcibly kicked. It's a Vec since they're easy to initialise
		/// and the performance hit is minimal (we expect no more than four invulnerables) and restricted to testnets.
		pub Invulnerables get(invulnerables) config(): Vec<T::AccountId>;

		/// Map from all locked "stash" accounts to the controller account.
		pub Bonded get(bonded) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|(stash, controller, _)| (stash.clone(), controller.clone())).collect::<Vec<_>>()
		}): map T::AccountId => Option<T::AccountId>;
		/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
		pub Ledger get(ledger) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|(stash, controller, value)| (
				controller.clone(),
				StakingLedger {
					stash: stash.clone(),
					total: *value,
					active: *value,
					unlocking: Vec::<UnlockChunk<BalanceOf<T>, T::BlockNumber>>::new(),
				},
			)).collect::<Vec<_>>()
		}): map T::AccountId => Option<StakingLedger<T::AccountId, BalanceOf<T>, T::BlockNumber>>;

		/// Where the reward payment should be made.
		pub Payee get(payee): map T::AccountId => RewardDestination;

		/// The set of keys are all controllers that want to validate.
		/// 
		/// The values are the preferences that a validator has.
		pub Validators get(validators) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|(_stash, controller, _value)| (
				controller.clone(),
				ValidatorPrefs::<BalanceOf<T>>::default(),
			)).collect::<Vec<_>>()
		}): linked_map T::AccountId => ValidatorPrefs<BalanceOf<T>>;

		/// The set of keys are all controllers that want to nominate.
		/// 
		/// The value are the nominations.
		pub Nominators get(nominators): linked_map T::AccountId => Vec<T::AccountId>;

		/// Nominators for a particular account that is in action right now. You can't iterate through validators here,
		/// but you can find them in the `sessions` module.
		pub Stakers get(stakers) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|(_stash, controller, value)| (
				controller.clone(),
				Exposure {
					total: *value,
					own: *value,
					others: Vec::<IndividualExposure<T::AccountId, _>>::new(),
				},
			)).collect::<Vec<_>>()
		}): map T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		// The historical validators and their nominations for a given era. Stored as a trie root of the mapping
		// `T::AccountId` => `Exposure<T::AccountId, BalanceOf<T>>`, which is just the contents of `Stakers`,
		// under a key that is the `era`.
		// 
		// Every era change, this will be appended with the trie root of the contents of `Stakers`, and the oldest
		// entry removed down to a specific number of entries (probably around 90 for a 3 month history).
//		pub HistoricalStakers get(historical_stakers): map T::BlockNumber => Option<H256>;

		/// The current era index.
		pub CurrentEra get(current_era) config(): T::BlockNumber;

		/// Maximum reward, per validator, that is provided per acceptable session.
		pub CurrentSessionReward get(current_session_reward) config(): BalanceOf<T>;
		/// Slash, per validator that is taken for the first time they are found to be offline.
		pub CurrentOfflineSlash get(current_offline_slash) config(): BalanceOf<T>;

		/// The accumulated reward for the current era. Reset to zero at the beginning of the era and
		/// increased for every successfully finished session.
		pub CurrentEraReward get(current_era_reward): BalanceOf<T>;

		/// The next value of sessions per era.
		pub NextSessionsPerEra get(next_sessions_per_era): Option<T::BlockNumber>;
		/// The session index at which the era length last changed.
		pub LastEraLengthChange get(last_era_length_change): T::BlockNumber;

		/// The amount of balance actively at stake for each validator slot, currently.
		///
		/// This is used to derive rewards and punishments.
		pub SlotStake get(slot_stake) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|&(_, _, value)| value).min().unwrap_or_default()
		}): BalanceOf<T>;

		/// The number of times a given validator has been reported offline. This gets decremented by one each era that passes.
		pub SlashCount get(slash_count): map T::AccountId => u32;

		/// We are forcing a new era.
		pub ForcingNewEra get(forcing_new_era): Option<()>;

		/// Most recent `RECENT_OFFLINE_COUNT` instances. (who it was, when it was reported, how many instances they were offline for).
		pub RecentlyOffline get(recently_offline): Vec<(T::AccountId, T::BlockNumber, u32)>;
	}
	add_extra_genesis {
		config(stakers): Vec<(T::AccountId, T::AccountId, BalanceOf<T>)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will be the
		/// account that controls it.
		fn bond(origin, controller: <T::Lookup as StaticLookup>::Source, #[compact] value: BalanceOf<T>, payee: RewardDestination) {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::exists(&stash) {
				return Err("stash already bonded")
			}

			let controller = T::Lookup::lookup(controller)?;

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate.
			<Bonded<T>>::insert(&stash, controller.clone());

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);

			<Ledger<T>>::insert(&controller, StakingLedger { stash, total: value, active: value, unlocking: vec![] });
			<Payee<T>>::insert(&controller, payee);
		}

		/// Add some extra amount that have appeared in the stash `free_balance` into the balance up for
		/// staking.
		/// 
		/// Use this if there are additional funds in your stash account that you wish to bond.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		fn bond_extra(origin, max_additional: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash_balance = T::Currency::free_balance(&ledger.stash);

			if stash_balance > ledger.total {
				let extra = (stash_balance - ledger.total).min(max_additional);
				ledger.total += extra;
				ledger.active += extra;
				<Ledger<T>>::insert(&controller, ledger);
			}
		}

		/// Schedule a portion of the stash to be unlocked ready for transfer out after the bond
		/// period ends. If this leaves an amount actively bonded less than 
		/// T::Currency::existential_deposit(), then it is increased to the full amount.
		/// 
		/// Once the unlock period is done, you can call `withdraw_unbonded` to actually move
		/// the funds out of management ready for transfer. 
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		/// 
		/// See also `withdraw_unbonded`.
		fn unbond(origin, #[compact] value: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;

			let mut value = value.min(ledger.active);

			if !value.is_zero() {
				ledger.active -= value;

				// Avoid there being a dust balance left in the staking system.
				let ed = T::Currency::minimum_balance();
				if ledger.active < ed {
					value += ledger.active;
					ledger.active = Zero::zero();
				}

				let era = Self::current_era() + Self::bonding_duration();
				ledger.unlocking.push(UnlockChunk { value, era });
				<Ledger<T>>::insert(&controller, ledger);
			}
		}

		/// Remove any unlocked chunks from the `unlocking` queue from our management.
		/// 
		/// This essentially frees up that balance to be used by the stash account to do
		/// whatever it wants.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		/// 
		/// See also `unbond`.
		fn withdraw_unbonded(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			<Ledger<T>>::insert(&controller, ledger.consolidate_unlocked(Self::current_era()));
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		fn validate(origin, prefs: ValidatorPrefs<BalanceOf<T>>) {
			let controller = ensure_signed(origin)?;
			let _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			ensure!(prefs.unstake_threshold <= MAX_UNSTAKE_THRESHOLD, "unstake threshold too large");
			<Nominators<T>>::remove(&controller);
			<Validators<T>>::insert(controller, prefs);
		}

		/// Declare the desire to nominate `targets` for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		fn nominate(origin, targets: Vec<<T::Lookup as StaticLookup>::Source>) {
			let controller = ensure_signed(origin)?;
			let _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			ensure!(!targets.is_empty(), "targets cannot be empty");
			let targets = targets.into_iter()
				.take(MAX_NOMINATIONS)
				.map(T::Lookup::lookup)
				.collect::<result::Result<Vec<T::AccountId>, &'static str>>()?;

			<Validators<T>>::remove(&controller);
			<Nominators<T>>::insert(controller, targets);
		}

		/// Declare no desire to either validate or nominate.
		///
		/// Effects will be felt at the beginning of the next era.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		fn chill(origin) {
			let controller = ensure_signed(origin)?;
			let _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			<Validators<T>>::remove(&controller);
			<Nominators<T>>::remove(&controller);
		}

		/// (Re-)set the payment target for a controller.
		///
		/// Effects will be felt at the beginning of the next era.
		/// 
		/// NOTE: This call must be made by the controller, not the stash.
		fn set_payee(origin, payee: RewardDestination) {
			let controller = ensure_signed(origin)?;
			let _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			<Payee<T>>::insert(&controller, payee);
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

	// PUBLIC MUTABLES (DANGEROUS)
	
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

		if !rest_slash.is_zero() {
			// The total to be slashed from the nominators.
			let total = exposure.total - exposure.own;
			if !total.is_zero() {
				let safe_mul_rational = |b| b * rest_slash / total;// FIXME #1572 avoid overflow
				for i in exposure.others.iter() {
					let _ = T::Currency::slash(&i.who, safe_mul_rational(i.value));	// best effort - not much that can be done on fail.
				}
			}
		}
	}

	/// Actually make a payment to a staker. This uses the currency's reward function
	/// to pay the right payee for the given staker account.
	fn make_payout(who: &T::AccountId, amount: BalanceOf<T>) {
		match Self::payee(who) {
			RewardDestination::Controller => {
				let _ = T::Currency::reward(&who, amount);
			}
			RewardDestination::Stash => {
				let _ = Self::ledger(who).map(|l| T::Currency::reward(&l.stash, amount));
			}
			RewardDestination::Staked => <Ledger<T>>::mutate(who, |ml| {
				if let Some(l) = ml.as_mut() {
					l.active += amount;
					l.total += amount;
					let _ = T::Currency::reward(&l.stash, amount);
				}
			}),
		}		
	}

	/// Reward a given validator by a specific amount. Add the reward to their, and their nominators'
	/// balance, pro-rata based on their exposure, after having removed the validator's pre-payout cut.
	fn reward_validator(who: &T::AccountId, reward: BalanceOf<T>) {
		let off_the_table = reward.min(Self::validators(who).validator_payment);
		let reward = reward - off_the_table;
		let validator_cut = if reward.is_zero() {
			Zero::zero()
		} else {
			let exposure = Self::stakers(who);
			let total = exposure.total.max(One::one());
			let safe_mul_rational = |b| b * reward / total;// FIXME #1572:  avoid overflow
			for i in &exposure.others {
				Self::make_payout(&i.who, safe_mul_rational(i.value));
			}
			safe_mul_rational(exposure.own)
		};
		Self::make_payout(who, validator_cut + off_the_table);
	}

	/// Get the reward for the session, assuming it ends with this block.
	fn this_session_reward(actual_elapsed: T::Moment) -> BalanceOf<T> {
		let ideal_elapsed = <session::Module<T>>::ideal_session_duration();
		if ideal_elapsed.is_zero() {
			return Self::current_session_reward();
		}
		let per65536: u64 = (T::Moment::sa(65536u64) * ideal_elapsed.clone() / actual_elapsed.max(ideal_elapsed)).as_();
		Self::current_session_reward() * <BalanceOf<T>>::sa(per65536) / <BalanceOf<T>>::sa(65536u64)
	}

	/// Session has just changed. We need to determine whether we pay a reward, slash and/or
	/// move to a new era.
	fn new_session(actual_elapsed: T::Moment, should_reward: bool) {
		if should_reward {
			// accumulate good session reward
			let reward = Self::this_session_reward(actual_elapsed);
			<CurrentEraReward<T>>::mutate(|r| *r += reward);
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

		// Map of (would-be) validator account to amount of stake backing it.
		
		// First, we pull all validators, together with their stash balance into a Vec (cpu=O(V), mem=O(V))
		let mut candidates = <Validators<T>>::enumerate()
			.map(|(who, _)| {
				let stash_balance = Self::stash_balance(&who);
				(who, Exposure { total: stash_balance, own: stash_balance, others: vec![] })
			})
			.collect::<Vec<(T::AccountId, Exposure<T::AccountId, BalanceOf<T>>)>>();
		// Second, we sort by accountid (cpu=O(V.log(V)))
		candidates.sort_unstable_by_key(|i| i.0.clone());
		// Third, iterate through nominators and add their balance to the first validator in their approval
		// list. cpu=O(N.log(V))
		for (who, nominees) in <Nominators<T>>::enumerate() {
			// For this trivial nominator mapping, we just assume that nominators always
			// have themselves assigned to the first validator in their list.
			if nominees.is_empty() {
				// Not possible, but we protect against it anyway.
				continue;
			}
			if let Ok(index) = candidates.binary_search_by(|i| i.0.cmp(&nominees[0])) {
				let stash_balance = Self::stash_balance(&who);
				candidates[index].1.total += stash_balance;
				candidates[index].1.others.push(IndividualExposure { who, value: stash_balance });
			}
		}

		// Get the new staker set by sorting by total backing stake and truncating.
		// cpu=O(V.log(s)) average, O(V.s) worst.
		let count = Self::validator_count() as usize;
		let candidates = if candidates.len() <= count {
			candidates
		} else {
			candidates.into_iter().fold(vec![], |mut winners: Vec<(T::AccountId, Exposure<T::AccountId, BalanceOf<T>>)>, entry| {
				if let Err(insert_point) = winners.binary_search_by_key(&entry.1.total, |i| i.1.total) {
					if winners.len() < count {
						winners.insert(insert_point, entry)
					} else {
						if insert_point > 0 {
							// Big enough to be considered: insert at beginning and swap up to relevant point.
							winners[0] = entry;
							for i in 0..(insert_point - 1) {
								winners.swap(i, i + 1)
							}
						}
					}
				}
				winners
			})
		};

		// Clear Stakers and reduce their slash_count.
		for v in <session::Module<T>>::validators().iter() {
			<Stakers<T>>::remove(v);
			let slash_count = <SlashCount<T>>::take(v);
			if slash_count > 1 {
				<SlashCount<T>>::insert(v, slash_count - 1);
			}
		}

		// Figure out the minimum stake behind a slot.
		let slot_stake = candidates.last().map(|i| i.1.total).unwrap_or_default();
		<SlotStake<T>>::put(&slot_stake);

		// Populate Stakers.
		for (who, exposure) in &candidates {
			<Stakers<T>>::insert(who, exposure);
		}
		// Set the new validator set.
		<session::Module<T>>::set_validators(
			&candidates.into_iter().map(|i| i.0).collect::<Vec<_>>()
		);

		// Update the balances for slashing/rewarding according to the stakes.
		<CurrentOfflineSlash<T>>::put(Self::offline_slash() * slot_stake);
		<CurrentSessionReward<T>>::put(Self::session_reward() * slot_stake);
	}

	/// Call when a validator is determined to be offline. `count` is the
	/// number of offences the validator has committed.
	pub fn on_offline_validator(v: T::AccountId, count: usize) {
		use primitives::traits::CheckedShl;

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

		let prefs = Self::validators(&v);
		let unstake_threshold = prefs.unstake_threshold.min(MAX_UNSTAKE_THRESHOLD);
		let max_slashes = grace + unstake_threshold;

		let event = if new_slash_count > max_slashes {
			let slot_stake = Self::slot_stake();
			// They're bailing.
			let slash = Self::current_offline_slash()
				// Multiply current_offline_slash by 2^(unstake_threshold with upper bound)
				.checked_shl(unstake_threshold)
				.map(|x| x.min(slot_stake))
				.unwrap_or(slot_stake);
			let _ = Self::slash_validator(&v, slash);
			<Validators<T>>::remove(&v);
			let _ = Self::apply_force_new_era(false);
			
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

impl<T: Trait> EnsureAccountLiquid<T::AccountId, BalanceOf<T>> for Module<T> {
	fn ensure_account_liquid(who: &T::AccountId) -> Result {
		if <Bonded<T>>::exists(who) {
			Err("stash accounts are not liquid")
		} else {
			Ok(())
		}
	}
	fn ensure_account_can_withdraw(
		who: &T::AccountId,
		amount: BalanceOf<T>,
		_reason: WithdrawReason,
	) -> Result {
		if let Some(controller) = Self::bonded(who) {
			let ledger = Self::ledger(&controller).ok_or("stash without controller")?;
			let free_balance = T::Currency::free_balance(&who);
			ensure!(free_balance.saturating_sub(ledger.total) > amount,
				"stash with too much under management");
		}		
		Ok(())
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		if let Some(controller) = <Bonded<T>>::take(who) {
			<Ledger<T>>::remove(&controller);
			<Payee<T>>::remove(&controller);
			<SlashCount<T>>::remove(&controller);
			<Validators<T>>::remove(&controller);
			<Nominators<T>>::remove(&controller);
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
