// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! # Staking Module
//!
//! <!-- Original author of paragraph: @gavofyork -->
//! The staking module is the means by which a set of network maintainers (known as "authorities" in some contexts and "validators" in others)
//! are chosen based upon those who voluntarily place funds under deposit. Under deposit, those funds are rewarded under
//! normal operation but are held at pain of "slash" (expropriation) should the staked maintainer be found not to be
//! discharging their duties properly.
//! You can start using the Staking module by implementing the staking [`Trait`].
//!
//! ## Overview
//!
//! ### Terminology
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! - Staking: The process of locking up funds for some time, placing them at risk of slashing (loss) in order to become a rewarded maintainer of the network.
//! - Validating: The process of running a node to actively maintain the network, either by producing blocks or guaranteeing finality of the chain.
//! - Nominating: The process of placing staked funds behind one or more validators in order to share in any reward, and punishment, they take.
//! - Stash account: The account holding an owner's funds used for staking.
//! - Controller account: The account which controls an owner's funds for staking.
//! - Era: A (whole) number of sessions, which is the period that the validator set (and each validator's active nominator set) is recalculated and where rewards are paid out.
//! - Slash: The punishment of a staker by reducing their funds ([reference](#references)).
//!
//! ### Goals
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! The staking system in Substrate NPoS is designed to achieve three goals:
//! - It should be possible to stake funds that are controlled by a cold wallet.
//! - It should be possible to withdraw some, or deposit more, funds without interrupting the role of an entity.
//! - It should be possible to switch between roles (nominator, validator, idle) with minimal overhead.
//!
//! ### Scenarios
//!
//! #### Staking
//!
//! Almost any interaction with the staking module requires at least one account to become **bonded**, also known as
//! being a **staker**. For this, all that it is needed is a secondary _**stash account**_ which will hold the staked funds.
//! Henceforth, the former account that initiated the interest is called the **controller** and the latter, holding the
//! funds, is named the **stash**. Also, note that this implies that entering the staking process requires an _account
//! pair_, one to take the role of the controller and one to be the frozen stash account (any value locked in
//! stash cannot be used, hence called _frozen_). This process in the public API is mostly referred to as _bonding_ via
//! the `bond()` function.
//!
//! Any account pair successfully placed at stake can accept three possible roles, namely: `validate`, `nominate` or
//! simply `chill`. Note that during the process of accepting these roles, the _controller_ account is always responsible
//! for declaring interest and the _stash_ account stays untouched, without directly interacting in any operation.
//!
//! #### Validating
//!
//! A **validator** takes the role of either validating blocks or ensuring their finality, maintaining the veracity of
//! the network. A validator should avoid both any sort of malicious misbehavior and going offline.
//! Bonded accounts that state interest in being a validator do NOT get immediately chosen as a validator. Instead, they
//! are declared as a _candidate_ and they _might_ get elected at the _next **era**_ as a validator. The result of the
//! election is determined by nominators and their votes. An account can become a validator via the `validate()` call.
//!
//! #### Nomination
//!
//! A **nominator** does not take any _direct_ role in maintaining the network, instead, it votes on a set of validators
//! to be elected. Once interest in nomination is stated by an account, it takes effect _immediately_, meaning that its
//! votes will be taken into account at the next election round. As mentioned above, a nominator must also place some
//! funds in a stash account, essentially indicating the _weight_ of its vote. In some sense, the nominator bets on the
//! honesty of a set of validators by voting for them, with the goal of having a share of the reward granted to them.
//! Any rewards given to a validator is shared among that validator and all of the nominators that voted for it. The
//! same logic applies to the slash of a validator; if a validator misbehaves all of its nominators also get slashed.
//! This rule incentivizes the nominators to NOT vote for the misbehaving/offline validators as much as possible, simply
//! because the nominators will also lose funds if they vote poorly. An account can become a nominator via the
//! `nominate()` call.
//!
//! #### Rewards and Slash
//!
//! The **reward and slashing** procedure are the core of the staking module, attempting to _embrace valid behavior_
//! while _punishing any misbehavior or lack of availability_. Slashing can occur at any point in time, once
//! misbehavior is reported. One such misbehavior is a validator being detected as offline more than a certain number of
//! times. Once slashing is determined, a value is deducted from the balance of the validator and all the nominators who
//! voted for this validator. Same rules apply to the rewards in the sense of being shared among a validator and its
//! associated nominators.
//!
//! Finally, any of the roles above can choose to step back temporarily and just chill for a while. This means that if
//! they are a nominator, they will not be considered as voters anymore and if they are validators, they will no longer
//! be a candidate for the next election (again, both effects apply at the beginning of the next era). An account can
//! step back via the `chill()` call.
//!
//! ## Interface
//!
//! ### Types
//!
//! - `Currency`: Used as the measurement means of staking and funds management.
//!
//! ### Dispatchable
//!
//! The Dispatchable functions of the staking module enable the steps needed for entities to accept and change their
//! role, alongside some helper functions to get/set the metadata of the module.
//!
//! Please refer to the [`Call`] enum and its associated variants for a detailed list of dispatchable functions.
//!
//! ### Public
//! The staking module contains many public storage items and (im)mutable functions. Please refer to the [struct list](#structs)
//!  below and the [`Module`](https://crates.parity.io/srml_staking/struct.Module.html) struct definition for more details.
//!
//! ## Usage
//!
//!
//! ### Snippet: Bonding and Accepting Roles
//!
//! An arbitrary account pair, given that the associated stash has the required funds, can become stakers via the following call:
//!
//! ```rust,ignore
//! // bond account 3 as stash
//! // account 4 as controller
//! // with stash value 1500 units
//! // while the rewards get transferred to the controller account.
//! Staking::bond(Origin::signed(3), 4, 1500, RewardDestination::Controller);
//! ```
//!
//! To state desire to become a validator:
//!
//! ```rust,ignore
//! // controller account 4 states desire for validation with the given preferences.
//! Staking::validate(Origin::signed(4), ValidatorPrefs::default());
//! ```
//!
//! Note that, as mentioned, the stash account is transparent in such calls and only the controller initiates the function calls.
//!
//! Similarly, to state desire in nominating:
//!
//! ```rust,ignore
//! // controller account 4 nominates for account 10 and 20.
//! Staking::nominate(Origin::signed(4), vec![20, 10]);
//! ```
//!
//! Finally, account 4 can withdraw from any of the above roles via
//!
//! ```rust,ignore
//! Staking::chill(Origin::signed(4));
//! ```
//!
//! ## Implementation Details
//!
//! ### Slot Stake
//!
//! The term `slot_stake` will be used throughout this section. It refers to a value calculated at the end of each era,
//! containing the _minimum value at stake among all validators._
//!
//! ### Reward Calculation
//!
//! - Rewards are recorded **per-session** and paid **per-era**. The value of the reward for each session is calculated at
//!     the end of the session based on the timeliness of the session, then accumulated to be paid later. The value of
//!     the new _per-session-reward_ is calculated at the end of each era by multiplying `slot_stake` and a configuration
//!     storage item named `SessionReward`.
//! - Once a new era is triggered, rewards are paid to the validators and the associated nominators.
//! - The validator can declare an amount, named `validator_payment`, that does not get shared with the nominators at
//!     each reward payout through their `ValidatorPrefs`. This value gets deducted from the total reward that can be paid.
//!     The remaining portion is split among the validator and all of the nominators who had a vote for this validator,
//!     proportional to their staked value.
//! - All entities who receive a reward have the option to choose their reward destination, through the `Payee` storage item (see `set_payee()`), to be one of the following:
//! - Controller account.
//! - Stash account, not increasing the staked value.
//! - Stash account, also increasing the staked value.
//!
//! ### Slashing details
//!
//! - A validator can be _reported_ to be offline at any point via `on_offline_validator` public function.
//! - Each validator declares how many times it can be _reported_ before it actually gets slashed via the
//!     `unstake_threshold` in `ValidatorPrefs`. On top of this, the module also introduces an `OfflineSlashGrace`,
//!      which applies to all validators and prevents them from getting immediately slashed.
//! - Similar to the reward value, the slash value is updated at the end of each era by multiplying `slot_stake` and a
//!     configuration storage item, `OfflineSlash`.
//! - Once a validator has been reported a sufficient number of times, the actual value that gets deducted from that
//!     validator, and every single nominator that voted for it is calculated by multiplying the result of the above point
//!       by `2.pow(unstake_threshold)`.
//! - If the previous overflows, then `slot_stake` is used.
//! - If the previous is more than what the validator/nominator has in stake, all of its stake is slashed (`.max(total_stake)`).
//!
//! ### Additional Fund Management Operations
//!
//! Any funds already placed into stash can be the target of the following operations:
//!
//! - The controller account can free a portion (or all) of the funds using the `unbond()` call. Note that the funds
//!     are not immediately accessible, instead, a duration denoted by `BondingDuration` (in number of eras) must pass until the funds can actually be removed.
//! - To actually remove the funds, once the bonding duration is over, `withdraw_unbonded()` can be used.
//! - As opposed to the above, additional funds can be added to the stash account via the `bond_extra()` transaction call.
//!
//! ### Election algorithm details.
//!
//! The current election algorithm is implemented based on Phragmén. The reference implementation can be found [here](https://github.com/w3f/consensus/tree/master/NPoS).
//!
//! ## GenesisConfig
//!
//! See the [`GensisConfig`] for a list of attributes that can be provided.
//!
//! ## Related Modules
//!
//! - [**Balances**](https://crates.parity.io/srml_balances/index.html): Used to manage values at stake.
//! - [**Sessions**](https://crates.parity.io/srml_session/index.html): Used to manage sessions. Also, a list of new validators is also stored in the sessions module's `Validators` at the end of each era.
//! - [**System**](https://crates.parity.io/srml_system/index.html): Used to obtain block number and time, among other details.
//!
//! # References
//!
//! 1. This document is written as a more verbose version of the original [Staking.md](../Staking.md) file. Some sections, are taken directly from the aforementioned document.


#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use runtime_io::with_storage;
use rstd::{prelude::*, result};
use parity_codec::{HasCompact, Encode, Decode};
use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result};
use srml_support::{decl_module, decl_event, decl_storage, ensure};
use srml_support::traits::{
	Currency, OnFreeBalanceZero, OnDilution, LockIdentifier, LockableCurrency, WithdrawReasons,
	OnUnbalanced, Imbalance
};
use session::OnSessionChange;
use primitives::Perbill;
use primitives::traits::{Zero, One, As, StaticLookup, Saturating, Bounded};
#[cfg(feature = "std")]
use primitives::{Serialize, Deserialize};
use system::ensure_signed;

mod mock;
mod tests;
mod phragmen;

use phragmen::{elect, ElectionConfig};

const RECENT_OFFLINE_COUNT: usize = 32;
const DEFAULT_MINIMUM_VALIDATOR_COUNT: u32 = 4;
const MAX_NOMINATIONS: usize = 16;
const MAX_UNSTAKE_THRESHOLD: u32 = 10;

// Indicates the initial status of the staker
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum StakerStatus<AccountId> {
	// Chilling.
	Idle,
	// Declared state in validating or already participating in it.
	Validator,
	// Nominating for a group of other stakers.
	Nominator(Vec<AccountId>),
}

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

impl<
	AccountId,
	Balance: HasCompact + Copy + Saturating,
	BlockNumber: HasCompact + PartialOrd
> StakingLedger<AccountId, Balance, BlockNumber> {
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

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: system::Trait + session::Trait {
	/// The staking balance.
	type Currency:
		Currency<Self::AccountId> +
		LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;

	/// Some tokens minted.
	type OnRewardMinted: OnDilution<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Handler for the unbalanced reduction when slashing a staker.
	type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced increment when rewarding a staker.
	type Reward: OnUnbalanced<PositiveImbalanceOf<Self>>;
}

const STAKING_ID: LockIdentifier = *b"staking ";

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
		pub Bonded get(bonded): map T::AccountId => Option<T::AccountId>;
		/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
		pub Ledger get(ledger): map T::AccountId => Option<StakingLedger<T::AccountId, BalanceOf<T>, T::BlockNumber>>;

		/// Where the reward payment should be made.
		pub Payee get(payee): map T::AccountId => RewardDestination;

		/// The set of keys are all controllers that want to validate.
		///
		/// The values are the preferences that a validator has.
		pub Validators get(validators): linked_map T::AccountId => ValidatorPrefs<BalanceOf<T>>;

		/// The set of keys are all controllers that want to nominate.
		///
		/// The value are the nominations.
		pub Nominators get(nominators): linked_map T::AccountId => Vec<T::AccountId>;

		/// Nominators for a particular account that is in action right now. You can't iterate through validators here,
		/// but you can find them in the `sessions` module.
		pub Stakers get(stakers): map T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		// The historical validators and their nominations for a given era. Stored as a trie root of the mapping
		// `T::AccountId` => `Exposure<T::AccountId, BalanceOf<T>>`, which is just the contents of `Stakers`,
		// under a key that is the `era`.
		//
		// Every era change, this will be appended with the trie root of the contents of `Stakers`, and the oldest
		// entry removed down to a specific number of entries (probably around 90 for a 3 month history).
		// pub HistoricalStakers get(historical_stakers): map T::BlockNumber => Option<H256>;

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
			config.stakers.iter().map(|&(_, _, value, _)| value).min().unwrap_or_default()
		}): BalanceOf<T>;

		/// The number of times a given validator has been reported offline. This gets decremented by one each era that passes.
		pub SlashCount get(slash_count): map T::AccountId => u32;

		/// We are forcing a new era.
		pub ForcingNewEra get(forcing_new_era): Option<()>;

		/// Most recent `RECENT_OFFLINE_COUNT` instances. (who it was, when it was reported, how many instances they were offline for).
		pub RecentlyOffline get(recently_offline): Vec<(T::AccountId, T::BlockNumber, u32)>;
	}
	add_extra_genesis {
		config(stakers): Vec<(T::AccountId, T::AccountId, BalanceOf<T>, StakerStatus<T::AccountId>)>;
		build(|storage: &mut primitives::StorageOverlay, _: &mut primitives::ChildrenStorageOverlay, config: &GenesisConfig<T>| {
			with_storage(storage, || {
				for &(ref stash, ref controller, balance, ref status) in &config.stakers {
					assert!(T::Currency::free_balance(&stash) >= balance);
					let _ = <Module<T>>::bond(
						T::Origin::from(Some(stash.clone()).into()),
						T::Lookup::unlookup(controller.clone()),
						balance,
						RewardDestination::Staked
					);
					let _ = match status {
						StakerStatus::Validator => {
							<Module<T>>::validate(
								T::Origin::from(Some(controller.clone()).into()),
								Default::default()
							)
						}, StakerStatus::Nominator(votes) => {
							<Module<T>>::nominate(
								T::Origin::from(Some(controller.clone()).into()),
								votes.iter().map(|l| {T::Lookup::unlookup(l.clone())}).collect()
							)
						}, _ => Ok(())
					};
				}

				<Module<T>>::select_validators();
			});
		});
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will be the
		/// account that controls it.
		///
		/// The dispatch origin for this call must be _Signed_.
		fn bond(origin, controller: <T::Lookup as StaticLookup>::Source, #[compact] value: BalanceOf<T>, payee: RewardDestination) {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::exists(&stash) {
				return Err("stash already bonded")
			}

			let controller = T::Lookup::lookup(controller)?;

			if <Ledger<T>>::exists(&controller) {
				return Err("controller already paired")
			}

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate.
			<Bonded<T>>::insert(&stash, controller.clone());

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);

			Self::update_ledger(&controller, StakingLedger { stash, total: value, active: value, unlocking: vec![] });
			<Payee<T>>::insert(&controller, payee);
		}

		/// Add some extra amount that have appeared in the stash `free_balance` into the balance up for
		/// staking.
		///
		/// Use this if there are additional funds in your stash account that you wish to bond.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		fn bond_extra(origin, max_additional: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash_balance = T::Currency::free_balance(&ledger.stash);

			if stash_balance > ledger.total {
				let extra = (stash_balance - ledger.total).min(max_additional);
				ledger.total += extra;
				ledger.active += extra;
				Self::update_ledger(&controller, ledger);
			}
		}

		/// Schedule a portion of the stash to be unlocked ready for transfer out after the bond
		/// period ends. If this leaves an amount actively bonded less than
		/// T::Currency::existential_deposit(), then it is increased to the full amount.
		///
		/// Once the unlock period is done, you can call `withdraw_unbonded` to actually move
		/// the funds out of management ready for transfer.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// See also [`Call::withdraw_unbonded`].
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
				Self::update_ledger(&controller, ledger);
			}
		}

		/// Remove any unlocked chunks from the `unlocking` queue from our management.
		///
		/// This essentially frees up that balance to be used by the stash account to do
		/// whatever it wants.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// See also [`Call::unbond`].
		fn withdraw_unbonded(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let ledger = ledger.consolidate_unlocked(Self::current_era());
			Self::update_ledger(&controller, ledger);
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
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
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
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
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
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
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		fn set_payee(origin, payee: RewardDestination) {
			let controller = ensure_signed(origin)?;
			let _ledger = Self::ledger(&controller).ok_or("not a controller")?;
			<Payee<T>>::insert(&controller, payee);
		}

		/// (Re-)set the payment target for a controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		fn set_controller(origin, controller: <T::Lookup as StaticLookup>::Source) {
			let stash = ensure_signed(origin)?;
			let old_controller = Self::bonded(&stash).ok_or("not a stash")?;
			let controller = T::Lookup::lookup(controller)?;
			if <Ledger<T>>::exists(&controller) {
				return Err("controller already paired")
			}
			if controller != old_controller {
				<Bonded<T>>::insert(&stash, &controller);
				if let Some(l) = <Ledger<T>>::take(&old_controller) { <Ledger<T>>::insert(&controller, l) };
				<Payee<T>>::insert(&controller, <Payee<T>>::take(&old_controller));
			}
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

// An event in this module.
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

	// MUTABLES (DANGEROUS)

	/// Update the ledger for a controller. This will also update the stash lock.
	fn update_ledger(controller: &T::AccountId, ledger: StakingLedger<T::AccountId, BalanceOf<T>, T::BlockNumber>) {
		T::Currency::set_lock(STAKING_ID, &ledger.stash, ledger.total, T::BlockNumber::max_value(), WithdrawReasons::all());
		<Ledger<T>>::insert(controller, ledger);
	}

	/// Slash a given validator by a specific amount. Removes the slash from their balance by preference,
	/// and reduces the nominators' balance if needed.
	fn slash_validator(v: &T::AccountId, slash: BalanceOf<T>) {
		// The exposure (backing stake) information of the validator to be slashed.
		let exposure = Self::stakers(v);
		// The amount we are actually going to slash (can't be bigger than their total exposure)
		let slash = slash.min(exposure.total);
		// The amount we'll slash from the validator's stash directly.
		let own_slash = exposure.own.min(slash);
		let (mut imbalance, missing) = T::Currency::slash(v, own_slash);
		let own_slash = own_slash - missing;
		// The amount remaining that we can't slash from the validator, that must be taken from the nominators.
		let rest_slash = slash - own_slash;
		if !rest_slash.is_zero() {
			// The total to be slashed from the nominators.
			let total = exposure.total - exposure.own;
			if !total.is_zero() {
				let safe_mul_rational = |b| b * rest_slash / total;// FIXME #1572 avoid overflow
				for i in exposure.others.iter() {
					// best effort - not much that can be done on fail.
					imbalance.subsume(T::Currency::slash(&i.who, safe_mul_rational(i.value)).0)
				}
			}
		}
		T::Slash::on_unbalanced(imbalance);
	}

	/// Actually make a payment to a staker. This uses the currency's reward function
	/// to pay the right payee for the given staker account.
	fn make_payout(who: &T::AccountId, amount: BalanceOf<T>) -> Option<PositiveImbalanceOf<T>> {
		match Self::payee(who) {
			RewardDestination::Controller => T::Currency::deposit_into_existing(&who, amount).ok(),
			RewardDestination::Stash => Self::ledger(who)
				.and_then(|l| T::Currency::deposit_into_existing(&l.stash, amount).ok()),
			RewardDestination::Staked =>
				Self::ledger(who).and_then(|mut l| {
					l.active += amount;
					l.total += amount;
					let r = T::Currency::deposit_into_existing(&l.stash, amount).ok();
					Self::update_ledger(who, l);
					r
				}),
		}
	}

	/// Reward a given validator by a specific amount. Add the reward to their, and their nominators'
	/// balance, pro-rata based on their exposure, after having removed the validator's pre-payout cut.
	fn reward_validator(who: &T::AccountId, reward: BalanceOf<T>) {
		let off_the_table = reward.min(Self::validators(who).validator_payment);
		let reward = reward - off_the_table;
		let mut imbalance = <PositiveImbalanceOf<T>>::zero();
		let validator_cut = if reward.is_zero() {
			Zero::zero()
		} else {
			let exposure = Self::stakers(who);
			let total = exposure.total.max(One::one());
			let safe_mul_rational = |b| b * reward / total;// FIXME #1572:  avoid overflow
			for i in &exposure.others {
				imbalance.maybe_subsume(Self::make_payout(&i.who, safe_mul_rational(i.value)));
			}
			safe_mul_rational(exposure.own)
		};
		imbalance.maybe_subsume(Self::make_payout(who, validator_cut + off_the_table));
		T::Reward::on_unbalanced(imbalance);
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
		let slot_stake = Self::select_validators();

		// Update the balances for slashing/rewarding according to the stakes.
		<CurrentOfflineSlash<T>>::put(Self::offline_slash() * slot_stake);
		<CurrentSessionReward<T>>::put(Self::session_reward() * slot_stake);
	}

	/// Select a new validator set from the assembled stakers and their role preferences.
	///
	/// Returns the new SlotStake value.
	fn select_validators() -> BalanceOf<T> {
		// Map of (would-be) validator account to amount of stake backing it.

		let rounds = || <ValidatorCount<T>>::get() as usize;
		let validators = || <Validators<T>>::enumerate();
		let nominators = || <Nominators<T>>::enumerate();
		let stash_of = |w: &T::AccountId| -> BalanceOf<T> { Self::stash_balance(w) };
		let min_validator_count = Self::minimum_validator_count() as usize;
		let maybe_elected_candidates = elect::<T, _, _, _, _>(
			rounds,
			validators,
			nominators,
			stash_of,
			min_validator_count,
			ElectionConfig::<BalanceOf<T>> {
				equalise: true,
				tolerance: <BalanceOf<T>>::sa(10 as u64),
				iterations: 10,
			}
		);

		if let Some(elected_candidates) = maybe_elected_candidates {
			// Clear Stakers and reduce their slash_count.
			for v in <session::Module<T>>::validators().iter() {
				<Stakers<T>>::remove(v);
				let slash_count = <SlashCount<T>>::take(v);
				if slash_count > 1 {
					<SlashCount<T>>::insert(v, slash_count - 1);
				}
			}

			// Populate Stakers and figure out the minimum stake behind a slot.
			let mut slot_stake = elected_candidates[0].exposure.total;
			for c in &elected_candidates {
				if c.exposure.total < slot_stake {
					slot_stake = c.exposure.total;
				}
				<Stakers<T>>::insert(c.who.clone(), c.exposure.clone());
			}
			<SlotStake<T>>::put(&slot_stake);

			// Set the new validator set.
			<session::Module<T>>::set_validators(
				&elected_candidates.into_iter().map(|i| i.who).collect::<Vec<_>>()
			);

			slot_stake
		} else {
			// There were not enough candidates for even our minimal level of functionality.
			// This is bad.
			// We should probably disable all functionality except for block production
			// and let the chain keep producing blocks until we can decide on a sufficiently
			// substantial set.
			Self::slot_stake()
		}
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
