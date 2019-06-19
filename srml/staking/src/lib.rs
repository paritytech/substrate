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
//! The Staking module is used to manage funds at stake by network maintainers.
//!
//! - [`staking::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The Staking module is the means by which a set of network maintainers (known as _authorities_
//! in some contexts and _validators_ in others) are chosen based upon those who voluntarily place
//! funds under deposit. Under deposit, those funds are rewarded under normal operation but are
//! held at pain of _slash_ (expropriation) should the staked maintainer be found not to be
//! discharging its duties properly.
//!
//! ### Terminology
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! - Staking: The process of locking up funds for some time, placing them at risk of slashing
//! (loss) in order to become a rewarded maintainer of the network.
//! - Validating: The process of running a node to actively maintain the network, either by
//! producing blocks or guaranteeing finality of the chain.
//! - Nominating: The process of placing staked funds behind one or more validators in order to
//! share in any reward, and punishment, they take.
//! - Stash account: The account holding an owner's funds used for staking.
//! - Controller account: The account that controls an owner's funds for staking.
//! - Era: A (whole) number of sessions, which is the period that the validator set (and each
//! validator's active nominator set) is recalculated and where rewards are paid out.
//! - Slash: The punishment of a staker by reducing its funds.
//!
//! ### Goals
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! The staking system in Substrate NPoS is designed to make the following possible:
//!
//! - Stake funds that are controlled by a cold wallet.
//! - Withdraw some, or deposit more, funds without interrupting the role of an entity.
//! - Switch between roles (nominator, validator, idle) with minimal overhead.
//!
//! ### Scenarios
//!
//! #### Staking
//!
//! Almost any interaction with the Staking module requires a process of _**bonding**_ (also known
//! as being a _staker_). To become *bonded*, a fund-holding account known as the _stash account_,
//! which holds some or all of the funds that become frozen in place as part of the staking process,
//! is paired with an active **controller** account, which issues instructions on how they shall be
//! used.
//!
//! An account pair can become bonded using the [`bond`](./enum.Call.html#variant.bond) call.
//!
//! Stash accounts can change their associated controller using the
//! [`set_controller`](./enum.Call.html#variant.set_controller) call.
//!
//! There are three possible roles that any staked account pair can be in: `Validator`, `Nominator`
//! and `Idle` (defined in [`StakerStatus`](./enum.StakerStatus.html)). There are three
//! corresponding instructions to change between roles, namely:
//! [`validate`](./enum.Call.html#variant.validate), [`nominate`](./enum.Call.html#variant.nominate),
//! and [`chill`](./enum.Call.html#variant.chill).
//!
//! #### Validating
//!
//! A **validator** takes the role of either validating blocks or ensuring their finality,
//! maintaining the veracity of the network. A validator should avoid both any sort of malicious
//! misbehavior and going offline. Bonded accounts that state interest in being a validator do NOT
//! get immediately chosen as a validator. Instead, they are declared as a _candidate_ and they
//! _might_ get elected at the _next era_ as a validator. The result of the election is determined
//! by nominators and their votes.
//!
//! An account can become a validator candidate via the
//! [`validate`](./enum.Call.html#variant.validate) call.
//!
//! #### Nomination
//!
//! A **nominator** does not take any _direct_ role in maintaining the network, instead, it votes on
//! a set of validators  to be elected. Once interest in nomination is stated by an account, it
//! takes effect at the next election round. The funds in the nominator's stash account indicate the
//! _weight_ of its vote. Both the rewards and any punishment that a validator earns are shared
//! between the validator and its nominators. This rule incentivizes the nominators to NOT vote for
//! the misbehaving/offline validators as much as possible, simply because the nominators will also
//! lose funds if they vote poorly.
//!
//! An account can become a nominator via the [`nominate`](enum.Call.html#variant.nominate) call.
//!
//! #### Rewards and Slash
//!
//! The **reward and slashing** procedure is the core of the Staking module, attempting to _embrace
//! valid behavior_ while _punishing any misbehavior or lack of availability_.
//!
//! Slashing can occur at any point in time, once misbehavior is reported. Once slashing is
//! determined, a value is deducted from the balance of the validator and all the nominators who
//! voted for this validator (values are deducted from the _stash_ account of the slashed entity).
//!
//! Similar to slashing, rewards are also shared among a validator and its associated nominators.
//! Yet, the reward funds are not always transferred to the stash account and can be configured.
//! See [Reward Calculation](#reward-calculation) for more details.
//!
//! #### Chilling
//!
//! Finally, any of the roles above can choose to step back temporarily and just chill for a while.
//! This means that if they are a nominator, they will not be considered as voters anymore and if
//! they are validators, they will no longer be a candidate for the next election.
//!
//! An account can step back via the [`chill`](enum.Call.html#variant.chill) call.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! The dispatchable functions of the Staking module enable the steps needed for entities to accept
//! and change their role, alongside some helper functions to get/set the metadata of the module.
//!
//! ### Public Functions
//!
//! The Staking module contains many public storage items and (im)mutable functions.
//!
//! ## Usage
//!
//! ### Example: Reporting Misbehavior
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result};
//! use system::ensure_signed;
//! use srml_staking::{self as staking};
//!
//! pub trait Trait: staking::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!			/// Report whoever calls this function as offline once.
//! 		pub fn report_sender(origin) -> Result {
//! 			let reported = ensure_signed(origin)?;
//! 			<staking::Module<T>>::on_offline_validator(reported, 1);
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```
//!
//! ## Implementation Details
//!
//! ### Slot Stake
//!
//! The term [`SlotStake`](./struct.Module.html#method.slot_stake) will be used throughout this
//! section. It refers to a value calculated at the end of each era, containing the _minimum value
//! at stake among all validators._ Note that a validator's value at stake might be a combination
//! of the validator's own stake and the votes it received. See [`Exposure`](./struct.Exposure.html)
//! for more details.
//!
//! ### Reward Calculation
//!
//! Rewards are recorded **per-session** and paid **per-era**. The value of the reward for each
//! session is calculated at the end of the session based on the timeliness of the session, then
//! accumulated to be paid later. The value of the new _per-session-reward_ is calculated at the end
//! of each era by multiplying `SlotStake` and `SessionReward`  (`SessionReward` is the
//! multiplication factor, represented by a number between 0 and 1). Once a new era is triggered,
//! rewards are paid to the validators and their associated nominators.
//!
//! The validator can declare an amount, named
//! [`validator_payment`](./struct.ValidatorPrefs.html#structfield.validator_payment), that does not
//! get shared with the nominators at each reward payout through its
//! [`ValidatorPrefs`](./struct.ValidatorPrefs.html). This value gets deducted from the total reward
//! that can be paid. The remaining portion is split among the validator and all of the nominators
//! that nominated the validator, proportional to the value staked behind this validator (_i.e._
//! dividing the [`own`](./struct.Exposure.html#structfield.own) or
//! [`others`](./struct.Exposure.html#structfield.others) by
//! [`total`](./struct.Exposure.html#structfield.total) in [`Exposure`](./struct.Exposure.html)).
//!
//! All entities who receive a reward have the option to choose their reward destination
//! through the [`Payee`](./struct.Payee.html) storage item (see
//! [`set_payee`](enum.Call.html#variant.set_payee)), to be one of the following:
//!
//! - Controller account, (obviously) not increasing the staked value.
//! - Stash account, not increasing the staked value.
//! - Stash account, also increasing the staked value.
//!
//! ### Slashing details
//!
//! A validator can be _reported_ to be offline at any point via the public function
//! [`on_offline_validator`](enum.Call.html#variant.on_offline_validator). Each validator declares
//! how many times it can be _reported_ before it actually gets slashed via its
//! [`ValidatorPrefs::unstake_threshold`](./struct.ValidatorPrefs.html#structfield.unstake_threshold).
//!
//! On top of this, the Staking module also introduces an
//! [`OfflineSlashGrace`](./struct.Module.html#method.offline_slash_grace), which applies
//! to all validators and prevents them from getting immediately slashed.
//!
//! Essentially, a validator gets slashed once they have been reported more than
//! [`OfflineSlashGrace`] + [`ValidatorPrefs::unstake_threshold`] times. Getting slashed due to
//! offline report always leads to being _unstaked_ (_i.e._ removed as a validator candidate) as
//! the consequence.
//!
//! The base slash value is computed _per slash-event_ by multiplying
//! [`OfflineSlash`](./struct.Module.html#method.offline_slash) and the `total` `Exposure`. This
//! value is then multiplied by `2.pow(unstake_threshold)` to obtain the final slash value. All
//! individual accounts' punishments are capped at their total stake (NOTE: This cap should never
//! come into force in a correctly implemented, non-corrupted, well-configured system).
//!
//! ### Additional Fund Management Operations
//!
//! Any funds already placed into stash can be the target of the following operations:
//!
//! The controller account can free a portion (or all) of the funds using the
//! [`unbond`](enum.Call.html#variant.unbond) call. Note that the funds are not immediately
//! accessible. Instead, a duration denoted by [`BondingDuration`](./struct.BondingDuration.html)
//! (in number of eras) must pass until the funds can actually be removed. Once the
//! `BondingDuration` is over, the [`withdraw_unbonded`](./enum.Call.html#variant.withdraw_unbonded)
//! call can be used to actually withdraw the funds.
//!
//! Note that there is a limitation to the number of fund-chunks that can be scheduled to be
//! unlocked in the future via [`unbond`](enum.Call.html#variant.unbond). In case this maximum
//! (`MAX_UNLOCKING_CHUNKS`) is reached, the bonded account _must_ first wait until a successful
//! call to `withdraw_unbonded` to remove some of the chunks.
//!
//! ### Election Algorithm
//!
//! The current election algorithm is implemented based on Phragmén.
//! The reference implementation can be found
//! [here](https://github.com/w3f/consensus/tree/master/NPoS).
//!
//! The election algorithm, aside from electing the validators with the most stake value and votes,
//! tries to divide the nominator votes among candidates in an equal manner. To further assure this,
//! an optional post-processing can be applied that iteratively normalizes the nominator staked
//! values until the total difference among votes of a particular nominator are less than a
//! threshold.
//!
//! ## GenesisConfig
//!
//! The Staking module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).
//!
//! ## Related Modules
//!
//! - [Balances](../srml_balances/index.html): Used to manage values at stake.
//! - [Session](../srml_session/index.html): Used to manage sessions. Also, a list of new validators
//! is stored in the Session module's `Validators` at the end of each era.

#![recursion_limit="128"]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(all(feature = "bench", test), feature(test))]

#[cfg(all(feature = "bench", test))]
extern crate test;

#[cfg(any(feature = "bench", test))]
mod mock;

#[cfg(test)]
mod tests;

mod phragmen;

#[cfg(all(feature = "bench", test))]
mod benches;

#[cfg(feature = "std")]
use runtime_io::with_storage;
use rstd::{prelude::*, result, collections::btree_map::BTreeMap};
use parity_codec::{HasCompact, Encode, Decode};
use srml_support::{
	StorageValue, StorageMap, EnumerableStorageMap, decl_module, decl_event,
	decl_storage, ensure, traits::{
		Currency, OnFreeBalanceZero, OnDilution, LockIdentifier, LockableCurrency,
		WithdrawReasons, OnUnbalanced, Imbalance, Get
	}
};
use session::{OnSessionEnding, SessionIndex};
use primitives::Perbill;
use primitives::traits::{
	Convert, Zero, One, StaticLookup, CheckedSub, CheckedShl, Saturating, Bounded
};
#[cfg(feature = "std")]
use primitives::{Serialize, Deserialize};
use system::ensure_signed;

use phragmen::{elect, ACCURACY, ExtendedBalance};

const RECENT_OFFLINE_COUNT: usize = 32;
const DEFAULT_MINIMUM_VALIDATOR_COUNT: u32 = 4;
const MAX_NOMINATIONS: usize = 16;
const MAX_UNSTAKE_THRESHOLD: u32 = 10;
const MAX_UNLOCKING_CHUNKS: usize = 32;
const STAKING_ID: LockIdentifier = *b"staking ";

/// Counter for the number of eras that have passed.
pub type EraIndex = u32;

/// Indicates the initial status of the staker.
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum StakerStatus<AccountId> {
	/// Chilling.
	Idle,
	/// Declared desire in validating or already participating in it.
	Validator,
	/// Nominating for a group of other stakers.
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
	/// Reward that validator takes up-front; only the rest is split between themselves and
	/// nominators.
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
pub struct UnlockChunk<Balance: HasCompact> {
	/// Amount of funds to be unlocked.
	#[codec(compact)]
	value: Balance,
	/// Era number at which point it'll be unlocked.
	#[codec(compact)]
	era: EraIndex,
}

/// The ledger of a (bonded) stash.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct StakingLedger<AccountId, Balance: HasCompact> {
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
	pub unlocking: Vec<UnlockChunk<Balance>>,
}

impl<
	AccountId,
	Balance: HasCompact + Copy + Saturating,
> StakingLedger<AccountId, Balance> {
	/// Remove entries from `unlocking` that are sufficiently old and reduce the
	/// total by the sum of their balances.
	fn consolidate_unlocked(self, current_era: EraIndex) -> Self {
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
	/// The stash account of the nominator in question.
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
type PositiveImbalanceOf<T> =
<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

type RawAssignment<T> = (<T as system::Trait>::AccountId, ExtendedBalance);
type Assignment<T> = (<T as system::Trait>::AccountId, ExtendedBalance, BalanceOf<T>);
type ExpoMap<T> = BTreeMap<
	<T as system::Trait>::AccountId,
	Exposure<<T as system::Trait>::AccountId, BalanceOf<T>>
>;

pub trait Trait: system::Trait + session::Trait {
	/// The staking balance.
	type Currency: LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;

	/// Convert a balance into a number used for election calculation.
	/// This must fit into a `u64` but is allowed to be sensibly lossy.
	/// TODO: #1377
	/// The backward convert should be removed as the new Phragmen API returns ratio.
	/// The post-processing needs it but will be moved to off-chain.
	type CurrencyToVote: Convert<BalanceOf<Self>, u64> + Convert<u128, BalanceOf<Self>>;

	/// Some tokens minted.
	type OnRewardMinted: OnDilution<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Handler for the unbalanced reduction when slashing a staker.
	type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced increment when rewarding a staker.
	type Reward: OnUnbalanced<PositiveImbalanceOf<Self>>;

	/// Number of sessions per era.
	type SessionsPerEra: Get<SessionIndex>;

	/// Number of eras that staked funds must remain bonded for.
	type BondingDuration: Get<EraIndex>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Staking {

		/// The ideal number of staking participants.
		pub ValidatorCount get(validator_count) config(): u32;
		/// Minimum number of staking participants before emergency conditions are imposed.
		pub MinimumValidatorCount get(minimum_validator_count) config():
			u32 = DEFAULT_MINIMUM_VALIDATOR_COUNT;
		/// Maximum reward, per validator, that is provided per acceptable session.
		pub SessionReward get(session_reward) config(): Perbill = Perbill::from_parts(60);
		/// Slash, per validator that is taken for the first time they are found to be offline.
		pub OfflineSlash get(offline_slash) config(): Perbill = Perbill::from_millionths(1000);
		/// Number of instances of offline reports before slashing begins for validators.
		pub OfflineSlashGrace get(offline_slash_grace) config(): u32;

		/// Any validators that may never be slashed or forcibly kicked. It's a Vec since they're
		/// easy to initialize and the performance hit is minimal (we expect no more than four
		/// invulnerables) and restricted to testnets.
		pub Invulnerables get(invulnerables) config(): Vec<T::AccountId>;

		/// Map from all locked "stash" accounts to the controller account.
		pub Bonded get(bonded): map T::AccountId => Option<T::AccountId>;
		/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
		pub Ledger get(ledger):
			map T::AccountId => Option<StakingLedger<T::AccountId, BalanceOf<T>>>;

		/// Where the reward payment should be made. Keyed by stash.
		pub Payee get(payee): map T::AccountId => RewardDestination;

		/// The map from (wannabe) validator stash key to the preferences of that validator.
		pub Validators get(validators): linked_map T::AccountId => ValidatorPrefs<BalanceOf<T>>;

		/// The map from nominator stash key to the set of stash keys of all validators to nominate.
		pub Nominators get(nominators): linked_map T::AccountId => Vec<T::AccountId>;

		/// Nominators for a particular account that is in action right now. You can't iterate
		/// through validators here, but you can find them in the Session module.
		///
		/// This is keyed by the stash account.
		pub Stakers get(stakers): map T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		// The historical validators and their nominations for a given era. Stored as a trie root
		// of the mapping `T::AccountId` => `Exposure<T::AccountId, BalanceOf<T>>`, which is just
		// the contents of `Stakers`, under a key that is the `era`.
		//
		// Every era change, this will be appended with the trie root of the contents of `Stakers`,
		// and the oldest entry removed down to a specific number of entries (probably around 90 for
		// a 3 month history).
		// pub HistoricalStakers get(historical_stakers): map T::BlockNumber => Option<H256>;

		/// The currently elected validator set keyed by stash account ID.
		pub CurrentElected get(current_elected): Vec<T::AccountId>;

		/// The current era index.
		pub CurrentEra get(current_era) config(): EraIndex;

		/// Maximum reward, per validator, that is provided per acceptable session.
		pub CurrentSessionReward get(current_session_reward) config(): BalanceOf<T>;

		/// The accumulated reward for the current era. Reset to zero at the beginning of the era
		/// and increased for every successfully finished session.
		pub CurrentEraReward get(current_era_reward): BalanceOf<T>;

		/// The amount of balance actively at stake for each validator slot, currently.
		///
		/// This is used to derive rewards and punishments.
		pub SlotStake get(slot_stake) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|&(_, _, value, _)| value).min().unwrap_or_default()
		}): BalanceOf<T>;

		/// The number of times a given validator has been reported offline. This gets decremented
		/// by one each era that passes.
		pub SlashCount get(slash_count): map T::AccountId => u32;

		/// Most recent `RECENT_OFFLINE_COUNT` instances. (Who it was, when it was reported, how
		/// many instances they were offline for).
		pub RecentlyOffline get(recently_offline): Vec<(T::AccountId, T::BlockNumber, u32)>;

		/// True if the next session change will be a new era regardless of index.
		pub ForceNewEra get(forcing_new_era): bool;
	}
	add_extra_genesis {
		config(stakers):
			Vec<(T::AccountId, T::AccountId, BalanceOf<T>, StakerStatus<T::AccountId>)>;
		build(|
			storage: &mut primitives::StorageOverlay,
			_: &mut primitives::ChildrenStorageOverlay,
			config: &GenesisConfig<T>
		| {
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

				if let (_, Some(validators)) = <Module<T>>::select_validators() {
					<session::Validators<T>>::put(&validators);
				}
			});
		});
	}
}

decl_event!(
	pub enum Event<T> where Balance = BalanceOf<T>, <T as system::Trait>::AccountId {
		/// All validators have been rewarded by the given balance.
		Reward(Balance),
		/// One validator (and its nominators) has been given an offline-warning (it is still
		/// within its grace). The accrued number of slashes is recorded, too.
		OfflineWarning(AccountId, u32),
		/// One validator (and its nominators) has been slashed by the given amount.
		OfflineSlash(AccountId, Balance),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will
		/// be the  account that controls it.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash account.
		///
		/// # <weight>
		/// - Independent of the arguments. Moderate complexity.
		/// - O(1).
		/// - Three extra DB entries.
		///
		/// NOTE: Two of the storage writes (`Self::bonded`, `Self::payee`) are _never_ cleaned unless
		/// the `origin` falls below _existential deposit_ and gets removed as dust.
		///
		/// NOTE: At the moment, there are no financial restrictions to bond
		/// (which creates a bunch of storage items for an account). In essence, nothing prevents many accounts from
		/// spamming `Staking` storage by bonding 1 UNIT. See test case: `bond_with_no_staked_value`.
		/// # </weight>
		fn bond(origin,
			controller: <T::Lookup as StaticLookup>::Source,
			#[compact] value: BalanceOf<T>,
			payee: RewardDestination
		) {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::exists(&stash) {
				return Err("stash already bonded")
			}

			let controller = T::Lookup::lookup(controller)?;

			if <Ledger<T>>::exists(&controller) {
				return Err("controller already paired")
			}

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate and remove once you unbond __everything__.
			<Bonded<T>>::insert(&stash, controller.clone());
			<Payee<T>>::insert(&stash, payee);

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);
			let item = StakingLedger { stash, total: value, active: value, unlocking: vec![] };
			Self::update_ledger(&controller, &item);
		}

		/// Add some extra amount that have appeared in the stash `free_balance` into the balance up
		/// for  staking.
		///
		/// Use this if there are additional funds in your stash account that you wish to bond.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash, not the controller.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - O(1).
		/// - One DB entry.
		/// # </weight>
		fn bond_extra(origin, #[compact] max_additional: BalanceOf<T>) {
			let stash = ensure_signed(origin)?;

			let controller = Self::bonded(&stash).ok_or("not a stash")?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;

			let stash_balance = T::Currency::free_balance(&stash);

			if let Some(extra) = stash_balance.checked_sub(&ledger.total) {
				let extra = extra.min(max_additional);
				ledger.total += extra;
				ledger.active += extra;
				Self::update_ledger(&controller, &ledger);
			}
		}

		/// Schedule a portion of the stash to be unlocked ready for transfer out after the bond
		/// period ends. If this leaves an amount actively bonded less than
		/// T::Currency::existential_deposit(), then it is increased to the full amount.
		///
		/// Once the unlock period is done, you can call `withdraw_unbonded` to actually move
		/// the funds out of management ready for transfer.
		///
		/// No more than a limited number of unlocking chunks (see `MAX_UNLOCKING_CHUNKS`)
		/// can co-exists at the same time. In that case, [`Call::withdraw_unbonded`] need
		/// to be called first to remove some of the chunks (if possible).
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// See also [`Call::withdraw_unbonded`].
		///
		/// # <weight>
		/// - Independent of the arguments. Limited but potentially exploitable complexity.
		/// - Contains a limited number of reads.
		/// - Each call (requires the remainder of the bonded balance to be above `minimum_balance`)
		///   will cause a new entry to be inserted into a vector (`Ledger.unlocking`) kept in storage.
		///   The only way to clean the aforementioned storage item is also user-controlled via `withdraw_unbonded`.
		/// - One DB entry.
		/// </weight>
		fn unbond(origin, #[compact] value: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or("not a controller")?;
			ensure!(
				ledger.unlocking.len() < MAX_UNLOCKING_CHUNKS,
				"can not schedule more unlock chunks"
			);

			let mut value = value.min(ledger.active);

			if !value.is_zero() {
				ledger.active -= value;

				// Avoid there being a dust balance left in the staking system.
				if ledger.active < T::Currency::minimum_balance() {
					value += ledger.active;
					ledger.active = Zero::zero();
				}

				let era = Self::current_era() + T::BondingDuration::get();
				ledger.unlocking.push(UnlockChunk { value, era });
				Self::update_ledger(&controller, &ledger);
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
		///
		/// # <weight>
		/// - Could be dependent on the `origin` argument and how much `unlocking` chunks exist. It implies
		///   `consolidate_unlocked` which loops over `Ledger.unlocking`, which is indirectly
		///   user-controlled. See [`unbond`] for more detail.
		/// - Contains a limited number of reads, yet the size of which could be large based on `ledger`.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		fn withdraw_unbonded(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let ledger = ledger.consolidate_unlocked(Self::current_era());
			Self::update_ledger(&controller, &ledger);
		}

		/// Declare the desire to validate for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains a limited number of reads.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		fn validate(origin, prefs: ValidatorPrefs<BalanceOf<T>>) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash = &ledger.stash;
			ensure!(
				prefs.unstake_threshold <= MAX_UNSTAKE_THRESHOLD,
				"unstake threshold too large"
			);
			<Nominators<T>>::remove(stash);
			<Validators<T>>::insert(stash, prefs);
		}

		/// Declare the desire to nominate `targets` for the origin controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - The transaction's complexity is proportional to the size of `targets`,
		/// which is capped at `MAX_NOMINATIONS`.
		/// - Both the reads and writes follow a similar pattern.
		/// # </weight>
		fn nominate(origin, targets: Vec<<T::Lookup as StaticLookup>::Source>) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash = &ledger.stash;
			ensure!(!targets.is_empty(), "targets cannot be empty");
			let targets = targets.into_iter()
				.take(MAX_NOMINATIONS)
				.map(T::Lookup::lookup)
				.collect::<result::Result<Vec<T::AccountId>, &'static str>>()?;

			<Validators<T>>::remove(stash);
			<Nominators<T>>::insert(stash, targets);
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
		fn chill(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash = &ledger.stash;
			<Validators<T>>::remove(stash);
			<Nominators<T>>::remove(stash);
		}

		/// (Re-)set the payment target for a controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the controller, not the stash.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains a limited number of reads.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		fn set_payee(origin, payee: RewardDestination) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or("not a controller")?;
			let stash = &ledger.stash;
			<Payee<T>>::insert(stash, payee);
		}

		/// (Re-)set the payment target for a controller.
		///
		/// Effects will be felt at the beginning of the next era.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash, not the controller.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - Contains a limited number of reads.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		fn set_controller(origin, controller: <T::Lookup as StaticLookup>::Source) {
			let stash = ensure_signed(origin)?;
			let old_controller = Self::bonded(&stash).ok_or("not a stash")?;
			let controller = T::Lookup::lookup(controller)?;
			if <Ledger<T>>::exists(&controller) {
				return Err("controller already paired")
			}
			if controller != old_controller {
				<Bonded<T>>::insert(&stash, &controller);
				if let Some(l) = <Ledger<T>>::take(&old_controller) {
					<Ledger<T>>::insert(&controller, l);
				}
			}
		}

		/// The ideal number of validators.
		fn set_validator_count(#[compact] new: u32) {
			<ValidatorCount<T>>::put(new);
		}

		// ----- Root calls.

		/// Force there to be a new era. This also forces a new session immediately after.
		/// `apply_rewards` should be true for validators to get the session reward.
		///
		/// # <weight>
		/// - Independent of the arguments.
		/// - Triggers the Phragmen election. Expensive but not user-controlled.
		/// - Depends on state: `O(|edges| * |validators|)`.
		/// # </weight>
		fn force_new_era() {
			Self::apply_force_new_era()
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

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	/// The total balance that can be slashed from a validator controller account as of
	/// right now.
	pub fn slashable_balance(who: &T::AccountId) -> BalanceOf<T> {
		Self::stakers(who).total
	}

	// MUTABLES (DANGEROUS)

	/// Update the ledger for a controller. This will also update the stash lock.
	fn update_ledger(
		controller: &T::AccountId,
		ledger: &StakingLedger<T::AccountId, BalanceOf<T>>
	) {
		T::Currency::set_lock(
			STAKING_ID,
			&ledger.stash,
			ledger.total,
			T::BlockNumber::max_value(),
			WithdrawReasons::all()
		);
		<Ledger<T>>::insert(controller, ledger);
	}

	/// Slash a given validator by a specific amount. Removes the slash from the validator's
	/// balance by preference, and reduces the nominators' balance if needed.
	fn slash_validator(stash: &T::AccountId, slash: BalanceOf<T>) {
		// The exposure (backing stake) information of the validator to be slashed.
		let exposure = Self::stakers(stash);
		// The amount we are actually going to slash (can't be bigger than the validator's total
		// exposure)
		let slash = slash.min(exposure.total);
		// The amount we'll slash from the validator's stash directly.
		let own_slash = exposure.own.min(slash);
		let (mut imbalance, missing) = T::Currency::slash(stash, own_slash);
		let own_slash = own_slash - missing;
		// The amount remaining that we can't slash from the validator, that must be taken from the
		// nominators.
		let rest_slash = slash - own_slash;
		if !rest_slash.is_zero() {
			// The total to be slashed from the nominators.
			let total = exposure.total - exposure.own;
			if !total.is_zero() {
				// FIXME #1572 avoid overflow
				let safe_mul_rational = |b| b * rest_slash / total;
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
	fn make_payout(stash: &T::AccountId, amount: BalanceOf<T>) -> Option<PositiveImbalanceOf<T>> {
		let dest = Self::payee(stash);
		match dest {
			RewardDestination::Controller => Self::bonded(stash)
				.and_then(|controller|
					T::Currency::deposit_into_existing(&controller, amount).ok()
				),
			RewardDestination::Stash =>
				T::Currency::deposit_into_existing(stash, amount).ok(),
			RewardDestination::Staked => Self::bonded(stash)
				.and_then(|c| Self::ledger(&c).map(|l| (c, l)))
				.and_then(|(controller, mut l)| {
					l.active += amount;
					l.total += amount;
					let r = T::Currency::deposit_into_existing(stash, amount).ok();
					Self::update_ledger(&controller, &l);
					r
				}),
		}
	}

	/// Reward a given validator by a specific amount. Add the reward to the validator's, and its
	/// nominators' balance, pro-rata based on their exposure, after having removed the validator's
	/// pre-payout cut.
	fn reward_validator(stash: &T::AccountId, reward: BalanceOf<T>) {
		let off_the_table = reward.min(Self::validators(stash).validator_payment);
		let reward = reward - off_the_table;
		let mut imbalance = <PositiveImbalanceOf<T>>::zero();
		let validator_cut = if reward.is_zero() {
			Zero::zero()
		} else {
			let exposure = Self::stakers(stash);
			let total = exposure.total.max(One::one());
			// FIXME #1572:  avoid overflow
			let safe_mul_rational = |b| b * reward / total;
			for i in &exposure.others {
				let nom_payout = safe_mul_rational(i.value);
				imbalance.maybe_subsume(Self::make_payout(&i.who, nom_payout));
			}
			safe_mul_rational(exposure.own)
		};
		imbalance.maybe_subsume(Self::make_payout(stash, validator_cut + off_the_table));
		T::Reward::on_unbalanced(imbalance);
	}

	/// Session has just ended. Provide the validator set for the next session if it's an era-end.
	fn new_session(session_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		// accumulate good session reward
		let reward = Self::current_session_reward();
		<CurrentEraReward<T>>::mutate(|r| *r += reward);

		if <ForceNewEra<T>>::take() || session_index % T::SessionsPerEra::get() == 0 {
			Self::new_era()
		} else {
			None
		}
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens immediately before a session change to ensure that new validators
	/// get a chance to set their session keys.
	fn new_era() -> Option<Vec<T::AccountId>> {
		// Payout
		let reward = <CurrentEraReward<T>>::take();
		if !reward.is_zero() {
			let validators = Self::current_elected();
			for v in validators.iter() {
				Self::reward_validator(v, reward);
			}
			Self::deposit_event(RawEvent::Reward(reward));
			let len = validators.len() as u32; // validators length can never overflow u64
			let len: BalanceOf<T> = len.into();
			let total_minted = reward * len;
			let total_rewarded_stake = Self::slot_stake() * len;
			T::OnRewardMinted::on_dilution(total_minted, total_rewarded_stake);
		}

		// Increment current era.
		<CurrentEra<T>>::mutate(|s| *s += 1);

		// Reassign all Stakers.
		let (slot_stake, maybe_new_validators) = Self::select_validators();

		// Update the balances for rewarding according to the stakes.
		<CurrentSessionReward<T>>::put(Self::session_reward() * slot_stake);

		maybe_new_validators
	}

	fn slashable_balance_of(stash: &T::AccountId) -> BalanceOf<T> {
		Self::bonded(stash).and_then(Self::ledger).map(|l| l.total).unwrap_or_default()
	}

	/// Select a new validator set from the assembled stakers and their role preferences.
	///
	/// Returns the new `SlotStake` value.
	fn select_validators() -> (BalanceOf<T>, Option<Vec<T::AccountId>>) {
		let maybe_elected_set = elect::<T, _, _, _>(
			Self::validator_count() as usize,
			Self::minimum_validator_count().max(1) as usize,
			<Validators<T>>::enumerate(),
			<Nominators<T>>::enumerate(),
			Self::slashable_balance_of,
		);

		if let Some(elected_set) = maybe_elected_set {
			let elected_stashes = elected_set.0;
			let assignments = elected_set.1;

			// helper closure.
			let to_balance = |b: ExtendedBalance|
				<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
			let to_votes = |b: BalanceOf<T>|
				<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;

			// The return value of this is safe to be converted to u64.
			// The original balance, `b` is within the scope of u64. It is just extended to u128
			// to be properly multiplied by a ratio, which will lead to another value
			// less than u64 for sure. The result can then be safely passed to `to_balance`.
			// For now the backward convert is used. A simple `TryFrom<u64>` is also safe.
			let ratio_of = |b, p| (p as ExtendedBalance).saturating_mul(to_votes(b)) / ACCURACY;

			// Compute the actual stake from nominator's ratio.
			let mut assignments_with_stakes = assignments.iter().map(|(n, a)|(
				n.clone(),
				Self::slashable_balance_of(n),
				a.iter().map(|(acc, r)| (
					acc.clone(),
					*r,
					to_balance(ratio_of(Self::slashable_balance_of(n), *r)),
				))
				.collect::<Vec<Assignment<T>>>()
			)).collect::<Vec<(T::AccountId, BalanceOf<T>, Vec<Assignment<T>>)>>();

			// update elected candidate exposures.
			let mut exposures = <ExpoMap<T>>::new();
			elected_stashes
				.iter()
				.map(|e| (e, Self::slashable_balance_of(e)))
				.for_each(|(e, s)| {
					let item = Exposure { own: s, total: s, ..Default::default() };
					exposures.insert(e.clone(), item);
				});

			for (n, _, assignment) in &assignments_with_stakes {
				for (c, _, s) in assignment {
					if let Some(expo) = exposures.get_mut(c) {
						// NOTE: simple example where this saturates:
						// candidate with max_value stake. 1 nominator with max_value stake.
						// Nuked. Sadly there is not much that we can do about this.
						// See this test: phragmen_should_not_overflow_xxx()
						expo.total = expo.total.saturating_add(*s);
						expo.others.push( IndividualExposure { who: n.clone(), value: *s } );
					}
				}
			}

			// This optimization will most likely be only applied off-chain.
			let do_equalize = false;
			if do_equalize {
				let tolerance = 10 as u128;
				let iterations = 10 as usize;
				phragmen::equalize::<T>(
					&mut assignments_with_stakes,
					&mut exposures,
					tolerance,
					iterations
				);
			}

			// Clear Stakers and reduce their slash_count.
			for v in Self::current_elected().iter() {
				<Stakers<T>>::remove(v);
				let slash_count = <SlashCount<T>>::take(v);
				if slash_count > 1 {
					<SlashCount<T>>::insert(v, slash_count - 1);
				}
			}

			// Populate Stakers and figure out the minimum stake behind a slot.
			let mut slot_stake = BalanceOf::<T>::max_value();
			for (c, e) in exposures.iter() {
				if e.total < slot_stake {
					slot_stake = e.total;
				}
				<Stakers<T>>::insert(c.clone(), e.clone());
			}
			<SlotStake<T>>::put(&slot_stake);

			// Set the new validator set.
			<CurrentElected<T>>::put(&elected_stashes);
			let validators = elected_stashes.into_iter()
				.map(|s| Self::bonded(s).unwrap_or_default())
				.collect::<Vec<_>>();
			(slot_stake, Some(validators))
		} else {
			// There were not enough candidates for even our minimal level of functionality.
			// This is bad.
			// We should probably disable all functionality except for block production
			// and let the chain keep producing blocks until we can decide on a sufficiently
			// substantial set.
			// TODO: #2494
			(Self::slot_stake(), None)
		}
	}

	fn apply_force_new_era() {
		<ForceNewEra<T>>::put(true);
	}

	/// Call when a validator is determined to be offline. `count` is the
	/// number of offenses the validator has committed.
	///
	/// NOTE: This is called with the controller (not the stash) account id.
	pub fn on_offline_validator(controller: T::AccountId, count: usize) {
		if let Some(l) = Self::ledger(&controller) {
			let stash = l.stash;

			// Early exit if validator is invulnerable.
			if Self::invulnerables().contains(&stash) {
				return
			}

			let slash_count = Self::slash_count(&stash);
			let new_slash_count = slash_count + count as u32;
			<SlashCount<T>>::insert(&stash, new_slash_count);
			let grace = Self::offline_slash_grace();

			if RECENT_OFFLINE_COUNT > 0 {
				let item = (stash.clone(), <system::Module<T>>::block_number(), count as u32);
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

			let prefs = Self::validators(&stash);
			let unstake_threshold = prefs.unstake_threshold.min(MAX_UNSTAKE_THRESHOLD);
			let max_slashes = grace + unstake_threshold;

			let event = if new_slash_count > max_slashes {
				let slash_exposure = Self::stakers(&stash).total;
				let offline_slash_base = Self::offline_slash() * slash_exposure;
				// They're bailing.
				let slash = offline_slash_base
					// Multiply slash_mantissa by 2^(unstake_threshold with upper bound)
					.checked_shl(unstake_threshold)
					.map(|x| x.min(slash_exposure))
					.unwrap_or(slash_exposure);
				let _ = Self::slash_validator(&stash, slash);
				let _ = <session::Module<T>>::disable(&controller);

				RawEvent::OfflineSlash(stash.clone(), slash)
			} else {
				RawEvent::OfflineWarning(stash.clone(), slash_count)
			};

			Self::deposit_event(event);
		}
	}
}

impl<T: Trait> OnSessionEnding<T::AccountId> for Module<T> {
	fn on_session_ending(i: SessionIndex) -> Option<Vec<T::AccountId>> {
		Self::new_session(i + 1)
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(stash: &T::AccountId) {
		if let Some(controller) = <Bonded<T>>::take(stash) {
			<Ledger<T>>::remove(&controller);
		}
		<Payee<T>>::remove(stash);
		<SlashCount<T>>::remove(stash);
		<Validators<T>>::remove(stash);
		<Nominators<T>>::remove(stash);
	}
}
