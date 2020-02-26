// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//! [`validate`](./enum.Call.html#variant.validate),
//! [`nominate`](./enum.Call.html#variant.nominate), and [`chill`](./enum.Call.html#variant.chill).
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
//! Slashing logic is further described in the documentation of the `slashing` module.
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
//! ### Example: Rewarding a validator by id.
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::{self as system, ensure_signed};
//! use pallet_staking::{self as staking};
//!
//! pub trait Trait: staking::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!			/// Reward a validator.
//! 		pub fn reward_myself(origin) -> dispatch::DispatchResult {
//! 			let reported = ensure_signed(origin)?;
//! 			<staking::Module<T>>::reward_by_ids(vec![(reported, 10)]);
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
//! Validators and nominators are rewarded at the end of each era. The total reward of an era is
//! calculated using the era duration and the staking rate (the total amount of tokens staked by
//! nominators and validators, divided by the total token supply). It aims to incentivize toward a
//! defined staking rate. The full specification can be found
//! [here](https://research.web3.foundation/en/latest/polkadot/Token%20Economics.html#inflation-model).
//!
//! Total reward is split among validators and their nominators depending on the number of points
//! they received during the era. Points are added to a validator using
//! [`reward_by_ids`](./enum.Call.html#variant.reward_by_ids) or
//! [`reward_by_indices`](./enum.Call.html#variant.reward_by_indices).
//!
//! [`Module`](./struct.Module.html) implements
//! [`pallet_authorship::EventHandler`](../pallet_authorship/trait.EventHandler.html) to add reward
//! points to block producer and block producer of referenced uncles.
//!
//! The validator and its nominator split their reward as following:
//!
//! The validator can declare an amount, named
//! [`commission`](./struct.ValidatorPrefs.html#structfield.commission), that does not
//! get shared with the nominators at each reward payout through its
//! [`ValidatorPrefs`](./struct.ValidatorPrefs.html). This value gets deducted from the total reward
//! that is paid to the validator and its nominators. The remaining portion is split among the
//! validator and all of the nominators that nominated the validator, proportional to the value
//! staked behind this validator (_i.e._ dividing the
//! [`own`](./struct.Exposure.html#structfield.own) or
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
//! - [Balances](../pallet_balances/index.html): Used to manage values at stake.
//! - [Session](../pallet_session/index.html): Used to manage sessions. Also, a list of new
//!   validators is stored in the Session module's `Validators` at the end of each era.

#![recursion_limit="128"]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
#[cfg(feature = "testing-utils")]
pub mod testing_utils;

pub mod slashing;
pub mod offchain_election;
pub mod inflation;

use sp_std::{prelude::*, result, convert::{TryInto, From}};
use codec::{HasCompact, Encode, Decode};
use frame_support::{
	decl_module, decl_event, decl_storage, ensure, decl_error, debug, Parameter,
	weights::SimpleDispatchInfo,
	dispatch::{IsSubType, DispatchResult},
	traits::{
		Currency, LockIdentifier, LockableCurrency, WithdrawReasons, OnUnbalanced, Imbalance, Get,
		Time, EstimateNextSessionChange,
	}
};
use pallet_session::historical;
use sp_runtime::{
	Perbill, PerU16, PerThing, RuntimeDebug, RuntimeAppPublic,
	curve::PiecewiseLinear,
	traits::{
		Convert, Zero, One, StaticLookup, CheckedSub, Saturating, Bounded, SaturatedConversion,
		AtLeast32Bit, EnsureOrigin, Member, SignedExtension,
	},
	transaction_validity::{
		TransactionValidityError, TransactionValidity, ValidTransaction, InvalidTransaction,
	},
};
use sp_staking::{
	SessionIndex,
	offence::{OnOffenceHandler, OffenceDetails, Offence, ReportOffence},
};
#[cfg(feature = "std")]
use sp_runtime::{Serialize, Deserialize};
use frame_system::{
	self as system, ensure_signed, ensure_root, ensure_none,
	offchain::SubmitUnsignedTransaction,
};
use sp_phragmen::{
	ExtendedBalance, Assignment, PhragmenScore, PhragmenResult, build_support_map, evaluate_support,
	elect, generate_compact_solution_type, is_score_better, VotingLimit,
};

const DEFAULT_MINIMUM_VALIDATOR_COUNT: u32 = 4;
const MAX_UNLOCKING_CHUNKS: usize = 32;
const STAKING_ID: LockIdentifier = *b"staking ";

/// Maximum number of stakers that can be stored in a snapshot.
pub(crate) const MAX_VALIDATORS: u32 = ValidatorIndex::max_value() as u32;
pub(crate) const MAX_NOMINATORS: u32 = NominatorIndex::max_value();

// Note: Maximum nomination limit is set here -- 16.
generate_compact_solution_type!(pub CompactAssignments, 16);

/// Data type used to index nominators in the compact type
pub type NominatorIndex = u32;

/// Data type used to index validators in the compact type.
pub type ValidatorIndex = u16;

/// Counter for the number of eras that have passed.
pub type EraIndex = u32;

/// Counter for the number of "reward" points earned by a given validator.
pub type Points = u32;

/// Accuracy used for on-chain phragmen
pub type ChainAccuracy = Perbill;

/// Accuracy used for off-chain phragmen. This better be small.
pub type OffchainAccuracy = PerU16;

/// The balance type of this module.
pub type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// The compact type for election solutions.
pub type Compact = CompactAssignments<
	NominatorIndex,
	ValidatorIndex,
	OffchainAccuracy,
>;

type PositiveImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;
type MomentOf<T> = <<T as Trait>::Time as Time>::Moment;

/// Staking's key type used for submitting unsigned solutions.
pub mod sr25519 {
	mod app_sr25519 {
		use sp_application_crypto::{app_crypto, key_types::STAKING, sr25519};
		app_crypto!(sr25519, STAKING);
	}

	sp_application_crypto::with_pair! {
		/// A staking keypair using sr25519 as its crypto.
		pub type AuthorityPair = app_sr25519::Pair;
	}

	/// Staking signature using sr25519 as its crypto.
	pub type AuthoritySignature = app_sr25519::Signature;

	/// Staking identifier using sr25519 as its crypto.
	pub type AuthorityId = app_sr25519::Public;
}

/// Reward points of an era. Used to split era total payout between validators.
#[derive(Encode, Decode, Default)]
pub struct EraPoints {
	/// Total number of points. Equals the sum of reward points for each validator.
	total: Points,
	/// The reward points earned by a given validator. The index of this vec corresponds to the
	/// index into the current validator set.
	individual: Vec<Points>,
}

impl EraPoints {
	/// Add the reward to the validator at the given index. Index must be valid
	/// (i.e. `index < current_elected.len()`).
	fn add_points_to_index(&mut self, index: u32, points: u32) {
		if let Some(new_total) = self.total.checked_add(points) {
			self.total = new_total;
			self.individual.resize((index as usize + 1).max(self.individual.len()), 0);
			self.individual[index as usize] += points; // Addition is less than total
		}
	}
}

/// Indicates the initial status of the staker.
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum StakerStatus<AccountId> {
	/// Chilling.
	Idle,
	/// Declared desire in validating or already participating in it.
	Validator,
	/// Nominating for a group of other stakers.
	Nominator(Vec<AccountId>),
}

/// A destination account for payment.
#[derive(PartialEq, Eq, Copy, Clone, Encode, Decode, RuntimeDebug)]
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

/// Preference of what happens regarding validation.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct ValidatorPrefs {
	/// Reward that validator takes up-front; only the rest is split between themselves and
	/// nominators.
	#[codec(compact)]
	pub commission: Perbill,
}

impl Default for ValidatorPrefs {
	fn default() -> Self {
		ValidatorPrefs {
			commission: Default::default(),
		}
	}
}

/// Just a Balance/BlockNumber tuple to encode when a chunk of funds will be unlocked.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct UnlockChunk<Balance: HasCompact> {
	/// Amount of funds to be unlocked.
	#[codec(compact)]
	value: Balance,
	/// Era number at which point it'll be unlocked.
	#[codec(compact)]
	era: EraIndex,
}

/// The ledger of a (bonded) stash.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
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
	Balance: HasCompact + Copy + Saturating + AtLeast32Bit,
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

	/// Re-bond funds that were scheduled for unlocking.
	fn rebond(mut self, value: Balance) -> Self {
		let mut unlocking_balance: Balance = Zero::zero();

		while let Some(last) = self.unlocking.last_mut() {
			if unlocking_balance + last.value <= value {
				unlocking_balance += last.value;
				self.active += last.value;
				self.unlocking.pop();
			} else {
				let diff = value - unlocking_balance;

				unlocking_balance += diff;
				self.active += diff;
				last.value -= diff;
			}

			if unlocking_balance >= value {
				break
			}
		}

		self
	}
}

impl<AccountId, Balance> StakingLedger<AccountId, Balance> where
	Balance: AtLeast32Bit + Saturating + Copy,
{
	/// Slash the validator for a given amount of balance. This can grow the value
	/// of the slash in the case that the validator has less than `minimum_balance`
	/// active funds. Returns the amount of funds actually slashed.
	///
	/// Slashes from `active` funds first, and then `unlocking`, starting with the
	/// chunks that are closest to unlocking.
	fn slash(
		&mut self,
		mut value: Balance,
		minimum_balance: Balance,
	) -> Balance {
		let pre_total = self.total;
		let total = &mut self.total;
		let active = &mut self.active;

		let slash_out_of = |
			total_remaining: &mut Balance,
			target: &mut Balance,
			value: &mut Balance,
		| {
			let mut slash_from_target = (*value).min(*target);

			if !slash_from_target.is_zero() {
				*target -= slash_from_target;

				// don't leave a dust balance in the staking system.
				if *target <= minimum_balance {
					slash_from_target += *target;
					*value += sp_std::mem::replace(target, Zero::zero());
				}

				*total_remaining = total_remaining.saturating_sub(slash_from_target);
				*value -= slash_from_target;
			}
		};

		slash_out_of(total, active, &mut value);

		let i = self.unlocking.iter_mut()
			.map(|chunk| {
				slash_out_of(total, &mut chunk.value, &mut value);
				chunk.value
			})
			.take_while(|value| value.is_zero()) // take all fully-consumed chunks out.
			.count();

		// kill all drained chunks.
		let _ = self.unlocking.drain(..i);

		pre_total.saturating_sub(*total)
	}
}

/// A record of the nominations made by a specific account.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct Nominations<AccountId> {
	/// The targets of nomination.
	pub targets: Vec<AccountId>,
	/// The era the nominations were submitted.
	pub submitted_in: EraIndex,
	/// Whether the nominations have been suppressed.
	pub suppressed: bool,
}

/// The amount of exposure (to slashing) than an individual nominator has.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, RuntimeDebug)]
pub struct IndividualExposure<AccountId, Balance: HasCompact> {
	/// The stash account of the nominator in question.
	who: AccountId,
	/// Amount of funds exposed.
	#[codec(compact)]
	value: Balance,
}

/// A snapshot of the stake backing a single validator in the system.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, Default, RuntimeDebug)]
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

/// A pending slash record. The value of the slash has been computed but not applied yet,
/// rather deferred for several eras.
#[derive(Encode, Decode, Default, RuntimeDebug)]
pub struct UnappliedSlash<AccountId, Balance: HasCompact> {
	/// The stash ID of the offending validator.
	validator: AccountId,
	/// The validator's own slash.
	own: Balance,
	/// All other slashed stakers and amounts.
	others: Vec<(AccountId, Balance)>,
	/// Reporters of the offence; bounty payout recipients.
	reporters: Vec<AccountId>,
	/// The amount of payout.
	payout: Balance,
}

/// Indicate how an election round was computed.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum ElectionCompute {
	/// Result was forcefully computed on chain at the end of the session.
	OnChain,
	/// Result was submitted and accepted to the chain via a signed transaction.
	Signed,
	/// Result was submitted by an authority (probably via an unsigned transaction)
	Authority,
}

/// The result of an election round.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct ElectionResult<AccountId, Balance: HasCompact> {
	/// Flat list of validators who have been elected.
	elected_stashes: Vec<AccountId>,
	/// Flat list of new exposures, to be updated in the [`Exposure`] storage.
	exposures: Vec<(AccountId, Exposure<AccountId, Balance>)>,
	/// Type of the result. This is kept on chain only to track and report the best score's
	/// submission type. An optimisation can could remove this.
	compute: ElectionCompute,
}

/// The status of the upcoming (offchain) election.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub enum ElectionStatus<BlockNumber> {
	/// Nothing has and will happen for now. submission window is not open.
	Closed,
	/// The submission window has been open since the contained block number.
	Open(BlockNumber),
}

impl<BlockNumber> Default for ElectionStatus<BlockNumber> {
	fn default() -> Self {
		Self::Closed
	}
}

/// Means for interacting with a specialized version of the `session` trait.
///
/// This is needed because `Staking` sets the `ValidatorIdOf` of the `pallet_session::Trait`
pub trait SessionInterface<AccountId>: frame_system::Trait {
	/// Disable a given validator by stash ID.
	///
	/// Returns `true` if new era should be forced at the end of this session.
	/// This allows preventing a situation where there is too many validators
	/// disabled and block production stalls.
	fn disable_validator(validator: &AccountId) -> Result<bool, ()>;
	/// Get the validators from session.
	fn validators() -> Vec<AccountId>;
	/// Prune historical session tries up to but not including the given index.
	fn prune_historical_up_to(up_to: SessionIndex);
	/// Current session index.
	fn current_index() -> SessionIndex;
}

impl<T: Trait> SessionInterface<<T as frame_system::Trait>::AccountId> for T where
	T: pallet_session::Trait<ValidatorId = <T as frame_system::Trait>::AccountId>,
	T: pallet_session::historical::Trait<
		FullIdentification = Exposure<<T as frame_system::Trait>::AccountId, BalanceOf<T>>,
		FullIdentificationOf = ExposureOf<T>,
	>,
	T::SessionHandler: pallet_session::SessionHandler<<T as frame_system::Trait>::AccountId>,
	T::SessionManager: pallet_session::SessionManager<<T as frame_system::Trait>::AccountId>,
	T::ValidatorIdOf: Convert<<T as frame_system::Trait>::AccountId, Option<<T as frame_system::Trait>::AccountId>>,
{
	fn disable_validator(validator: &<T as frame_system::Trait>::AccountId) -> Result<bool, ()> {
		<pallet_session::Module<T>>::disable(validator)
	}

	fn validators() -> Vec<<T as frame_system::Trait>::AccountId> {
		<pallet_session::Module<T>>::validators()
	}

	fn prune_historical_up_to(up_to: SessionIndex) {
		<pallet_session::historical::Module<T>>::prune_up_to(up_to);
	}

	fn current_index() -> SessionIndex {
		<pallet_session::Module<T>>::current_index()
	}
}

pub trait Trait: frame_system::Trait {
	/// The staking balance.
	type Currency: LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;

	/// Time used for computing era duration.
	type Time: Time;

	/// Convert a balance into a number used for election calculation.
	/// This must fit into a `u64` but is allowed to be sensibly lossy.
	/// TODO: #1377
	/// The backward convert should be removed as the new Phragmen API returns ratio.
	/// The post-processing needs it but will be moved to off-chain. TODO: #2908
	type CurrencyToVote: Convert<BalanceOf<Self>, u64> + Convert<u128, BalanceOf<Self>>;

	/// Tokens have been minted and are unused for validator-reward.
	type RewardRemainder: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// Handler for the unbalanced reduction when slashing a staker.
	type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced increment when rewarding a staker.
	type Reward: OnUnbalanced<PositiveImbalanceOf<Self>>;

	/// Number of sessions per era.
	type SessionsPerEra: Get<SessionIndex>;

	/// Number of eras that staked funds must remain bonded for.
	type BondingDuration: Get<EraIndex>;

	/// Number of eras that slashes are deferred by, after computation. This
	/// should be less than the bonding duration. Set to 0 if slashes should be
	/// applied immediately, without opportunity for intervention.
	type SlashDeferDuration: Get<EraIndex>;

	/// The origin which can cancel a deferred slash. Root can always do this.
	type SlashCancelOrigin: EnsureOrigin<Self::Origin>;

	/// Interface for interacting with a session module.
	type SessionInterface: self::SessionInterface<Self::AccountId>;

	/// The NPoS reward curve to use.
	type RewardCurve: Get<&'static PiecewiseLinear<'static>>;

	/// Something that can predict the next session change.
	type NextSessionChange: EstimateNextSessionChange<Self::BlockNumber>;

	/// How many blocks ahead of the era do we try to run the phragmen offchain? Setting this to
	/// zero will disable the offchain compute and only on-chain seq-phragmen will be used.
	type ElectionLookahead: Get<Self::BlockNumber>;

	/// The overarching call type.
	type Call: From<Call<Self>> + IsSubType<Module<Self>, Self> + Clone;

	/// A transaction submitter.
	type SubmitTransaction: SubmitUnsignedTransaction<Self, <Self as Trait>::Call>;

	/// Key type used to sign and verify transaction.
	type KeyType: RuntimeAppPublic + Member + Parameter + Default;
}

/// Mode of era-forcing.
#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum Forcing {
	/// Not forcing anything - just let whatever happen.
	NotForcing,
	/// Force a new era, then reset to `NotForcing` as soon as it is done.
	ForceNew,
	/// Avoid a new era indefinitely.
	ForceNone,
	/// Force a new era at the end of all sessions indefinitely.
	ForceAlways,
}

impl Default for Forcing {
	fn default() -> Self { Forcing::NotForcing }
}

decl_storage! {
	trait Store for Module<T: Trait> as Staking {
		/// The ideal number of staking participants.
		pub ValidatorCount get(fn validator_count) config(): u32;
		/// Minimum number of staking participants before emergency conditions are imposed.
		pub MinimumValidatorCount get(fn minimum_validator_count) config():
			u32 = DEFAULT_MINIMUM_VALIDATOR_COUNT;

		/// Any validators that may never be slashed or forcibly kicked. It's a Vec since they're
		/// easy to initialize and the performance hit is minimal (we expect no more than four
		/// invulnerables) and restricted to testnets.
		pub Invulnerables get(fn invulnerables) config(): Vec<T::AccountId>;

		/// Map from all locked "stash" accounts to the controller account.
		pub Bonded get(fn bonded): map hasher(blake2_256) T::AccountId => Option<T::AccountId>;
		/// Map from all (unlocked) "controller" accounts to the info regarding the staking.
		pub Ledger get(fn ledger):
			map hasher(blake2_256) T::AccountId
			=> Option<StakingLedger<T::AccountId, BalanceOf<T>>>;

		/// Where the reward payment should be made. Keyed by stash.
		pub Payee get(fn payee): map hasher(blake2_256) T::AccountId => RewardDestination;

		/// The map from (wannabe) validator stash key to the preferences of that validator.
		pub Validators get(fn validators):
			linked_map hasher(blake2_256) T::AccountId => ValidatorPrefs;

		/// The map from nominator stash key to the set of stash keys of all validators to nominate.
		///
		/// NOTE: is private so that we can ensure upgraded before all typical accesses.
		/// Direct storage APIs can still bypass this protection.
		Nominators get(fn nominators):
			linked_map hasher(blake2_256) T::AccountId => Option<Nominations<T::AccountId>>;

		/// Nominators for a particular account that is in action right now. You can't iterate
		/// through validators here, but you can find them in the Session module.
		///
		/// This is keyed by the stash account.
		pub Stakers get(fn stakers):
			map hasher(blake2_256) T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		/// Snapshot of validators at the beginning of the current election window. This should only
		/// have a value when [`EraElectionStatus`] == `ElectionStatus::Open(_)`.
		pub SnapshotValidators get(fn snapshot_validators): Option<Vec<T::AccountId>>;

		/// Snapshot of nominators at the beginning of the current election window. This should only
		/// have a value when [`EraElectionStatus`] == `ElectionStatus::Open(_)`.
		pub SnapshotNominators get(fn snapshot_nominators): Option<Vec<T::AccountId>>;

		/// The currently elected validator set keyed by stash account ID.
		pub CurrentElected get(fn current_elected): Vec<T::AccountId>;

		/// The current set of staking keys.
		pub Keys get(fn keys): Vec<T::KeyType>;

		/// The next validator set. At the end of an era, if this is available (potentially from the
		/// result of an offchain worker), it is immediately used. Otherwise, the on-chain election
		/// is executed.
		pub QueuedElected get(fn queued_elected): Option<ElectionResult<T::AccountId, BalanceOf<T>>>;

		/// The score of the current [`QueuedElected`].
		pub QueuedScore get(fn queued_score): Option<PhragmenScore>;

		/// Flag to control the execution of the offchain election.
		pub EraElectionStatus get(fn era_election_status): ElectionStatus<T::BlockNumber>;

		/// The current era index.
		pub CurrentEra get(fn current_era) config(): EraIndex;

		/// The start of the current era.
		pub CurrentEraStart get(fn current_era_start): MomentOf<T>;

		/// The session index at which the current era started.
		pub CurrentEraStartSessionIndex get(fn current_era_start_session_index): SessionIndex;

		/// Rewards for the current era. Using indices of current elected set.
		CurrentEraPointsEarned get(fn current_era_reward): EraPoints;

		/// The amount of balance actively at stake for each validator slot, currently.
		///
		/// This is used to derive rewards and punishments.
		pub SlotStake get(fn slot_stake) build(|config: &GenesisConfig<T>| {
			config.stakers.iter().map(|&(_, _, value, _)| value).min().unwrap_or_default()
		}): BalanceOf<T>;

		/// Mode of era forcing.
		pub ForceEra get(fn force_era) config(): Forcing;

		/// The percentage of the slash that is distributed to reporters.
		///
		/// The rest of the slashed value is handled by the `Slash`.
		pub SlashRewardFraction get(fn slash_reward_fraction) config(): Perbill;

		/// The amount of currency given to reporters of a slash event which was
		/// canceled by extraordinary circumstances (e.g. governance).
		pub CanceledSlashPayout get(fn canceled_payout) config(): BalanceOf<T>;

		/// All unapplied slashes that are queued for later.
		pub UnappliedSlashes:
			map hasher(blake2_256) EraIndex => Vec<UnappliedSlash<T::AccountId, BalanceOf<T>>>;

		/// A mapping from still-bonded eras to the first session index of that era.
		BondedEras: Vec<(EraIndex, SessionIndex)>;

		/// All slashing events on validators, mapped by era to the highest slash proportion
		/// and slash value of the era.
		ValidatorSlashInEra:
			double_map hasher(blake2_256) EraIndex, hasher(twox_128) T::AccountId
			=> Option<(Perbill, BalanceOf<T>)>;

		/// All slashing events on nominators, mapped by era to the highest slash value of the era.
		NominatorSlashInEra:
			double_map hasher(blake2_256) EraIndex, hasher(twox_128) T::AccountId
			=> Option<BalanceOf<T>>;

		/// Slashing spans for stash accounts.
		SlashingSpans: map hasher(blake2_256) T::AccountId => Option<slashing::SlashingSpans>;

		/// Records information about the maximum slash of a stash within a slashing span,
		/// as well as how much reward has been paid out.
		SpanSlash:
			map hasher(blake2_256) (T::AccountId, slashing::SpanIndex)
			=> slashing::SpanRecord<BalanceOf<T>>;

		/// The earliest era for which we have a pending, unapplied slash.
		EarliestUnappliedSlash: Option<EraIndex>;
	}
	add_extra_genesis {
		config(stakers):
			Vec<(T::AccountId, T::AccountId, BalanceOf<T>, StakerStatus<T::AccountId>)>;
		build(|config: &GenesisConfig<T>| {
			for &(ref stash, ref controller, balance, ref status) in &config.stakers {
				assert!(
					T::Currency::free_balance(&stash) >= balance,
					"Stash does not have enough balance to bond."
				);
				let _ = <Module<T>>::bond(
					T::Origin::from(Some(stash.clone()).into()),
					T::Lookup::unlookup(controller.clone()),
					balance,
					RewardDestination::Staked,
				);
				let _ = match status {
					StakerStatus::Validator => {
						<Module<T>>::validate(
							T::Origin::from(Some(controller.clone()).into()),
							Default::default(),
						)
					},
					StakerStatus::Nominator(votes) => {
						<Module<T>>::nominate(
							T::Origin::from(Some(controller.clone()).into()),
							votes.iter().map(|l| T::Lookup::unlookup(l.clone())).collect(),
						)
					}, _ => Ok(())
				};
			}
		});
	}
}

decl_event!(
	pub enum Event<T> where Balance = BalanceOf<T>, <T as frame_system::Trait>::AccountId {
		/// All validators have been rewarded by the first balance; the second is the remainder
		/// from the maximum amount of reward.
		Reward(Balance, Balance),
		/// One validator (and its nominators) has been slashed by the given amount.
		Slash(AccountId, Balance),
		/// An old slashing report from a prior era was discarded because it could
		/// not be processed.
		OldSlashingReportDiscarded(SessionIndex),
		/// A new set of stakers was elected with the given computation method.
		StakingElection(ElectionCompute),
	}
);

decl_error! {
	/// Error for the staking module.
	pub enum Error for Module<T: Trait> {
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
		/// Can not bond with value less than minimum balance.
		InsufficientValue,
		/// Can not schedule more unlock chunks.
		NoMoreChunks,
		/// Can not rebond without unlocking chunks.
		NoUnlockChunk,
		/// Attempting to target a stash that still has funds.
		FundedTarget,
		/// The submitted result is received out of the open window.
		PhragmenEarlySubmission,
		/// The submitted result is not as good as the one stored on chain.
		PhragmenWeakSubmission,
		/// The snapshot data of the current window is missing.
		SnapshotUnavailable,
		/// Incorrect number of winners were presented.
		PhragmenBogusWinnerCount,
		/// One of the submitted winners is not an active candidate on chain (index is out of range
		/// in snapshot).
		PhragmenBogusWinner,
		/// Error while building the assignment type from the compact. This can happen if an index
		/// is invalid, or if the weights _overflow_.
		PhragmenBogusCompact,
		/// One of the submitted nominators is not an active nominator on chain. DEPRECATED.
		PhragmenBogusNominator,
		/// One of the submitted nominators has an edge to which they have not voted on chain.
		PhragmenBogusNomination,
		/// A self vote must only be originated from a validator to ONLY themselves.
		PhragmenBogusSelfVote,
		/// The submitted result has unknown edges that are not among the presented winners.
		PhragmenBogusEdge,
		/// The claimed score does not match with the one computed from the data.
		PhragmenBogusScore,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Number of sessions per era.
		const SessionsPerEra: SessionIndex = T::SessionsPerEra::get();

		/// Number of eras that staked funds must remain bonded for.
		const BondingDuration: EraIndex = T::BondingDuration::get();

		type Error = Error<T>;

		fn deposit_event() = default;

		/// Does the following:
		///
		/// 1. potential storage migration
		/// 2. sets `ElectionStatus` to `Open(now)` where `now` is the block number at which
		///    the election window has opened. The offchain worker, if applicable, will execute at
		///    the end of the current block. `submit_election_solution` will accept solutions from
		///    this block until the end of the era.
		fn on_initialize(now: T::BlockNumber) {
			Self::ensure_storage_upgraded();
			if
				// if we don't have any ongoing offchain compute.
				Self::era_election_status() == ElectionStatus::Closed &&
				// and an era is about to be changed.
				Self::is_current_session_final()
			{
				let next_session_change =
					T::NextSessionChange::estimate_next_session_change(now);
				if let Some(remaining) = next_session_change.checked_sub(&now) {
					if remaining <= T::ElectionLookahead::get() && !remaining.is_zero() {
						// create snapshot.
						if Self::create_stakers_snapshot() {
							// Set the flag to make sure we don't waste any compute here in the same era
							// after we have triggered the offline compute.
							<EraElectionStatus<T>>::put(
								ElectionStatus::<T::BlockNumber>::Open(now)
							);
							debug::native::info!(
								target: "staking",
								"Election window is Open({:?}). Snapshot created",
								now,
							);
						} else {
							debug::native::warn!(
								target: "staking",
								"Failed to create snapshot at {:?}. Election window will remain closed.",
								now,
							);
						}

					}
				}
			}
		}

		/// Check if the current block number is the one at which the election window has been set
		/// to open. If so, it runs the offchain worker code.
		fn offchain_worker(now: T::BlockNumber) {
			debug::RuntimeLogger::init();
			use offchain_election::{set_check_offchain_execution_status, compute_offchain_election};

			let window_open =
				Self::era_election_status() == ElectionStatus::<T::BlockNumber>::Open(now);

			if window_open {
				let offchain_status = set_check_offchain_execution_status::<T>(now);
				if let Err(why) = offchain_status {
					debug::native::warn!(
						target: "staking",
						"skipping offchain call in open election window due to [{}]",
						why,
					);
				} else {
					if let Err(e) = compute_offchain_election::<T>() {
						debug::native::warn!(
							target: "staking",
							"Error in phragmen offchain worker call: {:?}",
							e,
						);
					};
				}
			}
		}

		fn on_finalize() {
			// Set the start of the first era.
			if !<CurrentEraStart<T>>::exists() {
				<CurrentEraStart<T>>::put(T::Time::now());
			}
		}

		/// Take the origin account as a stash and lock up `value` of its balance. `controller` will
		/// be the account that controls it.
		///
		/// `value` must be more than the `minimum_balance` specified by `T::Currency`.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash account.
		///
		/// # <weight>
		/// - Independent of the arguments. Moderate complexity.
		/// - O(1).
		/// - Three extra DB entries.
		///
		/// NOTE: Two of the storage writes (`Self::bonded`, `Self::payee`) are _never_ cleaned
		/// unless the `origin` falls below _existential deposit_ and gets removed as dust.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn bond(origin,
			controller: <T::Lookup as StaticLookup>::Source,
			#[compact] value: BalanceOf<T>,
			payee: RewardDestination,
		) {
			let stash = ensure_signed(origin)?;

			if <Bonded<T>>::contains_key(&stash) {
				Err(Error::<T>::AlreadyBonded)?
			}

			let controller = T::Lookup::lookup(controller)?;

			if <Ledger<T>>::contains_key(&controller) {
				Err(Error::<T>::AlreadyPaired)?
			}

			// reject a bond which is considered to be _dust_.
			if value < T::Currency::minimum_balance() {
				Err(Error::<T>::InsufficientValue)?
			}

			// You're auto-bonded forever, here. We might improve this by only bonding when
			// you actually validate/nominate and remove once you unbond __everything__.
			<Bonded<T>>::insert(&stash, &controller);
			<Payee<T>>::insert(&stash, payee);

			system::Module::<T>::inc_ref(&stash);

			let stash_balance = T::Currency::free_balance(&stash);
			let value = value.min(stash_balance);
			let item = StakingLedger { stash, total: value, active: value, unlocking: vec![] };
			Self::update_ledger(&controller, &item);
		}

		/// Add some extra amount that have appeared in the stash `free_balance` into the balance up
		/// for staking.
		///
		/// Use this if there are additional funds in your stash account that you wish to bond.
		/// Unlike [`bond`] or [`unbond`] this function does not impose any limitation on the amount
		/// that can be added.
		///
		/// The dispatch origin for this call must be _Signed_ by the stash, not the controller.
		///
		/// # <weight>
		/// - Independent of the arguments. Insignificant complexity.
		/// - O(1).
		/// - One DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn bond_extra(origin, #[compact] max_additional: BalanceOf<T>) {
			let stash = ensure_signed(origin)?;

			let controller = Self::bonded(&stash).ok_or(Error::<T>::NotStash)?;
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;

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
		/// T::Currency::minimum_balance(), then it is increased to the full amount.
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
		#[weight = SimpleDispatchInfo::FixedNormal(400_000)]
		fn unbond(origin, #[compact] value: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let mut ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			ensure!(
				ledger.unlocking.len() < MAX_UNLOCKING_CHUNKS,
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
		/// - Could be dependent on the `origin` argument and how much `unlocking` chunks exist.
		///  It implies `consolidate_unlocked` which loops over `Ledger.unlocking`, which is
		///  indirectly user-controlled. See [`unbond`] for more detail.
		/// - Contains a limited number of reads, yet the size of which could be large based on `ledger`.
		/// - Writes are limited to the `origin` account key.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(400_000)]
		fn withdraw_unbonded(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let ledger = ledger.consolidate_unlocked(Self::current_era());

			if ledger.unlocking.is_empty() && ledger.active.is_zero() {
				// This account must have called `unbond()` with some value that caused the active
				// portion to fall below existential deposit + will have no more unlocking chunks
				// left. We can now safely remove this.
				let stash = ledger.stash;
				// remove all staking-related information.
				Self::kill_stash(&stash)?;
				// remove the lock.
				T::Currency::remove_lock(STAKING_ID, &stash);
			} else {
				// This was the consequence of a partial unbond. just update the ledger and move on.
				Self::update_ledger(&controller, &ledger);
			}
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
		#[weight = SimpleDispatchInfo::FixedNormal(750_000)]
		fn validate(origin, prefs: ValidatorPrefs) {
			Self::ensure_storage_upgraded();

			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = &ledger.stash;
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
		/// which is capped at Compact::LIMIT.
		/// - Both the reads and writes follow a similar pattern.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(750_000)]
		fn nominate(origin, targets: Vec<<T::Lookup as StaticLookup>::Source>) {
			Self::ensure_storage_upgraded();

			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = &ledger.stash;
			ensure!(!targets.is_empty(), Error::<T>::EmptyTargets);
			let targets = targets.into_iter()
				.take(<Compact as VotingLimit>::LIMIT)
				.map(|t| T::Lookup::lookup(t))
				.collect::<result::Result<Vec<T::AccountId>, _>>()?;

			let nominations = Nominations {
				targets,
				submitted_in: Self::current_era(),
				suppressed: false,
			};

			<Validators<T>>::remove(stash);
			<Nominators<T>>::insert(stash, &nominations);
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
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn chill(origin) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			Self::chill_stash(&ledger.stash);
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
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn set_payee(origin, payee: RewardDestination) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			let stash = &ledger.stash;
			<Payee<T>>::insert(stash, payee);
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
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(750_000)]
		fn set_controller(origin, controller: <T::Lookup as StaticLookup>::Source) {
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
		}

		/// The ideal number of validators.
		#[weight = SimpleDispatchInfo::FixedNormal(5_000)]
		fn set_validator_count(origin, #[compact] new: u32) {
			ensure_root(origin)?;
			ValidatorCount::put(new);
		}

		// ----- Root calls.

		/// Force there to be no new eras indefinitely.
		///
		/// # <weight>
		/// - No arguments.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(5_000)]
		fn force_no_eras(origin) {
			ensure_root(origin)?;
			ForceEra::put(Forcing::ForceNone);
		}

		/// Force there to be a new era at the end of the next session. After this, it will be
		/// reset to normal (non-forced) behaviour.
		///
		/// # <weight>
		/// - No arguments.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(5_000)]
		fn force_new_era(origin) {
			ensure_root(origin)?;
			ForceEra::put(Forcing::ForceNew);
		}

		/// Set the validators who cannot be slashed (if any).
		#[weight = SimpleDispatchInfo::FixedNormal(5_000)]
		fn set_invulnerables(origin, validators: Vec<T::AccountId>) {
			ensure_root(origin)?;
			<Invulnerables<T>>::put(validators);
		}

		/// Force a current staker to become completely unstaked, immediately.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn force_unstake(origin, stash: T::AccountId) {
			ensure_root(origin)?;

			// remove all staking-related information.
			Self::kill_stash(&stash)?;

			// remove the lock.
			T::Currency::remove_lock(STAKING_ID, &stash);
		}

		/// Force there to be a new era at the end of sessions indefinitely.
		///
		/// # <weight>
		/// - One storage write
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(5_000)]
		fn force_new_era_always(origin) {
			ensure_root(origin)?;
			ForceEra::put(Forcing::ForceAlways);
		}

		/// Cancel enactment of a deferred slash. Can be called by either the root origin or
		/// the `T::SlashCancelOrigin`.
		/// passing the era and indices of the slashes for that era to kill.
		///
		/// # <weight>
		/// - One storage write.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn cancel_deferred_slash(origin, era: EraIndex, slash_indices: Vec<u32>) {
			T::SlashCancelOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			let mut slash_indices = slash_indices;
			slash_indices.sort_unstable();
			let mut unapplied = <Self as Store>::UnappliedSlashes::get(&era);

			for (removed, index) in slash_indices.into_iter().enumerate() {
				let index = index as usize;

				// if `index` is not duplicate, `removed` must be <= index.
				ensure!(removed <= index, Error::<T>::DuplicateIndex);

				// all prior removals were from before this index, since the
				// list is sorted.
				let index = index - removed;
				ensure!(index < unapplied.len(), Error::<T>::InvalidSlashIndex);

				unapplied.remove(index);
			}

			<Self as Store>::UnappliedSlashes::insert(&era, &unapplied);
		}

		/// Rebond a portion of the stash scheduled to be unlocked.
		///
		/// # <weight>
		/// - Time complexity: O(1). Bounded by `MAX_UNLOCKING_CHUNKS`.
		/// - Storage changes: Can't increase storage, only decrease it.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn rebond(origin, #[compact] value: BalanceOf<T>) {
			let controller = ensure_signed(origin)?;
			let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
			ensure!(
				ledger.unlocking.len() > 0,
				Error::<T>::NoUnlockChunk,
			);

			let ledger = ledger.rebond(value);
			Self::update_ledger(&controller, &ledger);
		}

		/// Remove all data structure concerning a staker/stash once its balance is zero.
		/// This is essentially equivalent to `withdraw_unbonded` except it can be called by anyone
		/// and the target `stash` must have no funds left.
		///
		/// This can be called from any origin.
		///
		/// - `stash`: The stash account to reap. Its balance must be zero.
		fn reap_stash(_origin, stash: T::AccountId) {
			Self::ensure_storage_upgraded();
			ensure!(T::Currency::total_balance(&stash).is_zero(), Error::<T>::FundedTarget);
			Self::kill_stash(&stash)?;
			T::Currency::remove_lock(STAKING_ID, &stash);
		}

		/// Submit a phragmen result to the chain. If the solution:
		///
		/// 1. is valid
		/// 2. has a better score than a potentially existing solution on chain
		///
		/// then, it will be put on chain.
		///
		/// A solution consists of two pieces of data:
		///
		/// 1. `winners`: a flat vector of all the winners of the round.
		/// 2. `assignments`: the compact version of an assignment vector that encodes the edge
		///    weights.
		///
		/// Both of which may be computed using [`phragmen`], or any other algorithm.
		///
		/// Additionally, the submitter must provide:
		///
		/// - The score that they claim their solution has.
		///
		/// Both validators and nominators will be represented by indices in the solution. The
		/// indices should respect the corresponding types ([`ValidatorIndex`] and
		/// [`NominatorIndex`]). Moreover, they should be valid when used to index into
		/// [`SnapshotValidators`] and [`SnapshotNominators`]. Any invalid index will cause the
		/// solution to be rejected.
		///
		/// A solution is valid if:
		///
		/// 0. It is submitted when [`EraElectionStatus`] is `Open`.
		/// 1. Its claimed score is equal to the score computed on-chain.
		/// 2. Presents the correct number of winners.
		/// 3. All indexes must be value according to the snapshot vectors. All edge values must
		///    also be correct and should not overflow the granularity of the ratio type (i.e. 256
		///    or billion).
		/// 4. For each edge, all targets are actually nominated by the voter.
		/// 5. Has correct self-votes.
		///
		/// A solutions score is consisted of 3 parameters:
		///
		/// 1. `min { support.total }` for each support of a winner. This value should be maximized.
		/// 2. `sum { support.total }` for each support of a winner. This value should be minimized.
		/// 3. `sum { support.total^2 }` for each support of a winner. This value should be
		///    minimized (to ensure less variance)
		///
		/// # <weight>
		/// E: number of edges.
		/// m: size of winner committee.
		/// n: number of nominators.
		/// d: edge degree (16 for now)
		/// v: number of on-chain validator candidates.
		///
		/// NOTE: given a solution which is reduced, we can enable a new check the ensure `|E| < n +
		/// m`.
		///
		/// major steps (all done in `check_and_replace_solution`):
		///
		/// - Storage: O(1) read `ElectionStatus`.
		/// - Storage: O(1) read `PhragmenScore`.
		/// - Storage: O(1) read `ValidatorCount`.
		/// - Storage: O(1) length read from `SnapshotValidators`.
		/// - Storage: O(v) reads of `AccountId`.
		/// - Memory: O(m) iterations to map winner index to validator id.
		/// - Storage: O(n) reads `AccountId`.
		/// - Memory: O(n + m) reads to map index to `AccountId` for un-compact.
		/// - Storage: O(e) accountid reads from `Nomination` to read correct nominations.
		/// - Storage: O(e) calls into `slashable_balance_of_extended` to convert ratio to staked.
		/// - Memory: build_support_map. O(e).
		/// - Memory: evaluate_support: O(E).
		/// - Storage: O(e) writes to `QueuedElected`.
		/// - Storage: O(1) write to `QueuedScore`
		///
		/// The weight of this call is 1/10th of the blocks total weight.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000_000)]
		pub fn submit_election_solution(
			origin,
			winners: Vec<ValidatorIndex>,
			compact_assignments: Compact,
			score: PhragmenScore,
		) {
			let _who = ensure_signed(origin)?;
			Self::check_and_replace_solution(
				winners,
				compact_assignments,
				ElectionCompute::Signed,
				score,
			)?
		}

		/// Unsigned version of `submit_election_solution`. Will only be accepted from those who are
		/// in the current validator set.
		#[weight = SimpleDispatchInfo::FixedNormal(100_000_000)]
		pub fn submit_election_solution_unsigned(
			origin,
			winners: Vec<ValidatorIndex>,
			compact_assignments: Compact,
			score: PhragmenScore,
			// already used and checked in ValidateUnsigned.
			_validator_index: u32,
			_signature: <T::KeyType as RuntimeAppPublic>::Signature,
		) {
			ensure_none(origin)?;
			Self::check_and_replace_solution(
				winners,
				compact_assignments,
				ElectionCompute::Authority,
				score,
			)?
		}
	}
}

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	/// The total balance that can be slashed from a stash account as of right now.
	pub fn slashable_balance_of(stash: &T::AccountId) -> BalanceOf<T> {
		Self::bonded(stash).and_then(Self::ledger).map(|l| l.active).unwrap_or_default()
	}

	/// internal impl of [`slashable_balance_of`] that returns [`ExtendedBalance`].
	fn slashable_balance_of_extended(stash: &T::AccountId) -> ExtendedBalance {
		<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			Self::slashable_balance_of(stash)
		) as ExtendedBalance
	}

	/// returns true if the end of the current session leads to an era change.
	fn is_current_session_final() -> bool {
		let current_index = T::SessionInterface::current_index();
		let era_length = current_index
			.checked_sub(Self::current_era_start_session_index())
			.unwrap_or(0);
		let session_per_era = T::SessionsPerEra::get()
			.checked_sub(One::one())
			.unwrap_or(0);
		era_length >= session_per_era
	}

	/// Dump the list of validators and nominators into vectors and keep them on-chain.
	///
	/// This data is used to efficiently evaluate election results. returns `true` if the operation
	/// is successful.
	fn create_stakers_snapshot() -> bool {
		let validators = <Validators<T>>::enumerate().map(|(v, _)| v).collect::<Vec<_>>();
		let mut nominators = <Nominators<T>>::enumerate().map(|(n, _)| n).collect::<Vec<_>>();

		// all validators nominate themselves;
		nominators.extend(validators.clone());

		let num_validators = validators.len() as u32;
		let num_nominators = nominators.len() as u32;
		if num_validators > MAX_VALIDATORS || num_nominators > MAX_NOMINATORS {
			debug::native::warn!(
				target: "staking",
				"Snapshot size too big [{} <> {}][{} <> {}].",
				num_validators,
				MAX_VALIDATORS,
				num_nominators,
				MAX_NOMINATORS,
			);
			false
		} else {
			<SnapshotValidators<T>>::put(validators);
			<SnapshotNominators<T>>::put(nominators);
			true
		}

	}

	/// Clears both snapshots of stakers.
	fn kill_stakers_snapshot() {
		<SnapshotValidators<T>>::kill();
		<SnapshotNominators<T>>::kill();
	}

	// MUTABLES (DANGEROUS)

	/// Update the ledger for a controller. This will also update the stash lock. The lock will
	/// will lock the entire funds except paying for further transactions.
	fn update_ledger(
		controller: &T::AccountId,
		ledger: &StakingLedger<T::AccountId, BalanceOf<T>>
	) {
		T::Currency::set_lock(
			STAKING_ID,
			&ledger.stash,
			ledger.total,
			WithdrawReasons::all(),
		);
		<Ledger<T>>::insert(controller, ledger);
	}

	/// Chill a stash account.
	fn chill_stash(stash: &T::AccountId) {
		<Validators<T>>::remove(stash);
		<Nominators<T>>::remove(stash);
	}

	/// Ensures storage is upgraded to most recent necessary state.
	///
	/// Right now it's a no-op as all networks that are supported by Substrate Frame Core are
	/// running with the latest staking storage scheme.
	fn ensure_storage_upgraded() {}

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
	fn reward_validator(stash: &T::AccountId, reward: BalanceOf<T>) -> PositiveImbalanceOf<T> {
		let off_the_table = Self::validators(stash).commission * reward;
		let reward = reward.saturating_sub(off_the_table);
		let mut imbalance = <PositiveImbalanceOf<T>>::zero();
		let validator_cut = if reward.is_zero() {
			Zero::zero()
		} else {
			let exposure = Self::stakers(stash);
			let total = exposure.total.max(One::one());

			for i in &exposure.others {
				let per_u64 = Perbill::from_rational_approximation(i.value, total);
				imbalance.maybe_subsume(Self::make_payout(&i.who, per_u64 * reward));
			}

			let per_u64 = Perbill::from_rational_approximation(exposure.own, total);
			per_u64 * reward
		};

		imbalance.maybe_subsume(Self::make_payout(stash, validator_cut + off_the_table));

		imbalance
	}

	/// Session has just ended. Provide the validator set for the next session if it's an era-end.
	fn new_session(session_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		let era_length = session_index
			.checked_sub(Self::current_era_start_session_index())
			.unwrap_or(0);
		match ForceEra::get() {
			Forcing::ForceNew => ForceEra::kill(),
			Forcing::ForceAlways => (),
			Forcing::NotForcing if era_length >= T::SessionsPerEra::get() => (),
			_ => return None,
		}

		Self::new_era(session_index)
	}

	/// Initialize the first session (and consequently the first era)
	fn initial_session() -> Option<Vec<T::AccountId>> {
		// note: `CurrentEraStart` is set in `on_finalize` of the first block because now is not
		// available yet.
		CurrentEraStartSessionIndex::put(0);
		BondedEras::mutate(|bonded| bonded.push((0, 0)));
		Self::select_and_update_validators()
	}

	/// Checks a given solution and if correct and improved, writes it on chain as the queued result
	/// of the next round. This may be called by both a signed and an unsigned transaction.
	fn check_and_replace_solution(
		winners: Vec<ValidatorIndex>,
		compact_assignments: Compact,
		compute: ElectionCompute,
		claimed_score: PhragmenScore,
	) -> Result<(), Error<T>> {
		// discard early solutions
		match Self::era_election_status() {
			ElectionStatus::Closed => Err(Error::<T>::PhragmenEarlySubmission)?,
			ElectionStatus::Open(_) => { /* Open and no solutions received. Allowed. */ },
		}

		// assume the given score is valid. Is it better than what we have on-chain, if we have any?
		if let Some(queued_score) = Self::queued_score() {
			ensure!(
				is_score_better(queued_score, claimed_score),
				Error::<T>::PhragmenWeakSubmission,
			)
		}

		// Check that the number of presented winners is sane. Most often we have more candidates
		// that we need. Then it should be Self::validator_count(). Else it should be all the
		// candidates.
		let snapshot_length = <SnapshotValidators<T>>::decode_len()
			.map_err(|_| Error::<T>::SnapshotUnavailable)?;
		let desired_winners = Self::validator_count().min(snapshot_length as u32);
		ensure!(winners.len() as u32 == desired_winners, Error::<T>::PhragmenBogusWinnerCount);

		// decode snapshot validators.
		let snapshot_validators = Self::snapshot_validators()
			.ok_or(Error::<T>::SnapshotUnavailable)?;

		// check if all winners were legit; this is rather cheap. Replace with accountId.
		let winners = winners.into_iter().map(|widx| {
			snapshot_validators.get(widx as usize).cloned().ok_or(Error::<T>::PhragmenBogusWinner)
		}).collect::<Result<Vec<T::AccountId>, Error<T>>>()?;

		// decode the rest of the snapshot.
		let snapshot_nominators = <Module<T>>::snapshot_nominators()
			.ok_or(Error::<T>::SnapshotUnavailable)?;

		// helpers
		let nominator_at = |i: NominatorIndex| -> Option<T::AccountId> {
			// NOTE: we assume both `ValidatorIndex` and `NominatorIndex` are smaller than usize.
			snapshot_nominators.get(i as usize).cloned()
		};
		let validator_at = |i: ValidatorIndex| -> Option<T::AccountId> {
			// NOTE: we assume both `ValidatorIndex` and `NominatorIndex` are smaller than usize.
			snapshot_validators.get(i as usize).cloned()
		};

		// un-compact.
		let assignments = compact_assignments.into_assignment(
			nominator_at,
			validator_at,
		).map_err(|e| {
			debug::native::warn!(
				target: "staking",
				"un-compacting solution failed due to {:?}",
				e,
			);
			Error::<T>::PhragmenBogusCompact
		})?;

		// check all nominators actually including the claimed vote. Also check correct self votes.
		// Note that we assume all validators and nominators in `assignments` are properly bonded,
		// because they are coming from the snapshot via a given index.
		for Assignment { who, distribution } in assignments.iter() {
			let is_validator = <Validators<T>>::contains_key(&who);
			let maybe_nomination = Self::nominators(&who);

			if !(maybe_nomination.is_some() ^ is_validator) {
				// all of the indices must map to either a validator or a nominator. If this is ever
				// not the case, then the locking system of staking is most likely faulty, or we
				// have bigger problems.
				debug::native::error!(
					target: "staking",
					"detected an error in the staking locking and snapshot."
				);
				// abort.
				return Err(Error::<T>::PhragmenBogusNominator);
			}

			if !is_validator {
				// a normal vote
				let nomination = maybe_nomination.expect(
					"exactly one of maybe_validator and maybe_nomination is true. \
					is_validator is false; maybe_nomination is some; qed"
				);
				// NOTE: we don't really have to check here if the sum of all edges are the
				// nominator correct. Un-compacting assures this by definition.
				ensure!(
					distribution.into_iter().all(|(t, _)| {
						nomination.targets.iter().find(|&tt| tt == t).is_some()
					}),
					Error::<T>::PhragmenBogusNomination,
				);
			} else {
				// a self vote
				ensure!(distribution.len() == 1, Error::<T>::PhragmenBogusSelfVote);
				ensure!(distribution[0].0 == *who, Error::<T>::PhragmenBogusSelfVote);
				// defensive only. A compact assignment of length one does NOT encode the weight and
				// it is always created to be 100%.
				ensure!(
					distribution[0].1 == OffchainAccuracy::one(),
					Error::<T>::PhragmenBogusSelfVote,
				);
			}
		}

		// convert into staked assignments.
		let staked_assignments = sp_phragmen::assignment_ratio_to_staked(
			assignments,
			Self::slashable_balance_of_extended,
		);

		// build the support map thereof in order to evaluate.
		// OPTIMIZATION: loop to create the staked assignments but it would bloat the code. Okay for
		// now as it does not add to the complexity order.
		let (supports, num_error) = build_support_map::<T::AccountId>(
			&winners,
			&staked_assignments,
		);
		// This technically checks that all targets in all nominators were among the winners.
		ensure!(num_error == 0, Error::<T>::PhragmenBogusEdge);

		// Check if the score is the same as the claimed one.
		let submitted_score = evaluate_support(&supports);
		ensure!(submitted_score == claimed_score, Error::<T>::PhragmenBogusScore);

		// At last, alles Ok. Exposures and store the result.
		let to_balance = |e: ExtendedBalance|
			<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(e);

		let exposures = supports.into_iter().map(|(validator, support)| {
			let mut others = Vec::new();
			let mut own: BalanceOf<T> = Zero::zero();
			let mut total: BalanceOf<T> = Zero::zero();
			support.voters
				.into_iter()
				.map(|(target, weight)| (target, to_balance(weight)))
				.for_each(|(nominator, stake)| {
					if nominator == validator {
						own = own.saturating_add(stake);
					} else {
						others.push(IndividualExposure { who: nominator, value: stake });
					}
					total = total.saturating_add(stake);
				});
			let exposure = Exposure { own, others, total };

			(validator, exposure)
		}).collect::<Vec<(T::AccountId, Exposure<_, _>)>>();

		debug::native::info!(
			target: "staking",
			"A better solution has been validated and stored on chain.",
		);

		<QueuedElected<T>>::put(ElectionResult {
			elected_stashes: winners,
			compute,
			exposures,
		});
		QueuedScore::put(submitted_score);

		Ok(())
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens immediately before a session change to ensure that new validators
	/// get a chance to set their session keys.
	fn new_era(start_session_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		// Payout
		let points = CurrentEraPointsEarned::take();
		let now = T::Time::now();
		let previous_era_start = <CurrentEraStart<T>>::mutate(|v| {
			sp_std::mem::replace(v, now)
		});
		let era_duration = now - previous_era_start;
		if !era_duration.is_zero() {
			let validators = Self::current_elected();

			let validator_len: BalanceOf<T> = (validators.len() as u32).into();
			let total_rewarded_stake = Self::slot_stake() * validator_len;

			let (total_payout, max_payout) = inflation::compute_total_payout(
				&T::RewardCurve::get(),
				total_rewarded_stake.clone(),
				T::Currency::total_issuance(),
				// Duration of era; more than u64::MAX is rewarded as u64::MAX.
				era_duration.saturated_into::<u64>(),
			);

			let mut total_imbalance = <PositiveImbalanceOf<T>>::zero();

			for (v, p) in validators.iter().zip(points.individual.into_iter()) {
				if p != 0 {
					let reward = Perbill::from_rational_approximation(p, points.total) * total_payout;
					total_imbalance.subsume(Self::reward_validator(v, reward));
				}
			}

			let total_payout = total_imbalance.peek();

			let rest = max_payout.saturating_sub(total_payout);
			Self::deposit_event(RawEvent::Reward(total_payout, rest));

			T::Reward::on_unbalanced(total_imbalance);
			T::RewardRemainder::on_unbalanced(T::Currency::issue(rest));
		}

		// Increment current era.
		let current_era = CurrentEra::mutate(|s| { *s += 1; *s });

		CurrentEraStartSessionIndex::mutate(|v| {
			*v = start_session_index;
		});
		let bonding_duration = T::BondingDuration::get();

		BondedEras::mutate(|bonded| {
			bonded.push((current_era, start_session_index));

			if current_era > bonding_duration {
				let first_kept = current_era - bonding_duration;

				// prune out everything that's from before the first-kept index.
				let n_to_prune = bonded.iter()
					.take_while(|&&(era_idx, _)| era_idx < first_kept)
					.count();

				// kill slashing metadata.
				for (pruned_era, _) in bonded.drain(..n_to_prune) {
					slashing::clear_era_metadata::<T>(pruned_era);
				}

				if let Some(&(_, first_session)) = bonded.first() {
					T::SessionInterface::prune_historical_up_to(first_session);
				}
			}
		});

		// Reassign all Stakers.
		let maybe_new_validators = Self::select_and_update_validators();
		Self::apply_unapplied_slashes(current_era);

		maybe_new_validators
	}

	/// Apply previously-unapplied slashes on the beginning of a new era, after a delay.
	fn apply_unapplied_slashes(current_era: EraIndex) {
		let slash_defer_duration = T::SlashDeferDuration::get();
		<Self as Store>::EarliestUnappliedSlash::mutate(|earliest| if let Some(ref mut earliest) = earliest {
			let keep_from = current_era.saturating_sub(slash_defer_duration);
			for era in (*earliest)..keep_from {
				let era_slashes = <Self as Store>::UnappliedSlashes::take(&era);
				for slash in era_slashes {
					slashing::apply_slash::<T>(slash);
				}
			}

			*earliest = (*earliest).max(keep_from)
		})
	}

	/// Select the new validator set at the end of the era.
	///
	/// Runs [`try_do_phragmen`] and updates the following storage items:
	/// - [`EraElectionStatus`]: with `None`.
	/// - [`Stakers`]: with the new staker set.
	/// - [`SlotStake`]: with the new slot stake.
	/// - [`CurrentElected`]: with the new elected set.
	/// - [`SnapshotValidators`] and [`SnapshotNominators`] are both removed.
	///
	/// Internally, [`QueuedElected`], snapshots and [`QueuedScore`] are also consumed.
	///
	/// If the election has been successful, It passes the new set upwards.
	///
	/// This should only be called at the end of an era.
	fn select_and_update_validators() -> Option<Vec<T::AccountId>> {
		if let Some(ElectionResult::<T::AccountId, BalanceOf<T>> {
			elected_stashes,
			exposures,
			compute,
		}) = Self::try_do_phragmen() {
			// We have chosen the new validator set. Submission is no longer allowed.
			<EraElectionStatus<T>>::put(ElectionStatus::Closed);

			// kill the snapshots.
			Self::kill_stakers_snapshot();

			// Clear Stakers.
			for v in Self::current_elected().iter() {
				<Stakers<T>>::remove(v);
			}

			// Populate Stakers and write slot stake.
			let mut slot_stake: BalanceOf<T> = Bounded::max_value();
			exposures.into_iter().for_each(|(s, e)| {
				if e.total < slot_stake { slot_stake = e.total }
				<Stakers<T>>::insert(s, e);
			});

			// Update slot stake.
			<SlotStake<T>>::put(&slot_stake);

			// Update current elected.
			<CurrentElected<T>>::put(&elected_stashes);

			// emit event
			Self::deposit_event(RawEvent::StakingElection(compute));

			debug::native::info!(
				target: "staking",
				"new validator set of size {:?} has been elected via {:?}",
				elected_stashes.len(),
				compute,
			);

			Some(elected_stashes)
		} else {
			None
		}
	}

	/// Select a new validator set from the assembled stakers and their role preferences. It tries
	/// first to peek into [`QueuedElected`]. Otherwise, it runs a new phragmen.
	///
	/// If [`QueuedElected`] and [`QueuedScore`] exists, they are both removed. No further storage
	/// is updated.
	fn try_do_phragmen() -> Option<ElectionResult<T::AccountId, BalanceOf<T>>> {
		// a phragmen result from either a stored submission or locally executed one.
		let next_result = <QueuedElected<T>>::take().or_else(||
			Self::do_phragmen_with_post_processing::<ChainAccuracy>(ElectionCompute::OnChain)
		);

		// either way, kill this. We remove it here to make sure it always has teh exact same
		// lifetime as `QueuedElected`.
		QueuedScore::kill();

		next_result
	}

	/// Execute phragmen and return the new results. The edge weights are processed into  support
	/// values.
	///
	/// No storage item is updated.
	fn do_phragmen_with_post_processing<
		Accuracy: PerThing,
	>(
		compute: ElectionCompute,
	) -> Option<ElectionResult<T::AccountId, BalanceOf<T>>>
		where
			Accuracy: sp_std::ops::Mul<ExtendedBalance, Output=ExtendedBalance>,
			ExtendedBalance: From<<Accuracy as PerThing>::Inner>,
	{
		if let Some(phragmen_result) = Self::do_phragmen::<Accuracy>() {
			let elected_stashes = phragmen_result.winners.iter()
				.map(|(s, _)| s.clone())
				.collect::<Vec<T::AccountId>>();
			let assignments = phragmen_result.assignments;

			let staked_assignments = sp_phragmen::assignment_ratio_to_staked(
				assignments,
				Self::slashable_balance_of_extended,
			);

			let (supports, _) = build_support_map::<T::AccountId>(
				&elected_stashes,
				&staked_assignments,
			);

			let to_balance = |e: ExtendedBalance|
				<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(e);

			// collect exposures
			let exposures = supports.into_iter().map(|(validator, support)| {
				// build `struct exposure` from `support`
				let mut others = Vec::new();
				let mut own: BalanceOf<T> = Zero::zero();
				let mut total: BalanceOf<T> = Zero::zero();
				support.voters
					.into_iter()
					.map(|(nominator, weight)| (nominator, to_balance(weight)))
					.for_each(|(nominator, stake)| {
						if nominator == validator {
							own = own.saturating_add(stake);
						} else {
							others.push(IndividualExposure { who: nominator, value: stake });
						}
						total = total.saturating_add(stake);
					});
				let exposure = Exposure {
					own,
					others,
					// This might reasonably saturate and we cannot do much about it. The sum of
					// someone's stake might exceed the balance type if they have the maximum amount
					// of balance and receive some support. This is super unlikely to happen, yet we
					// simulate it in some tests.
					total,
				};

				(validator, exposure)
			}).collect::<Vec<(T::AccountId, Exposure<_, _>)>>();

			// In order to keep the property required by `n_session_ending` that we must return the
			// new validator set even if it's the same as the old, as long as any underlying
			// economic conditions have changed, we don't attempt to do any optimization where we
			// compare against the prior set.
			Some(ElectionResult::<T::AccountId, BalanceOf<T>> {
				elected_stashes,
				exposures,
				compute,
			})
		} else {
			// There were not enough candidates for even our minimal level of functionality. This is
			// bad. We should probably disable all functionality except for block production and let
			// the chain keep producing blocks until we can decide on a sufficiently substantial
			// set. TODO: #2494
			None
		}
	}

	/// Execute phragmen and return the new results. No post-processing is applied and the raw edge
	/// weights are returned.
	///
	/// Self votes are added and nominations before the most recent slashing span are reaped.
	///
	/// No storage item is updated.
	fn do_phragmen<Accuracy: PerThing>() -> Option<PhragmenResult<T::AccountId, Accuracy>> {
		let mut all_nominators: Vec<(T::AccountId, Vec<T::AccountId>)> = Vec::new();
		let all_validator_candidates_iter = <Validators<T>>::enumerate();
		let all_validators = all_validator_candidates_iter.map(|(who, _pref)| {
			// append self vote
			let self_vote = (who.clone(), vec![who.clone()]);
			all_nominators.push(self_vote);

			who
		}).collect::<Vec<T::AccountId>>();

		let nominator_votes = <Nominators<T>>::enumerate().map(|(nominator, nominations)| {
			let Nominations { submitted_in, mut targets, suppressed: _ } = nominations;

			// Filter out nomination targets which were nominated before the most recent
			// slashing span.
			targets.retain(|stash| {
				<Self as Store>::SlashingSpans::get(&stash).map_or(
					true,
					|spans| submitted_in >= spans.last_nonzero_slash(),
				)
			});

			(nominator, targets)
		});
		all_nominators.extend(nominator_votes);

		elect::<_, _, _, T::CurrencyToVote, Accuracy>(
			Self::validator_count() as usize,
			Self::minimum_validator_count().max(1) as usize,
			all_validators,
			all_nominators,
			Self::slashable_balance_of,
		)
	}

	/// Remove all associated data of a stash account from the staking system.
	///
	/// Assumes storage is upgraded before calling.
	///
	/// This is called:
	/// - after a `withdraw_unbond()` call that frees all of a stash's bonded balance.
	/// - through `reap_stash()` if the balance has fallen to zero (through slashing).
	fn kill_stash(stash: &T::AccountId) -> DispatchResult {
		let controller = Bonded::<T>::take(stash).ok_or(Error::<T>::NotStash)?;
		<Ledger<T>>::remove(&controller);

		<Payee<T>>::remove(stash);
		<Validators<T>>::remove(stash);
		<Nominators<T>>::remove(stash);

		slashing::clear_stash_metadata::<T>(stash);

		system::Module::<T>::dec_ref(stash);

		Ok(())
	}

	/// Add reward points to validators using their stash account ID.
	///
	/// Validators are keyed by stash account ID and must be in the current elected set.
	///
	/// For each element in the iterator the given number of points in u32 is added to the
	/// validator, thus duplicates are handled.
	///
	/// At the end of the era each the total payout will be distributed among validator
	/// relatively to their points.
	///
	/// COMPLEXITY: Complexity is `number_of_validator_to_reward x current_elected_len`.
	/// If you need to reward lots of validator consider using `reward_by_indices`.
	pub fn reward_by_ids(validators_points: impl IntoIterator<Item = (T::AccountId, u32)>) {
		CurrentEraPointsEarned::mutate(|rewards| {
			let current_elected = <Module<T>>::current_elected();
			for (validator, points) in validators_points.into_iter() {
				if let Some(index) = current_elected.iter()
					.position(|elected| *elected == validator)
				{
					rewards.add_points_to_index(index as u32, points);
				}
			}
		});
	}

	/// Add reward points to validators using their validator index.
	///
	/// For each element in the iterator the given number of points in u32 is added to the
	/// validator, thus duplicates are handled.
	pub fn reward_by_indices(validators_points: impl IntoIterator<Item = (u32, u32)>) {
		let current_elected_len = <Module<T>>::current_elected().len() as u32;

		CurrentEraPointsEarned::mutate(|rewards| {
			for (validator_index, points) in validators_points.into_iter() {
				if validator_index < current_elected_len {
					rewards.add_points_to_index(validator_index, points);
				}
			}
		});
	}

	/// Ensures that at the end of the current session there will be a new era.
	fn ensure_new_era() {
		match ForceEra::get() {
			Forcing::ForceAlways | Forcing::ForceNew => (),
			_ => ForceEra::put(Forcing::ForceNew),
		}
	}
}

impl<T: Trait> pallet_session::SessionManager<T::AccountId> for Module<T> {
	fn new_session(new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		Self::ensure_storage_upgraded();
		if new_index == 0 {
			return Self::initial_session();
		}
		Self::new_session(new_index - 1)
	}
	fn end_session(_end_index: SessionIndex) {}
}

impl<T: Trait> historical::SessionManager<T::AccountId, Exposure<T::AccountId, BalanceOf<T>>> for Module<T> {
	fn new_session(new_index: SessionIndex)
		-> Option<Vec<(T::AccountId, Exposure<T::AccountId, BalanceOf<T>>)>>
	{
		<Self as pallet_session::SessionManager<_>>::new_session(new_index).map(|validators| {
			validators.into_iter().map(|v| {
				let exposure = <Stakers<T>>::get(&v);
				(v, exposure)
			}).collect()
		})
	}
	fn end_session(end_index: SessionIndex) {
		<Self as pallet_session::SessionManager<_>>::end_session(end_index)
	}
}

/// Add reward points to block authors:
/// * 20 points to the block producer for producing a (non-uncle) block in the relay chain,
/// * 2 points to the block producer for each reference to a previously unreferenced uncle, and
/// * 1 point to the producer of each referenced uncle block.
impl<T: Trait + pallet_authorship::Trait> pallet_authorship::EventHandler<T::AccountId, T::BlockNumber> for Module<T> {
	fn note_author(author: T::AccountId) {
		Self::reward_by_ids(vec![(author, 20)]);
	}
	fn note_uncle(author: T::AccountId, _age: T::BlockNumber) {
		Self::reward_by_ids(vec![
			(<pallet_authorship::Module<T>>::author(), 2),
			(author, 1)
		])
	}
}

/// A `Convert` implementation that finds the stash of the given controller account,
/// if any.
pub struct StashOf<T>(sp_std::marker::PhantomData<T>);

impl<T: Trait> Convert<T::AccountId, Option<T::AccountId>> for StashOf<T> {
	fn convert(controller: T::AccountId) -> Option<T::AccountId> {
		<Module<T>>::ledger(&controller).map(|l| l.stash)
	}
}

/// A typed conversion from stash account ID to the current exposure of nominators
/// on that account.
pub struct ExposureOf<T>(sp_std::marker::PhantomData<T>);

impl<T: Trait> Convert<T::AccountId, Option<Exposure<T::AccountId, BalanceOf<T>>>>
	for ExposureOf<T>
{
	fn convert(validator: T::AccountId) -> Option<Exposure<T::AccountId, BalanceOf<T>>> {
		Some(<Module<T>>::stakers(&validator))
	}
}

/// This is intended to be used with `FilterHistoricalOffences`.
impl <T: Trait> OnOffenceHandler<T::AccountId, pallet_session::historical::IdentificationTuple<T>> for Module<T> where
	T: pallet_session::Trait<ValidatorId = <T as frame_system::Trait>::AccountId>,
	T: pallet_session::historical::Trait<
		FullIdentification = Exposure<<T as frame_system::Trait>::AccountId, BalanceOf<T>>,
		FullIdentificationOf = ExposureOf<T>,
	>,
	T::SessionHandler: pallet_session::SessionHandler<<T as frame_system::Trait>::AccountId>,
	T::SessionManager: pallet_session::SessionManager<<T as frame_system::Trait>::AccountId>,
	T::ValidatorIdOf: Convert<<T as frame_system::Trait>::AccountId, Option<<T as frame_system::Trait>::AccountId>>
{
	fn on_offence(
		offenders: &[OffenceDetails<T::AccountId, pallet_session::historical::IdentificationTuple<T>>],
		slash_fraction: &[Perbill],
		slash_session: SessionIndex,
	) {
		<Module<T>>::ensure_storage_upgraded();

		let reward_proportion = SlashRewardFraction::get();

		let era_now = Self::current_era();
		let window_start = era_now.saturating_sub(T::BondingDuration::get());
		let current_era_start_session = CurrentEraStartSessionIndex::get();

		// fast path for current-era report - most likely.
		let slash_era = if slash_session >= current_era_start_session {
			era_now
		} else {
			let eras = BondedEras::get();

			// reverse because it's more likely to find reports from recent eras.
			match eras.iter().rev().filter(|&&(_, ref sesh)| sesh <= &slash_session).next() {
				None => return, // before bonding period. defensive - should be filtered out.
				Some(&(ref slash_era, _)) => *slash_era,
			}
		};

		<Self as Store>::EarliestUnappliedSlash::mutate(|earliest| {
			if earliest.is_none() {
				*earliest = Some(era_now)
			}
		});

		let slash_defer_duration = T::SlashDeferDuration::get();

		for (details, slash_fraction) in offenders.iter().zip(slash_fraction) {
			let stash = &details.offender.0;
			let exposure = &details.offender.1;

			// Skip if the validator is invulnerable.
			if Self::invulnerables().contains(stash) {
				continue
			}

			let unapplied = slashing::compute_slash::<T>(slashing::SlashParams {
				stash,
				slash: *slash_fraction,
				exposure,
				slash_era,
				window_start,
				now: era_now,
				reward_proportion,
			});

			if let Some(mut unapplied) = unapplied {
				unapplied.reporters = details.reporters.clone();
				if slash_defer_duration == 0 {
					// apply right away.
					slashing::apply_slash::<T>(unapplied);
				} else {
					// defer to end of some `slash_defer_duration` from now.
					<Self as Store>::UnappliedSlashes::mutate(
						era_now,
						move |for_later| for_later.push(unapplied),
					);
				}
			}
		}
	}
}

/// Filter historical offences out and only allow those from the bonding period.
pub struct FilterHistoricalOffences<T, R> {
	_inner: sp_std::marker::PhantomData<(T, R)>,
}

impl<T, Reporter, Offender, R, O> ReportOffence<Reporter, Offender, O>
	for FilterHistoricalOffences<Module<T>, R> where
	T: Trait,
	R: ReportOffence<Reporter, Offender, O>,
	O: Offence<Offender>,
{
	fn report_offence(reporters: Vec<Reporter>, offence: O) {
		<Module<T>>::ensure_storage_upgraded();

		// disallow any slashing from before the current bonding period.
		let offence_session = offence.session_index();
		let bonded_eras = BondedEras::get();

		if bonded_eras.first().filter(|(_, start)| offence_session >= *start).is_some() {
			R::report_offence(reporters, offence)
		} else {
			<Module<T>>::deposit_event(
				RawEvent::OldSlashingReportDiscarded(offence_session)
			)
		}
	}
}

impl<T: Trait> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = T::KeyType;
}

impl<T: Trait> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = T::KeyType;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::KeyType)>
	{
		assert!(Self::keys().is_empty(), "Keys are already initialized!");
		<Keys<T>>::put(validators.map(|x| x.1).collect::<Vec<_>>());
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, _queued_validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::KeyType)>
	{
		// Update they keys
		<Keys<T>>::put(validators.map(|x| x.1).collect::<Vec<_>>());
	}

	fn on_before_session_ending() {}

	fn on_disabled(_i: usize) {}
}


/// Disallows any transactions that change the election result to be submitted after the election
/// window is open.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct LockStakingStatus<T>(sp_std::marker::PhantomData<T>);

impl<T: Trait + Send + Sync> sp_std::fmt::Debug for LockStakingStatus<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "LockStakingStatus<{:?}>", self.0)
	}
	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T> LockStakingStatus<T> {
	/// Create new `LockStakingStatus`.
	pub fn new() -> Self {
		Self(sp_std::marker::PhantomData)
	}
}

impl<T> Default for LockStakingStatus<T> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T: Trait + Send + Sync> SignedExtension for LockStakingStatus<T> {
	const IDENTIFIER: &'static str = "LockStakingStatus";
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = ();
	type DispatchInfo = frame_support::weights::DispatchInfo;
	type Pre = ();

	fn additional_signed(&self) -> Result<(), TransactionValidityError> { Ok(()) }

	fn validate(
		&self,
		_who: &Self::AccountId,
		call: &Self::Call,
		_info: Self::DispatchInfo,
		_len: usize,
	) -> TransactionValidity {
		if let Some(inner_call) = call.is_sub_type() {
			if let ElectionStatus::Open(_) = <Module<T>>::era_election_status() {
				match inner_call {
					Call::<T>::bond(..) |
					Call::<T>::unbond(..) |
					Call::<T>::bond_extra(..) |
					Call::<T>::rebond(..) |
					Call::<T>::validate(..) |
					Call::<T>::nominate(..) |
					Call::<T>::chill(..) => {
						return Err(InvalidTransaction::Stale.into());
					}
					_ => { /* no problem */ }
				}
			}
		}

		Ok(Default::default())
	}
}

#[allow(deprecated)]
impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;
	fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
		if let Call::submit_election_solution_unsigned(
			winners,
			compact,
			score,
			validator_index,
			signature,
		) = call {
			use offchain_election::SignaturePayload;

			// discard early solution
			if Self::era_election_status() == ElectionStatus::Closed {
				debug::native::debug!(
					target: "staking",
					"rejecting unsigned transaction because it is too early."
				);
				return InvalidTransaction::Future.into();
			}

			// discard weak solution
			if let Some(queued_score) = Self::queued_score() {
				if !is_score_better(queued_score, *score) {
					debug::native::debug!(
						target: "staking",
						"rejecting unsigned transaction because the claimed score is not good enough."
					);
					return InvalidTransaction::Custom(1u8).into();
				}
			}

			// check signature
			let payload: SignaturePayload = (
				winners,
				compact,
				score,
				validator_index,
			);

			let all_keys = Self::keys();
			let validator_key = all_keys.get(*validator_index as usize)
				// validator index is incorrect -- no key corresponds to it.
				.ok_or(TransactionValidityError::Invalid(InvalidTransaction::Custom(0u8).into()))?;

			let signature_valid = payload.using_encoded(|encoded_payload| {
				validator_key.verify(&encoded_payload, &signature)
			});

			if !signature_valid {
				return InvalidTransaction::BadProof.into();
			}

			Ok(ValidTransaction {
				priority: score[0].saturated_into(),
				requires: vec![],
				provides: vec![(Self::current_era(), validator_key).encode()],
				longevity: TryInto::<u64>::try_into(T::ElectionLookahead::get()).unwrap_or(150_u64),
				propagate: true,
			})
		} else {
			InvalidTransaction::Call.into()
		}
	}
}
