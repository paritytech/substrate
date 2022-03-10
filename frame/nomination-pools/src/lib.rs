//! # Nomination Pools for Staking Delegation
//!
//! A pallet that allows delegators to delegate their stake to nominating pools, each of which acts
//! as a nominator and nominates validators on the delegators behalf.
//!
//! # Index
//!
//! * [Key terms](#key-terms)
//! * [Usage](#usage)
//! * [Design](#design)
//!
//! ## Key terms
//!
//!  * bonded pool: Tracks the distribution of actively staked funds. See [`BondedPool`] and
//! [`BondedPoolPoints`]
//! * reward pool: Tracks rewards earned by actively staked funds. See [`RewardPool`] and
//!   [`RewardPools`].
//! * unbonding sub pools: Collection of pools at different phases of the unbonding lifecycle. See
//!   [`SubPools`] and [`SubPoolsStorage`].
//! * delegators: Accounts that are members of pools. See [`Delegator`] and [`Delegators`].
//! * point: A measure of a delegators portion of a pools funds.
//!
//! ## Usage
//!
//! ### Join
//!
//! A account can stake funds with a nomination pool by calling [`Call::join`].
//!
//! For design docs see the [joining](#joining) section.
//!
//! ### Claim rewards
//!
//! After joining a pool, a delegator can claim rewards by calling [`Call::claim_payout`].
//!
//! For design docs see the [reward pool](#reward-pool) section.
//!
//! ### Leave
//!
//! In order to leave, a delegator must take two steps.
//!
//! First, they must call [`Call::unbond_other`]. The unbond other extrinsic will start the
//! unbonding process by unbonding all of the delegators funds.
//!
//! Second, once [`sp_staking::StakingInterface::bonding_duration`] eras have passed, the delegator
//! can call [`Call::withdraw_unbonded_other`] to withdraw all there funds.
//!
//! For design docs see the [bonded pool](#bonded-pool) and [unbonding sub
//! pools](#unbonding-sub-pools) sections.
//!
//! ### Slashes
//!
//! Slashes are distributed evenly across the bonded pool and the unbonding pools from slash era+1
//! through the slash apply era. Thus, any delegator who either a) unbonded or b) was actively
//! bonded in the aforementioned range of eras will be affected by the slash. A delegator is slashed
//! pro-rata based on its stake relative to the total slash amount.
//!
//! For design docs see the [slashing](#slashing) section.
//!
//! ### Adminstration
//!
//! A pool can be created with the [`Call::create`] call. Once created, the pools nominator or root
//! user must call [`Call::nominate`] to start nominating. [`Call::nominate`] can be called at
//! anytime to update validator selection.
//!
//! To help facilitate pool adminstration the pool has one of three states (see [`PoolState`]):
//!
//! * Open: Anyone can join the pool and no delegators can be permissionlessly removed.
//! * Blocked: No delegators can join and some admin roles can kick delegators.
//! * Destroying: No delegators can join and all delegators can be permissionlessly removed with
//!   [`Call::unbond_other`] and [`Call::withdraw_unbonded_other`]. Once a pool is destroying state,
//!   it cannot be reverted to another state.
//!
//! A pool has 3 administrative positions (see [`BondedPool`]):
//!
//! * Depositor: creates the pool and is the initial delegator. The can only leave pool once all
//!   other delegators have left. Once they fully leave the pool is destroyed.
//! * Nominator: can select which validators the pool nominates.
//! * State-Toggler: can change the pools state and kick delegators if the pool is blocked.
//! * Root: can change the nominator, state-toggler, or itself and can perform any of the actions
//!   the nominator or state-toggler can.
//!
//! ## Design
//!
//! _Notes_: this section uses pseudo code to explain general design and does not necessarily
//! reflect the exact implementation. Additionally, a working knowledge of `pallet-staking`'s api is
//! assumed.
//!
//! ### Goals
//!
//! * Maintain network security by upholding integrity of slashing events, sufficiently penalizing
//!   delegators that where in the pool while it was backing a validator that got slashed.
//! * Maximize scalability in terms of delegator count.
//!
//! In order to maintain scalability, all operations are independent of the number of delegators. To
//! do this, delegation specific information is stored local to the delegator while the pool data
//! structures have bounded datum.
//!
//! ### Bonded pool
//!
//! A bonded pool nominates with its total balance, excluding that which has been withdrawn for
//! unbonding. The total points of a bonded pool are always equal to the sum of points of the
//! delegation members. A bonded pool tracks its points and reads its bonded balance.
//!
//! When a delegator joins a pool, `amount_transferred` is transferred from the delegators account
//! to the bonded pools account. Then the pool calls `staking::bond_extra(amount_transferred)` and
//! issues new points which are tracked by the delegator and added to the bonded pool's points.
//!
//! When the pool already has some balance, we want the value of a point before the transfer to
//! equal the value of a point after the transfer. So, when a delegator joins a bonded pool with a
//! given `amount_transferred`, we maintain the ratio of bonded balance to points such that:
//!
//! ```text
//! balance_after_transfer / points_after_transfer == balance_before_transfer / points_before_transfer;
//! ```
//!
//! To achieve this, we issue points based on the following:
//!
//! ```text
//! points_issued = (points_before_transfer / balance_before_transfer) * amount_transferred;
//! ```
//!
//! For new bonded pools we can set the points issued per balance arbitrarily. In this
//! implementation we use a 1 points to 1 balance ratio for pool creation (see
//! [`POINTS_TO_BALANCE_INIT_RATIO`]).
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::create`]
//! * [`Call::join`]
//!
//! ### Reward pool
//!
//! When a pool is first bonded it sets up an arbitrary account as its reward destination. To track
//! staking rewards we track how the balance of this reward account changes.
//!
//! The reward pool needs to store:
//!
//! * The pool balance at the time of the last payout: `reward_pool.balance`
//! * The total earnings ever at the time of the last payout: `reward_pool.total_earnings`
//! * The total points in the pool at the time of the last payout: `reward_pool.points`
//!
//! And the delegator needs to store:
//!
//! * The total payouts at the time of the last payout by that delegator:
//!   `delegator.reward_pool_total_earnings`
//!
//! Before the first reward claim is initiated for a pool, all the above variables are set to zero.
//!
//! When a delegator initiates a claim, the following happens:
//!
//! 1) Compute the reward pool's total points and the delegator's virtual points in the reward pool
//!     * First `current_total_earnings` is computed (`current_balance` is the free balance of the
//!       reward pool at the beginning of these operations.)
//!			```text
//!			current_total_earnings =
//!       		current_balance - reward_pool.balance + pool.total_earnings;
//!			```
//!     * Then the `current_points` is computed. Every balance unit that was added to the reward
//!       pool since last time recorded means that the `pool.points` is increased by
//!       `bonding_pool.total_points`. In other words, for every unit of balance that has been
//!       earned by the reward pool, the reward pool points are inflated by `bonded_pool.points`. In
//!       effect this allows each, single unit of balance (e.g. planck) to be divvied up pro-rata
//!       among delegators based on points.
//!			```text
//!			new_earnings = current_total_earnings - reward_pool.total_earnings;
//!       	current_points = reward_pool.points + bonding_pool.points * new_earnings;
//!			```
//!     * Finally, the`delegator_virtual_points` are computed: the product of the delegator's points
//!       in the bonding pool and the total inflow of balance units since the last time the
//!       delegator claimed rewards
//!			```text
//!			new_earnings_since_last_claim = current_total_earnings - delegator.reward_pool_total_earnings;
//!        	delegator_virtual_points = delegator.points * new_earnings_since_last_claim;
//!       	```
//! 2) Compute the `delegator_payout`:
//!     ```text
//!     delegator_pool_point_ratio = delegator_virtual_points / current_points;
//!     delegator_payout = current_balance * delegator_pool_point_ratio;
//!     ```
//! 3) Transfer `delegator_payout` to the delegator
//! 4) For the delegator set:
//!     ```text
//!     delegator.reward_pool_total_earnings = current_total_earnings;
//!     ```
//! 5) For the pool set:
//!     ```text
//!     reward_pool.points = current_points - delegator_virtual_points;
//!     reward_pool.balance = current_balance - delegator_payout;
//!     reward_pool.total_earnings = current_total_earnings;
//!     ```
//!
//! _Note_: One short coming of this design is that new joiners can claim rewards for the era after
//! they join even though their funds did not contribute to the pools vote weight. When a
//! delegator joins, it's `reward_pool_total_earnings` field is set equal to the `total_earnings`
//! of the reward pool at that point in time. At best the reward pool has the rewards up through the
//! previous era. If a delegator joins prior to the election snapshot it will benefit from the
//! rewards for the active era despite not contributing to the pool's vote weight. If it joins
//! after the election snapshot is taken it will benefit from the rewards of the next _2_ eras
//! because it's vote weight will not be counted until the election snapshot in active era + 1.
//! Related: https://github.com/paritytech/substrate/issues/10861
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::claim_payout`]
//!
//! ### Unbonding sub pools
//!
//! When a delegator unbonds, it's balance is unbonded in the bonded pool's account and tracked in
//! an unbonding pool associated with the active era. If no such pool exists, one is created. To
//! track which unbonding sub pool a delegator belongs too, a delegator tracks it's
//! `unbonding_era`.
//!
//! When a delegator initiates unbonding it's claim on the bonded pool
//! (`balance_to_unbond`) is computed as:
//!
//! ```text
//! balance_to_unbond = (bonded_pool.balance / bonded_pool.points) * delegator.points;
//! ```
//!
//! If this is the first transfer into an unbonding pool arbitrary amount of points can be issued
//! per balance. In this implementation unbonding pools are initialized with a 1 point to 1 balance
//! ratio (see [`POINTS_TO_BALANCE_INIT_RATIO`]). Otherwise, the unbonding pools hold the same
//! points to balance ratio properties as the bonded pool, so delegator points in the
//! unbonding pool are issued based on
//!
//! ```text
//! new_points_issued = (points_before_transfer / balance_before_transfer) * balance_to_unbond;
//! ```
//!
//! For scalability, a bound is maintained on the number of unbonding sub pools (see
//! [`TotalUnbondingPools`]). An unbonding pool is removed once its older than `current_era -
//! TotalUnbondingPools`. An unbonding pool is merged into the unbonded pool with
//!
//! ```text
//! unbounded_pool.balance = unbounded_pool.balance + unbonding_pool.balance;
//! unbounded_pool.points = unbounded_pool.points + unbonding_pool.points;
//! ```
//!
//! This scheme "averages" out the points value in the unbonded pool.
//!
//! Once a delgators `unbonding_era` is older than `current_era -
//! [sp_staking::StakingInterface::bonding_duration]`, it can can cash it's points out of the
//! corresponding unbonding pool. If it's `unbonding_era` is older than `current_era -
//! TotalUnbondingPools`, it can cash it's points from the unbonded pool.
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::unbond_other`]
//! * [`Call::withdraw_unbonded_other`]
//!
//! ### Slashing
//!
//! This section assumes that the slash computation is executed by
//! [`pallet_staking::StakingLedger::slash`], which passes the information to this pallet via
//! [`sp_staking::OnStakerSlash::on_slash`].
//!
//! Unbonding pools need to be slashed to ensure all nominators whom where in the bonded pool
//! while it was backing a validator that equivocated are punished. Without these measures a
//! nominator could unbond right after a validator equivocated with no consequences.
//!
//! This strategy is unfair to delegators who joined after the slash, because they get slashed as
//! well, but spares delegators who unbond. The latter is much more important for security: if a
//! pool's validators are attacking the network, their delegators need to unbond fast! Avoiding
//! slashes gives them an incentive to do that if validators get repeatedly slashed.
//!
//! To be fair to joiners, this implementation also need joining pools, which are actively staking,
//! in addition to the unbonding pools. For maintenance simplicity these are not implemented. Related: https://github.com/paritytech/substrate/issues/10860
//!
//! **Relevant methods:**
//!
//! * [`Pallet::do_slash`]
//!
//! ### Limitations
//!
//! * Delegators cannot vote with their staked funds because they are transferred into the pools
//!   account. In the future this can be overcome by allowing the delegators to vote with their
//!   bonded funds via vote splitting.
//! * Delegators cannot quickly transfer to another pool if they do no like nominations, instead
//!   they must wait for the unbonding duration.
//!
//! # Runtime builder warnings
//!
//! * Watch out for overflow of [`RewardPoints`] and [`BalanceOf`] types. Consider things like the
//!   chains total issuance, staking reward rate, and burn rate.
//
// Invariants
// * A `delegator.pool` must always be a valid entry in `RewardPools`, and `BondedPoolPoints`.
// * Every entry in `BondedPoolPoints` must have  a corresponding entry in `RewardPools`
// * If a delegator unbonds, the sub pools should always correctly track slashses such that the
//   calculated amount when withdrawing unbonded is a lower bound of the pools free balance.
// * If the depositor is actively unbonding, the pool is in destroying state. To achieve this, once
//   a pool is flipped to a destroying state it cannot change its state.
// * The sum of each pools delegator counter equals the `Delegators::count()`.
// * A pool's `delegator_counter` should always be gt 0.

//
// - transparent prefx for account ids

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	ensure,
	pallet_prelude::{MaxEncodedLen, *},
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{
		Currency, DefensiveOption, DefensiveResult, DefensiveSaturating, ExistenceRequirement, Get,
	},
	DefaultNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_core::U256;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Bounded, Convert, Saturating, StaticLookup, TrailingZeroInput, Zero};
use sp_staking::{EraIndex, OnStakerSlash, StakingInterface};
use sp_std::{collections::btree_map::BTreeMap, ops::Div, vec::Vec};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod sanity;
#[cfg(test)]
mod tests;

pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type SubPoolsWithEra<T> = BoundedBTreeMap<EraIndex, UnbondPool<T>, TotalUnbondingPools<T>>;
// NOTE: this assumes the balance type u128 or smaller.
type RewardPoints = U256;

const POINTS_TO_BALANCE_INIT_RATIO: u32 = 1;

/// Extrinsics that bond some funds to the pool.
enum PoolBond {
	Create,
	Join,
}

/// Identifier for encoding different pool account types.
enum AccountType {
	/// The bonded account of the pool. This is functionally both the stash and controller account.
	Bonded,
	/// The reward account of the pool.
	Reward,
}

impl Encode for AccountType {
	fn encode(&self) -> Vec<u8> {
		match self {
			Self::Bonded => b"bond".to_vec(),
			Self::Reward => b"rewd".to_vec(),
		}
	}
}

/// Calculate the number of points to issue from a pool as `(current_points / current_balance) *
/// new_funds` except for some zero edge cases; see logic and tests for details.
fn points_to_issue<T: Config>(
	current_balance: BalanceOf<T>,
	current_points: BalanceOf<T>,
	new_funds: BalanceOf<T>,
) -> BalanceOf<T> {
	match (current_balance.is_zero(), current_points.is_zero()) {
		(true, true) | (false, true) =>
			new_funds.saturating_mul(POINTS_TO_BALANCE_INIT_RATIO.into()),
		(true, false) => {
			// The pool was totally slashed.
			// This is the equivalent of `(current_points / 1) * new_funds`.
			new_funds.saturating_mul(current_points)
		},
		(false, false) => {
			// Equivalent to (current_points / current_balance) * new_funds
			current_points
				.saturating_mul(new_funds)
				// We check for zero above
				.div(current_balance)
		},
	}
}

// Calculate the balance of a pool to unbond as `(current_balance / current_points) *
// delegator_points`. Returns zero if any of the inputs are zero.
fn balance_to_unbond<T: Config>(
	current_balance: BalanceOf<T>,
	current_points: BalanceOf<T>,
	delegator_points: BalanceOf<T>,
) -> BalanceOf<T> {
	if current_balance.is_zero() || current_points.is_zero() || delegator_points.is_zero() {
		// There is nothing to unbond
		return Zero::zero()
	}

	// Equivalent of (current_balance / current_points) * delegator_points
	current_balance
		.saturating_mul(delegator_points)
		// We check for zero above
		.div(current_points)
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Delegator<T: Config> {
	// TODO pool_bonded_account. Add in top level docs note about pool always ID'ed by bonded
	// account
	pub pool: T::AccountId,
	/// The quantity of points this delegator has in the bonded pool or in a sub pool if
	/// `Self::unbonding_era` is some.
	pub points: BalanceOf<T>,
	/// The reward pools total earnings _ever_ the last time this delegator claimed a payout.
	/// Assuming no massive burning events, we expect this value to always be below total issuance.
	/// This value lines up with the [`RewardPool::total_earnings`] after a delegator claims a
	/// payout.
	pub reward_pool_total_earnings: BalanceOf<T>,
	/// The era this delegator started unbonding at.
	pub unbonding_era: Option<EraIndex>,
}

/// A pool's possible states.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, RuntimeDebugNoBound, Clone)]
pub enum PoolState {
	#[codec(index = 0)]
	Open,
	#[codec(index = 1)]
	Blocked,
	#[codec(index = 2)]
	Destroying,
}

// TODO: if this is meant to not be used EVER directly, you can enforce that by putting this and
// `BondedPool` into a private `mod {}` and only exporting the stuff you need.
// TODO: call Inner
/// Pool permissions and state
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound, PartialEq)]
#[cfg_attr(feature = "std", derive(Clone))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct BondedPoolStorage<T: Config> {
	/// See [`BondedPool::points`].
	pub points: BalanceOf<T>,
	/// See [`BondedPool::state_toggler`].
	pub state: PoolState,
	/// See [`BondedPool::delegator_counter`]
	pub delegator_counter: u32,
	/// See [`BondedPool::depositor`].
	pub depositor: T::AccountId,
	/// See [`BondedPool::admin`].
	pub root: T::AccountId,
	/// See [`BondedPool::nominator`].
	pub nominator: T::AccountId,
	/// See [`BondedPool::state_toggler`].
	pub state_toggler: T::AccountId,
}

// module id + reward/bonded + last 20 chars of depositor account id

#[derive(RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
pub struct BondedPool<T: Config> {
	/// Points of the pool. Each delegator has some corresponding the points. The portion of points
	/// that belong to a delegator represent the portion of the pools bonded funds belong to the
	/// delegator.
	points: BalanceOf<T>,
	/// State of the pool.
	state: PoolState,
	/// Count of delegators that belong to this pool.
	delegator_counter: u32,
	/// Account that puts down a deposit to create the pool. This account acts a delegator, but can
	/// only unbond if no other delegators belong to the pool.
	depositor: T::AccountId,
	/// Can perform the same actions as [`Self::nominator`] and [`Self::state_toggler`].
	/// Additionally, this account can set the `nominator` and `state_toggler` at any time.
	root: T::AccountId,
	/// Can set the pool's nominations at any time.
	nominator: T::AccountId,
	/// Can toggle the pools state, including setting the pool as blocked or putting the pool into
	/// destruction mode. The state toggle can also "kick" delegators by unbonding them.
	state_toggler: T::AccountId,
	/// AccountId of the pool.
	account: T::AccountId,
}

impl<T: Config> BondedPool<T> {
	fn new(
		depositor: T::AccountId,
		root: T::AccountId,
		nominator: T::AccountId,
		state_toggler: T::AccountId,
	) -> Self {
		Self {
			account: Self::create_account(AccountType::Bonded, depositor.clone()),
			depositor,
			root,
			nominator,
			state_toggler,
			state: PoolState::Open,
			points: Zero::zero(),
			delegator_counter: Zero::zero(),
		}
	}

	// TODO: figure out if we should ditch BondedPoolStorage vs BondedPool and instead just have
	// BondedPool that doesn't have `account` field. Instead just use deterministic accountId
	// generation function. Only downside is this will have some increased computational cost
	/// Get [`Self`] from storage. Returns `None` if no entry for `pool_account` exists.
	fn get(pool_account: &T::AccountId) -> Option<Self> {
		BondedPools::<T>::try_get(pool_account).ok().map(|storage| Self {
			points: storage.points,
			delegator_counter: storage.delegator_counter,
			state_toggler: storage.state_toggler,
			depositor: storage.depositor,
			root: storage.root,
			nominator: storage.nominator,
			state: storage.state,
			account: pool_account.clone(),
		})
	}

	/// Consume and put [`Self`] into storage.
	fn put(self) {
		BondedPools::<T>::insert(
			self.account,
			BondedPoolStorage {
				points: self.points,
				delegator_counter: self.delegator_counter,
				depositor: self.depositor,
				root: self.root,
				nominator: self.nominator,
				state_toggler: self.state_toggler,
				state: self.state,
			},
		);
	}
	/// Consume and remove [`Self`] from storage.
	fn remove(self) {
		BondedPools::<T>::remove(self.account);
	}

	fn create_account(account_type: AccountType, depositor: T::AccountId) -> T::AccountId {
		// TODO: look into make the prefix transparent by not hashing anything
		// TODO: look into a using a configurable module id.
		let entropy = (b"npls", account_type, depositor).using_encoded(blake2_256);
		Decode::decode(&mut TrailingZeroInput::new(&entropy)).expect("Infinite length input. qed")
	}

	fn reward_account(&self) -> T::AccountId {
		Self::create_account(AccountType::Reward, self.depositor.clone())
	}

	/// Get the amount of points to issue for some new funds that will be bonded in the pool.
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());
		points_to_issue::<T>(bonded_balance, self.points, new_funds)
	}

	/// Get the amount of balance to unbond from the pool based on a delegator's points of the pool.
	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());
		balance_to_unbond::<T>(bonded_balance, self.points, delegator_points)
	}

	/// Issue points to [`Self`] for `new_funds`.
	fn issue(&mut self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let points_to_issue = self.points_to_issue(new_funds);
		self.points = self.points.saturating_add(points_to_issue);

		points_to_issue
	}

	/// Increment the delegator counter. Ensures that the pool and system delegator limits are
	/// respected.
	fn inc_delegators(&mut self) -> Result<(), DispatchError> {
		ensure!(
			MaxDelegatorsPerPool::<T>::get()
				.map_or(true, |max_per_pool| self.delegator_counter < max_per_pool),
			Error::<T>::MaxDelegators
		);
		ensure!(
			MaxDelegators::<T>::get().map_or(true, |max| Delegators::<T>::count() < max),
			Error::<T>::MaxDelegators
		);
		self.delegator_counter = self.delegator_counter.defensive_saturating_add(1);
		Ok(())
	}

	/// Decrement the delegator counter.
	fn dec_delegators(mut self) -> Self {
		self.delegator_counter = self.delegator_counter.defensive_saturating_sub(1);
		self
	}

	/// The pools balance that is not locked. This assumes the staking system is the only
	fn non_locked_balance(&self) -> BalanceOf<T> {
		T::Currency::free_balance(&self.account).saturating_sub(
			T::StakingInterface::locked_balance(&self.account).unwrap_or(Zero::zero()),
		)
	}

	fn can_nominate(&self, who: &T::AccountId) -> bool {
		*who == self.root || *who == self.nominator
	}

	fn can_kick(&self, who: &T::AccountId) -> bool {
		*who == self.root || *who == self.state_toggler && self.state == PoolState::Blocked
	}

	fn can_toggle_state(&self, who: &T::AccountId) -> bool {
		*who == self.root || *who == self.state_toggler && !self.is_destroying()
	}

	fn can_set_metadata(&self, who: &T::AccountId) -> bool {
		*who == self.root || *who == self.state_toggler
	}

	fn is_destroying(&self) -> bool {
		self.state == PoolState::Destroying
	}

	/// Whether or not the pool is ok to be in `PoolSate::Open`. If this returns an `Err`, then the
	/// pool is unrecoverable and should be in the destroying state.
	fn ok_to_be_open(&self) -> Result<(), DispatchError> {
		ensure!(!self.is_destroying(), Error::<T>::CanNotChangeState);

		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());
		ensure!(!bonded_balance.is_zero(), Error::<T>::OverflowRisk);

		let points_to_balance_ratio_floor = self
			.points
			// We checked for zero above
			.div(bonded_balance);

		// TODO make sure these checks make sense. Taken from staking design chat with Al

		// Pool points can inflate relative to balance, but only if the pool is slashed.
		//
		// If we cap the ratio of points:balance so one cannot join a pool that has been slashed
		// 90%,
		ensure!(points_to_balance_ratio_floor < 10u32.into(), Error::<T>::OverflowRisk);
		// while restricting the balance to 1/10th of max total issuance,
		ensure!(
			bonded_balance < BalanceOf::<T>::max_value().div(10u32.into()),
			Error::<T>::OverflowRisk
		);
		// then we can be decently confident the bonding pool points will not overflow
		// `BalanceOf<T>`.

		Ok(())
	}

	/// Check that the pool can accept a member with `new_funds`.
	fn ok_to_join_with(
		&self,
		new_funds: BalanceOf<T>,
		possible_delegator_id: &T::AccountId,
	) -> Result<(), DispatchError> {
		// If a delegator already exists that means they already belong to a pool
		ensure!(
			!Delegators::<T>::contains_key(possible_delegator_id),
			Error::<T>::AccountBelongsToOtherPool
		);
		ensure!(new_funds >= MinJoinBond::<T>::get(), Error::<T>::MinimumBondNotMet);

		ensure!(self.state == PoolState::Open, Error::<T>::NotOpen);

		self.ok_to_be_open()?;

		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());

		// TODO: this is highly questionable.
		// instead of this, where we multiply and it could saturate, watch out for being close to
		// the point of saturation.
		ensure!(
			new_funds.saturating_add(bonded_balance) <
				BalanceOf::<T>::max_value().div(10u32.into()),
			Error::<T>::OverflowRisk
		);

		Ok(())
	}

	fn ok_to_unbond_other_with(
		&self,
		caller: &T::AccountId,
		target_account: &T::AccountId,
		target_delegator: &Delegator<T>,
	) -> Result<(), DispatchError> {
		let is_permissioned = caller == target_account;
		let is_depositor = *target_account == self.depositor;
		match (is_permissioned, is_depositor) {
			// If the pool is blocked, then an admin with kicking permissions can remove a
			// delegator. If the pool is being destroyed, anyone can remove a delegator
			(false, false) => {
				ensure!(
					self.can_kick(caller) || self.is_destroying(),
					Error::<T>::NotKickerOrDestroying
				)
			},
			// Any delegator who is not the depositor can always unbond themselves
			(true, false) => (),
			// The depositor can only start unbonding if the pool is already being destroyed and
			// they are the delegator in the pool. Note that an invariant is once the pool is
			// destroying it cannot switch states, so by being in destroying we are guaranteed no
			// other delegators can possibly join.
			(false, true) | (true, true) => {
				ensure!(target_delegator.points == self.points, Error::<T>::NotOnlyDelegator);
				ensure!(self.is_destroying(), Error::<T>::NotDestroying);
			},
		}
		Ok(())
	}

	/// Returns a result indicating if [`Pallet::withdraw_unbonded_other`] can be executed.
	fn ok_to_withdraw_unbonded_other_with(
		&self,
		caller: &T::AccountId,
		target_account: &T::AccountId,
		target_delegator: &Delegator<T>,
		sub_pools: &SubPools<T>,
	) -> Result<bool, DispatchError> {
		if *target_account == self.depositor {
			// This is a depositor
			if !sub_pools.no_era.points.is_zero() {
				// Unbonded pool has some points, so if they are the last delegator they must be
				// here
				// Since the depositor is the last to unbond, this should never be possible
				ensure!(sub_pools.with_era.len().is_zero(), Error::<T>::NotOnlyDelegator);
				ensure!(
					sub_pools.no_era.points == target_delegator.points,
					Error::<T>::NotOnlyDelegator
				);
			} else {
				// No points in the `no_era` pool, so they must be in a `with_era` pool
				// If there are no other delegators, this can be the only `with_era` pool since the
				// depositor was the last to withdraw. This assumes with_era sub pools are destroyed
				// whenever their points go to zero.
				ensure!(sub_pools.with_era.len() == 1, Error::<T>::NotOnlyDelegator);
				sub_pools
					.with_era
					.values()
					.next()
					.filter(|only_unbonding_pool| {
						only_unbonding_pool.points == target_delegator.points
					})
					.ok_or(Error::<T>::NotOnlyDelegator)?;
			}
			Ok(true)
		} else {
			// This isn't a depositor
			let is_permissioned = caller == target_account;
			ensure!(
				is_permissioned || self.can_kick(caller) || self.is_destroying(),
				Error::<T>::NotKickerOrDestroying
			);
			Ok(false)
		}
	}

	/// Try to transfer a delegators funds to the bonded pool account and then try to bond them.
	///
	/// # Warning
	///
	/// This must only be used inside of transactional extrinsic, as funds are transferred prior to
	/// attempting a fallible bond.
	fn try_bond_delegator(
		&mut self,
		who: &T::AccountId,
		amount: BalanceOf<T>,
		ty: PoolBond,
	) -> Result<BalanceOf<T>, DispatchError> {

		// Transfer the funds to be bonded from `who` to the pools account so the pool can then
		// go bond them.
		T::Currency::transfer(
			&who,
			&self.account,
			amount,
			match ty {
				PoolBond::Create => ExistenceRequirement::AllowDeath,
				PoolBond::Join => ExistenceRequirement::KeepAlive,
			},
		)?;
		// We must calculate the points issued *before* we bond who's funds, else points:balance
		// ratio will be wrong.
		let points_issued = self.issue(amount);

		match ty {
			// TODO: Consider making StakingInterface use reference.
			PoolBond::Create => T::StakingInterface::bond(
				self.account.clone(),
				// We make the stash and controller the same for simplicity
				self.account.clone(),
				amount,
				self.reward_account(),
			)?,
			// The pool should always be created in such a way its in a state to bond extra, but if
			// the active balance is slashed below the minimum bonded or the account cannot be
			// found, we exit early.
			PoolBond::Join => T::StakingInterface::bond_extra(self.account.clone(), amount)?,
		}

		Ok(points_issued)
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
	/// The reward destination for the pool.
	pub account: T::AccountId,
	/// The balance of this reward pool after the last claimed payout.
	pub balance: BalanceOf<T>,
	/// The total earnings _ever_ of this reward pool after the last claimed payout. I.E. the sum
	/// of all incoming balance through the pools life.
	///
	/// NOTE: We assume this will always be less than total issuance and thus can use the runtimes
	/// `Balance` type. However in a chain with a burn rate higher than the rate this increases,
	/// this type should be bigger than `Balance`.
	pub total_earnings: BalanceOf<T>,
	/// The total points of this reward pool after the last claimed payout.
	pub points: RewardPoints,
}

impl<T: Config> RewardPool<T> {
	/// Mutate the reward pool by updating the total earnings and current free balance.
	fn update_total_earnings_and_balance(&mut self) {
		let current_balance = T::Currency::free_balance(&self.account);
		// The earnings since the last time it was updated
		let new_earnings = current_balance.saturating_sub(self.balance);
		// The lifetime earnings of the of the reward pool
		self.total_earnings = new_earnings.saturating_add(self.total_earnings);
		self.balance = current_balance;
	}

	/// Get a reward pool and update its total earnings and balance
	fn get_and_update(bonded_pool_account: &T::AccountId) -> Option<Self> {
		RewardPools::<T>::get(bonded_pool_account).map(|mut r| {
			r.update_total_earnings_and_balance();
			r
		})
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct UnbondPool<T: Config> {
	points: BalanceOf<T>,
	balance: BalanceOf<T>,
}

impl<T: Config> UnbondPool<T> {
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		points_to_issue::<T>(self.balance, self.points, new_funds)
	}

	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		balance_to_unbond::<T>(self.balance, self.points, delegator_points)
	}

	/// Issue points and update the balance given `new_balance`.
	fn issue(&mut self, new_funds: BalanceOf<T>) {
		self.points = self.points.saturating_add(self.points_to_issue(new_funds));
		self.balance = self.balance.saturating_add(new_funds);
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct SubPools<T: Config> {
	/// A general, era agnostic pool of funds that have fully unbonded. The pools
	/// of `Self::with_era` will lazily be merged into into this pool if they are
	/// older then `current_era - TotalUnbondingPools`.
	no_era: UnbondPool<T>,
	/// Map of era => unbond pools.
	with_era: SubPoolsWithEra<T>,
}

impl<T: Config> SubPools<T> {
	/// Merge the oldest `with_era` unbond pools into the `no_era` unbond pool.
	fn maybe_merge_pools(mut self, unbond_era: EraIndex) -> Self {
		if unbond_era < TotalUnbondingPools::<T>::get().into() {
			// For the first `0..TotalUnbondingPools` eras of the chain we don't need to do
			// anything. Ex: if `TotalUnbondingPools` is 5 and we are in era 4 we can add a pool
			// for this era and have exactly `TotalUnbondingPools` pools.
			return self
		}

		// Ex: if `TotalUnbondingPools` is 5 and current era is 10, we only want to retain pools
		// 6..=10.
		let newest_era_to_remove = unbond_era.saturating_sub(TotalUnbondingPools::<T>::get());

		let eras_to_remove: Vec<_> = self
			.with_era
			.keys()
			.cloned()
			.filter(|era| *era <= newest_era_to_remove)
			.collect();
		for era in eras_to_remove {
			if let Some(p) = self.with_era.remove(&era) {
				self.no_era.points = self.no_era.points.saturating_add(p.points);
				self.no_era.balance = self.no_era.balance.saturating_add(p.balance);
			}
		}

		self
	}

	/// Get the unbond pool for `era`. If one does not exist a default entry will be inserted.
	///
	/// The caller must ensure that the `SubPools::with_era` has room for 1 more entry. Calling
	/// [`SubPools::maybe_merge_pools`] with the current era should the sub pools are in an ok state
	/// to call this method.
	fn unchecked_with_era_get_or_make(&mut self, era: EraIndex) -> &mut UnbondPool<T> {
		if !self.with_era.contains_key(&era) {
			self.with_era
				.try_insert(era, UnbondPool::default())
				.expect("caller has checked pre-conditions. qed.");
		}

		self.with_era.get_mut(&era).expect("entry inserted on the line above. qed.")
	}
}

/// The maximum amount of eras an unbonding pool can exist prior to being merged with the
/// `no_era` pool. This is guaranteed to at least be equal to the staking `UnbondingDuration`. For
/// improved UX [`Config::PostUnbondingPoolsWindow`] should be configured to a non-zero value.
pub struct TotalUnbondingPools<T: Config>(PhantomData<T>);
impl<T: Config> Get<u32> for TotalUnbondingPools<T> {
	fn get() -> u32 {
		// TODO: This may be too dangerous in the scenario bonding_duration gets decreased because
		// we would no longer be able to decode `SubPoolsWithEra`, which uses `TotalUnbondingPools`
		// as the bound
		T::StakingInterface::bonding_duration() + T::PostUnbondingPoolsWindow::get()
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::{ensure_signed, pallet_prelude::*};

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		// TODO: Should this just be part of the StakingInterface trait? We want the currencies to
		// be the same anyways
		/// The nominating balance.
		type Currency: Currency<Self::AccountId>;

		// Infallible method for converting `Currency::Balance` to `U256`.
		type BalanceToU256: Convert<BalanceOf<Self>, U256>;

		// Infallible method for converting `U256` to `Currency::Balance`.
		type U256ToBalance: Convert<U256, BalanceOf<Self>>;

		/// The interface for nominating.
		type StakingInterface: StakingInterface<
			Balance = BalanceOf<Self>,
			AccountId = Self::AccountId,
			LookupSource = <Self::Lookup as StaticLookup>::Source,
		>;

		/// The amount of eras a `SubPools::with_era` pool can exist before it gets merged into the
		/// `SubPools::no_era` pool. In other words, this is the amount of eras a delegator will be
		/// able to withdraw from an unbonding pool which is guaranteed to have the correct ratio of
		/// points to balance; once the `with_era` pool is merged into the `no_era` pool, the ratio
		/// can become skewed due to some slashed ratio getting merged in at some point.
		type PostUnbondingPoolsWindow: Get<u32>;

		/// The maximum length, in bytes, that a pools metadata maybe.
		type MaxMetadataLen: Get<u32>;
	}

	/// Minimum amount to bond to join a pool.
	#[pallet::storage]
	pub type MinJoinBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Minimum bond required to create a pool.
	#[pallet::storage]
	pub type MinCreateBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Maximum number of nomination pools that can exist. If `None`, then an unbounded number of
	/// pools can exist.
	#[pallet::storage]
	pub type MaxPools<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// Maximum number of delegators that can exist in the system. If `None`, then the count
	/// delegators are not bound on a system wide basis.
	#[pallet::storage]
	pub type MaxDelegators<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// Maximum number of delegators that may belong to pool. If `None`, then the count of
	/// delegators is not bound on a per pool basis.
	#[pallet::storage]
	pub type MaxDelegatorsPerPool<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// Active delegators.
	#[pallet::storage]
	pub type Delegators<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator<T>>;

	/// To get or insert a pool see [`BondedPool::get`] and [`BondedPool::put`]
	#[pallet::storage]
	pub type BondedPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, BondedPoolStorage<T>>;
	// CountedStorageMap<_, Twox64Concat, T::AccountId, BondedPoolStorage<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool. Keyed by the bonded pools
	/// _Stash_/_Controller_.
	#[pallet::storage]
	pub type RewardPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a bonded pool,
	/// hence the name sub-pools. Keyed by the bonded pools _Stash_/_Controller_.
	#[pallet::storage]
	pub type SubPoolsStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, SubPools<T>>;

	/// Metadata for the pool
	#[pallet::storage]
	pub type Metadata<T: Config> = CountedStorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		BoundedVec<u8, T::MaxMetadataLen>,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub min_join_bond: BalanceOf<T>,
		pub min_create_bond: BalanceOf<T>,
		pub max_pools: Option<u32>,
		pub max_delegators_per_pool: Option<u32>,
		pub max_delegators: Option<u32>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				min_join_bond: Zero::zero(),
				min_create_bond: Zero::zero(),
				max_pools: Some(16),
				max_delegators_per_pool: Some(32),
				max_delegators: Some(16 * 32),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			MinJoinBond::<T>::put(self.min_join_bond);
			MinCreateBond::<T>::put(self.min_create_bond);
			if let Some(max_pools) = self.max_pools {
				MaxPools::<T>::put(max_pools);
			}
			if let Some(max_delegators_per_pool) = self.max_delegators_per_pool {
				MaxDelegatorsPerPool::<T>::put(max_delegators_per_pool);
			}
			if let Some(max_delegators) = self.max_delegators {
				MaxDelegators::<T>::put(max_delegators);
			}
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		Created { pool: T::AccountId, depositor: T::AccountId },
		Joined { delegator: T::AccountId, pool: T::AccountId, bonded: BalanceOf<T> },
		PaidOut { delegator: T::AccountId, pool: T::AccountId, payout: BalanceOf<T> },
		Unbonded { delegator: T::AccountId, pool: T::AccountId, amount: BalanceOf<T> },
		Withdrawn { delegator: T::AccountId, pool: T::AccountId, amount: BalanceOf<T> },
		Destroyed { pool: T::AccountId },
	}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// A (bonded) pool id does not exist.
		PoolNotFound,
		/// An account is not a delegator.
		DelegatorNotFound,
		/// A reward pool does not exist. In all cases this is a system logic error.
		RewardPoolNotFound,
		/// A sub pool does not exist.
		SubPoolsNotFound,
		/// An account is already delegating in another pool. An account may only belong to one
		/// pool at a time.
		AccountBelongsToOtherPool,
		/// The pool has insufficient balance to bond as a nominator.
		InsufficientBond,
		/// The delegator is already unbonding.
		AlreadyUnbonding,
		/// The delegator is not unbonding and thus cannot withdraw funds.
		NotUnbonding,
		/// Unbonded funds cannot be withdrawn yet because the bonding duration has not passed.
		NotUnbondedYet,
		/// The amount does not meet the minimum bond to either join or create a pool.
		MinimumBondNotMet,
		/// The transaction could not be executed due to overflow risk for the pool.
		OverflowRisk,
		// Likely only an error ever encountered in poorly built tests.
		/// A pool with the generated account id already exists.
		IdInUse,
		/// A pool must be in [`PoolState::Destroying`] in order for the depositor to unbond or for
		/// other delegators to be permissionlessly unbonded.
		NotDestroying,
		/// The depositor must be the only delegator in the bonded pool in order to unbond. And the
		/// depositor must be the only delegator in the sub pools in order to withdraw unbonded.
		NotOnlyDelegator,
		/// The caller does not have nominating permissions for the pool.
		NotNominator,
		/// Either a) the caller cannot make a valid kick or b) the pool is not destroying.
		NotKickerOrDestroying,
		/// The pool is not open to join
		NotOpen,
		/// The system is maxed out on pools.
		MaxPools,
		/// Too many delegators in the pool or system.
		MaxDelegators,
		/// The pools state cannot be changed.
		CanNotChangeState,
		/// The caller does not have adequate permissions.
		DoesNotHavePermission,
		/// Metadata exceeds [`T::MaxMetadataLen`]
		MetadataExceedsMaxLen,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Stake funds with a pool. The amount to bond is transferred from the delegator to the
		/// pools account and immediately increases the pools bond.
		///
		/// # Note
		///
		/// * An account can only be a member of a single pool.
		/// * This call will *not* dust the delegator account, so the delegator must have at least
		///   `existential deposit + amount` in their account.
		/// * Only a pool with [`PoolState::Open`] can be joined
		#[pallet::weight(T::WeightInfo::join())]
		#[frame_support::transactional]
		pub fn join(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
			pool_account: T::AccountId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// // TODO: consider merging these checks into ok_to_join_with, also use the same
			// checker // functions in `fn create()`.
			// ensure!(amount >= MinJoinBond::<T>::get(), Error::<T>::MinimumBondNotMet);
			// // If a delegator already exists that means they already belong to a pool
			// ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			let mut bonded_pool =
				BondedPool::<T>::get(&pool_account).ok_or(Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_join_with(amount, &who)?;
			bonded_pool.inc_delegators()?;

			// TODO: seems like a lot of this and `create` can be factored into a `do_join`. We
			// don't actually care about writing the reward pool, we just need its total earnings at
			// this point in time.
			let reward_pool = RewardPool::<T>::get_and_update(&pool_account)
				.defensive_ok_or_else(|| Error::<T>::RewardPoolNotFound)?;

			// // Transfer the funds to be bonded from `who` to the pools account so the pool can then
			// // go bond them.
			// T::Currency::transfer(&who, &pool_account, amount, ExistenceRequirement::KeepAlive)?;

			// // We must calculate the points to issue *before* we bond `who`'s funds, else the
			// // points:balance ratio will be wrong.
			// let new_points = bonded_pool.issue(amount);
			// // The pool should always be created in such a way its in a state to bond extra, but if
			// // the active balance is slashed below the minimum bonded or the account cannot be
			// // found, we exit early.
			// T::StakingInterface::bond_extra(pool_account.clone(), amount)?;

			let points_issued = bonded_pool.try_bond_delegator(&who, amount, PoolBond::Join)?;

			Delegators::insert(
				who.clone(),
				Delegator::<T> {
					pool: pool_account.clone(),
					points: points_issued,
					// At best the reward pool has the rewards up through the previous era. If the
					// delegator joins prior to the snapshot they will benefit from the rewards of
					// the active era despite not contributing to the pool's vote weight. If they
					// join after the snapshot is taken they will benefit from the rewards of the
					// next 2 eras because their vote weight will not be counted until the
					// snapshot in active era + 1.
					reward_pool_total_earnings: reward_pool.total_earnings,
					unbonding_era: None,
				},
			);
			bonded_pool.put();
			Self::deposit_event(Event::<T>::Joined {
				delegator: who,
				pool: pool_account,
				bonded: amount,
			});

			Ok(())
		}

		/// A bonded delegator can use this to claim their payout based on the rewards that the pool
		/// has accumulated since their last claimed payout (OR since joining if this is there first
		/// time claiming rewards). The payout will be transffered to the delegator's account.
		///
		/// The delegator will earn rewards pro rata based on the delegators stake vs the sum of the
		/// delegators in the pools stake. Rewards do not "expire".
		#[pallet::weight(T::WeightInfo::claim_payout())]
		pub fn claim_payout(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let bonded_pool = BondedPool::<T>::get(&delegator.pool)
				.defensive_ok_or_else(|| Error::<T>::PoolNotFound)?;

			Self::do_reward_payout(who, delegator, &bonded_pool)?;

			Ok(())
		}

		/// Unbond _all_ of the `target` delegators funds from the pool. Under certain conditions,
		/// this call can be dispatched permissionlessly (i.e. by any account).
		///
		/// # Conditions for a permissionless dispatch
		///
		/// * The pool is blocked and the caller is either the root or state-toggler. This is
		///   refereed to as a kick.
		/// * The pool is destroying and the delegator is not the depositor.
		/// * The pool is destroying, the delegator is the depositor and no other delegators are in
		///   the pool.
		///
		/// # Conditions for permissioned dispatch (i.e. the caller is also the target):
		///
		/// * The caller is not the depositor.
		/// * The caller is the depositor, the pool is destroying and no other delegators are in the
		///   pool.
		///
		/// Note: If their are too many unlocking chunks to unbond with the pool account,
		/// [`Self::withdraw_unbonded_pool`] can be called to try and minimize unlocking chunks.
		#[pallet::weight(T::WeightInfo::unbond_other())]
		pub fn unbond_other(origin: OriginFor<T>, target: T::AccountId) -> DispatchResult {
			let caller = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&target).ok_or(Error::<T>::DelegatorNotFound)?;
			let mut bonded_pool = BondedPool::<T>::get(&delegator.pool)
				.defensive_ok_or_else(|| Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_unbond_other_with(&caller, &target, &delegator)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points
			// no longer exist in the bonded pool and thus they can no longer claim their payouts.
			// It is not strictly necessary to claim the rewards, but we do it here for UX.
			Self::do_reward_payout(target.clone(), delegator, &bonded_pool)?;

			// Re-fetch the delegator because they where updated by `do_reward_payout`.
			let mut delegator =
				Delegators::<T>::get(&target).ok_or(Error::<T>::DelegatorNotFound)?;
			// Note that we lazily create the unbonding pools here if they don't already exist
			let sub_pools = SubPoolsStorage::<T>::get(&delegator.pool).unwrap_or_default();
			let current_era = T::StakingInterface::current_era();
			let unbond_era = T::StakingInterface::bonding_duration().saturating_add(current_era);

			let balance_to_unbond = bonded_pool.balance_to_unbond(delegator.points);

			// Update the bonded pool. Note that we must do this *after* calculating the balance
			// to unbond so we have the correct points for the balance:share ratio.
			bonded_pool.points = bonded_pool.points.saturating_sub(delegator.points);

			// Unbond in the actual underlying pool
			T::StakingInterface::unbond(delegator.pool.clone(), balance_to_unbond)?;

			// Merge any older pools into the general, era agnostic unbond pool. Note that we do
			// this before inserting to ensure we don't go over the max unbonding pools.
			let mut sub_pools = sub_pools.maybe_merge_pools(unbond_era);

			// Update the unbond pool associated with the current era with the
			// unbonded funds. Note that we lazily create the unbond pool if it
			// does not yet exist.
			sub_pools.unchecked_with_era_get_or_make(unbond_era).issue(balance_to_unbond);

			delegator.unbonding_era = Some(unbond_era);

			Self::deposit_event(Event::<T>::Unbonded {
				delegator: target.clone(),
				pool: delegator.pool.clone(),
				amount: balance_to_unbond,
			});
			// Now that we know everything has worked write the items to storage.
			bonded_pool.put();
			SubPoolsStorage::insert(&delegator.pool, sub_pools);
			Delegators::insert(target, delegator);

			Ok(())
		}

		/// Call `withdraw_unbonded` for the pools account. This call can be made by any account.
		///
		/// This is useful if their are too many unlocking chunks to call `unbond_other`, and some
		/// can be cleared by withdrawing.
		#[pallet::weight(T::WeightInfo::pool_withdraw_unbonded(*num_slashing_spans))]
		pub fn pool_withdraw_unbonded(
			origin: OriginFor<T>,
			pool_account: T::AccountId,
			num_slashing_spans: u32,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			let pool = BondedPool::<T>::get(&pool_account).ok_or(Error::<T>::PoolNotFound)?;
			// For now we only allow a pool to withdraw unbonded if its not destroying. If the pool
			// is destroying then `withdraw_unbonded_other` can be used.
			ensure!(pool.state != PoolState::Destroying, Error::<T>::NotDestroying);
			T::StakingInterface::withdraw_unbonded(pool_account, num_slashing_spans)?;
			Ok(())
		}

		/// Withdraw unbonded funds for the `target` delegator. Under certain conditions,
		/// this call can be dispatched permissionlessly (i.e. by any account).
		///
		///  # Conditions for a permissionless dispatch
		///
		/// * The pool is in destroy mode and the target is not the depositor.
		/// * The target is the depositor and they are the only delegator in the sub pools.
		/// * The pool is blocked and the caller is either the root or state-toggler.
		///
		///  # Conditions for permissioned dispatch
		///
		/// * The caller is the target and they are not the depositor.
		///
		/// # Note
		///
		/// If the target is the depositor, the pool will be destroyed.
		#[pallet::weight(
			T::WeightInfo::withdraw_unbonded_other_kill(*num_slashing_spans)
		)]
		pub fn withdraw_unbonded_other(
			origin: OriginFor<T>,
			target: T::AccountId,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let caller = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&target).ok_or(Error::<T>::DelegatorNotFound)?;
			let unbonding_era = delegator.unbonding_era.ok_or(Error::<T>::NotUnbonding)?;
			let current_era = T::StakingInterface::current_era();
			ensure!(current_era >= unbonding_era, Error::<T>::NotUnbondedYet);

			let mut sub_pools = SubPoolsStorage::<T>::get(&delegator.pool)
				.defensive_ok_or_else(|| Error::<T>::SubPoolsNotFound)?;
			let bonded_pool = BondedPool::<T>::get(&delegator.pool)
				.defensive_ok_or_else(|| Error::<T>::PoolNotFound)?;
			let should_remove_pool = bonded_pool
				.ok_to_withdraw_unbonded_other_with(&caller, &target, &delegator, &sub_pools)?;

			// Before calculate the `balance_to_unbond`, with call withdraw unbonded to ensure the
			// `non_locked_balance` is correct.
			T::StakingInterface::withdraw_unbonded(delegator.pool.clone(), num_slashing_spans)?;

			let balance_to_unbond =
				if let Some(pool) = sub_pools.with_era.get_mut(&unbonding_era) {
					let balance_to_unbond = pool.balance_to_unbond(delegator.points);
					pool.points = pool.points.saturating_sub(delegator.points);
					pool.balance = pool.balance.saturating_sub(balance_to_unbond);
					if pool.points.is_zero() {
						// Clean up pool that is no longer used
						sub_pools.with_era.remove(&unbonding_era);
					}

					balance_to_unbond
				} else {
					// A pool does not belong to this era, so it must have been merged to the
					// era-less pool.
					let balance_to_unbond = sub_pools.no_era.balance_to_unbond(delegator.points);
					sub_pools.no_era.points =
						sub_pools.no_era.points.saturating_sub(delegator.points);
					sub_pools.no_era.balance =
						sub_pools.no_era.balance.saturating_sub(balance_to_unbond);

					balance_to_unbond
				}
				// A call to this function may cause the pool's stash to get dusted. If this happens
				// before the last delegator has withdrawn, then all subsequent withdraws will be 0.
				// However the unbond pools do no get updated to reflect this. In the aforementioned
				// scenario, this check ensures we don't try to withdraw funds that don't exist.
				// This check is also defensive in cases where the unbond pool does not update its
				// balance (e.g. a bug in the slashing hook.) We gracefully proceed in
				// order to ensure delegators can leave the pool and it can be destroyed.
				.min(bonded_pool.non_locked_balance());

			T::Currency::transfer(
				&delegator.pool,
				&target,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)
			.defensive_map_err(|e| e)?;
			Self::deposit_event(Event::<T>::Withdrawn {
				delegator: target.clone(),
				pool: delegator.pool.clone(),
				amount: balance_to_unbond,
			});

			let post_info_weight = if should_remove_pool {
				let reward_pool = RewardPools::<T>::take(&delegator.pool)
					.defensive_ok_or_else(|| Error::<T>::PoolNotFound)?;
				Self::deposit_event(Event::<T>::Destroyed { pool: delegator.pool.clone() });
				SubPoolsStorage::<T>::remove(&delegator.pool);
				// Kill accounts from storage by making their balance go below ED. We assume that
				// the accounts have no references that would prevent destruction once we get to
				// this point.
				T::Currency::make_free_balance_be(&reward_pool.account, Zero::zero());
				T::Currency::make_free_balance_be(&bonded_pool.account, Zero::zero());
				bonded_pool.remove();
				None
			} else {
				bonded_pool.dec_delegators().put();
				SubPoolsStorage::<T>::insert(&delegator.pool, sub_pools);
				Some(T::WeightInfo::withdraw_unbonded_other_update(num_slashing_spans))
			};
			Delegators::<T>::remove(&target);

			Ok(post_info_weight.into())
		}

		/// Create a new delegation pool.
		///
		/// # Arguments
		///
		/// * `amount` - The amount of funds to delegate to the pool. This also acts of a sort of
		///   deposit since the pools creator cannot fully unbond funds until the pool is being
		///   destroyed.
		/// * `index` - A disambiguation index for creating the account. Likely only useful when
		///   creating multiple pools in the same extrinsic.
		/// * `root` - The account to set as [`BondedPool::root`].
		/// * `nominator` - The account to set as the [`BondedPool::nominator`].
		/// * `state_toggler` - The account to set as the [`BondedPool::state_toggler`].
		#[pallet::weight(T::WeightInfo::create())]
		#[frame_support::transactional]
		pub fn create(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
			root: T::AccountId,
			nominator: T::AccountId,
			state_toggler: T::AccountId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(
				amount >= T::StakingInterface::minimum_bond() &&
					amount >= MinCreateBond::<T>::get(),
				Error::<T>::MinimumBondNotMet
			);
			ensure!(
				MaxPools::<T>::get()
					.map_or(true, |max_pools| BondedPools::<T>::count() < max_pools),
				Error::<T>::MaxPools
			);
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			let mut bonded_pool = BondedPool::<T>::new(who.clone(), root, nominator, state_toggler);
			// This shouldn't be possible since we are ensured the delegator is not a depositor and
			// the the account ID is generated based on the accountId
			ensure!(!BondedPools::<T>::contains_key(&bonded_pool.account), Error::<T>::IdInUse);
			bonded_pool.inc_delegators()?;

			let points_issued =
				bonded_pool.try_bond_delegator(&who, amount, PoolBond::Create)?;

			// TODO: make these one function that does this in the correct order
			// We must calculate the points issued *before* we bond who's funds, else points:balance
			// ratio will be wrong.
			// T::Currency::transfer(
			// 	&who,
			// 	&bonded_pool.account,
			// 	amount,
			// 	ExistenceRequirement::AllowDeath,
			// )?;
			// let points_issued = bonded_pool.issue(amount);
			// // Consider making StakingInterface use reference.
			// T::StakingInterface::bond(
			// 	bonded_pool.account.clone(),
			// 	// We make the stash and controller the same for simplicity
			// 	bonded_pool.account.clone(),
			// 	amount,
			// 	bonded_pool.reward_account(),
			// )?;

			Self::deposit_event(Event::<T>::Created {
				depositor: who.clone(),
				pool: bonded_pool.account.clone(),
			});
			Delegators::<T>::insert(
				who,
				Delegator::<T> {
					pool: bonded_pool.account.clone(),
					points: points_issued,
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None,
				},
			);
			RewardPools::<T>::insert(
				bonded_pool.account.clone(),
				RewardPool::<T> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account: bonded_pool.reward_account(),
				},
			);
			bonded_pool.put();

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::nominate())]
		pub fn nominate(
			origin: OriginFor<T>,
			pool_account: T::AccountId,
			validators: Vec<<T::Lookup as StaticLookup>::Source>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let bonded_pool =
				BondedPool::<T>::get(&pool_account).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_nominate(&who), Error::<T>::NotNominator);
			T::StakingInterface::nominate(pool_account.clone(), validators)?;
			Ok(())
		}

		#[pallet::weight(T::WeightInfo::set_state_other())]
		pub fn set_state_other(
			origin: OriginFor<T>,
			pool_account: T::AccountId,
			state: PoolState,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut bonded_pool =
				BondedPool::<T>::get(&pool_account).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.state != PoolState::Destroying, Error::<T>::CanNotChangeState);

			// TODO: [now] we could  check if bonded_pool.ok_to_be_open().is_err(), and if thats
			// true always set the state to destroying, regardless of the stat the caller passes.
			// The downside is that this seems like a misleading API

			if bonded_pool.can_toggle_state(&who) {
				bonded_pool.state = state
			} else if bonded_pool.ok_to_be_open().is_err() && state == PoolState::Destroying {
				// If the pool has bad properties, then anyone can set it as destroying
				bonded_pool.state = PoolState::Destroying;
			} else {
				Err(Error::<T>::CanNotChangeState)?;
			}

			bonded_pool.put();

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::set_metadata())]
		pub fn set_metadata(
			origin: OriginFor<T>,
			pool_account: T::AccountId,
			metadata: Vec<u8>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let metadata: BoundedVec<_, _> =
				metadata.try_into().map_err(|_| Error::<T>::MetadataExceedsMaxLen)?;
			ensure!(
				BondedPool::<T>::get(&pool_account)
					.ok_or(Error::<T>::PoolNotFound)?
					.can_set_metadata(&who),
				Error::<T>::DoesNotHavePermission
			);

			Metadata::<T>::mutate(&pool_account, |pool_meta| *pool_meta = metadata);

			Ok(())
		}

		// Set
		// * `min_join_bond`
		// * `min_create_bond`
		// * `max_pools`
		// * `max_delegators_per_pool`
		// * `max_delegators`
		// pub fn set_parameters(origin: OriginFor<T>, ) -> DispatchResult {

		// }
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(
				T::StakingInterface::bonding_duration() < TotalUnbondingPools::<T>::get(),
				"There must be more unbonding pools then the bonding duration /
				so a slash can be applied to relevant unboding pools. (We assume /
				the bonding duration > slash deffer duration.",
			);
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Calculate the rewards for `delegator`.
	fn calculate_delegator_payout(
		bonded_pool: &BondedPool<T>,
		mut reward_pool: RewardPool<T>,
		mut delegator: Delegator<T>,
	) -> Result<(RewardPool<T>, Delegator<T>, BalanceOf<T>), DispatchError> {
		let u256 = |x| T::BalanceToU256::convert(x);
		// If the delegator is unbonding they cannot claim rewards. Note that when the delegator
		// goes to unbond, the unbond function should claim rewards for the final time.
		ensure!(delegator.unbonding_era.is_none(), Error::<T>::AlreadyUnbonding);

		let last_total_earnings = reward_pool.total_earnings;
		reward_pool.update_total_earnings_and_balance();

		// Notice there is an edge case where total_earnings have not increased and this is zero
		let new_earnings = u256(reward_pool.total_earnings.saturating_sub(last_total_earnings));

		// The new points that will be added to the pool. For every unit of balance that has been
		// earned by the reward pool, we inflate the reward pool points by `bonded_pool.points`. In
		// effect this allows each, single unit of balance (e.g. plank) to be divvied up pro rata
		// among delegators based on points.
		let new_points = u256(bonded_pool.points).saturating_mul(new_earnings);

		// The points of the reward pool after taking into account the new earnings. Notice that
		// this only stays even or increases over time except for when we subtract delegator virtual
		// shares.
		let current_points = reward_pool.points.saturating_add(new_points);

		// The rewards pool's earnings since the last time this delegator claimed a payout.
		let new_earnings_since_last_claim =
			reward_pool.total_earnings.saturating_sub(delegator.reward_pool_total_earnings);

		// The points of the reward pool that belong to the delegator.
		let delegator_virtual_points =
			u256(delegator.points).saturating_mul(u256(new_earnings_since_last_claim));

		let delegator_payout = if delegator_virtual_points.is_zero() ||
			current_points.is_zero() ||
			reward_pool.balance.is_zero()
		{
			Zero::zero()
		} else {
			// Equivalent to `(delegator_virtual_points / current_points) * reward_pool.balance`
			T::U256ToBalance::convert(
				delegator_virtual_points
					.saturating_mul(u256(reward_pool.balance))
					// We check for zero above
					.div(current_points),
			)
		};

		// Record updates
		delegator.reward_pool_total_earnings = reward_pool.total_earnings;
		reward_pool.points = current_points.saturating_sub(delegator_virtual_points);
		reward_pool.balance = reward_pool.balance.saturating_sub(delegator_payout);

		Ok((reward_pool, delegator, delegator_payout))
	}

	fn do_reward_payout(
		// TODO :doesn't delegator have its id?
		delegator_id: T::AccountId,
		delegator: Delegator<T>, // TODO: make clear this is mut
		bonded_pool: &BondedPool<T>,
	) -> DispatchResult {
		let reward_pool = RewardPools::<T>::get(&delegator.pool)
			.defensive_ok_or_else(|| Error::<T>::RewardPoolNotFound)?;

		let (reward_pool, delegator, delegator_payout) =
			Self::calculate_delegator_payout(bonded_pool, reward_pool, delegator)?;

		// Transfer payout to the delegator.
		T::Currency::transfer(
			&reward_pool.account,
			&delegator_id,
			delegator_payout,
			ExistenceRequirement::AllowDeath,
		)?;
		Self::deposit_event(Event::<T>::PaidOut {
			delegator: delegator_id.clone(),
			pool: delegator.pool.clone(),
			payout: delegator_payout,
		});

		// Write the updated delegator and reward pool to storage
		RewardPools::insert(&delegator.pool, reward_pool);
		Delegators::insert(delegator_id, delegator);

		Ok(())
	}
}

impl<T: Config> OnStakerSlash<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_slash(
		pool_account: &T::AccountId,
		_slashed_bonded: BalanceOf<T>, // Bonded balance is always read directly from staking.
		slashed_unlocking: &BTreeMap<EraIndex, BalanceOf<T>>,
	) {
		let mut sub_pools = match SubPoolsStorage::<T>::get(pool_account) {
			Some(sub_pools) => sub_pools,
			None => return,
		};
		for (era, slashed_balance) in slashed_unlocking.iter() {
			if let Some(pool) = sub_pools.with_era.get_mut(era) {
				pool.balance = *slashed_balance
			}
		}
		SubPoolsStorage::<T>::insert(pool_account.clone(), sub_pools);
	}
}
