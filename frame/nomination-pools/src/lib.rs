//! # Nomination Pools for Staking Delegation
//!
//! A pallet that allows delegators to delegate their stake to nominating pools. A nomination pool
//! acts as nominator and nominates validators on the delegators behalf. # Index
//!
//! * [Key terms](#key-terms)
//! * [Usage](#usage)
//! * [Design](#design)
//!
//! ## Key terms
//!
//!  * bonded pool: Tracks the distribution of actively staked funds. See [`BondedPool`] and
//! [`BondedPoolInner`]. Bonded pools are identified via the pools bonded account.
//! * reward pool: Tracks rewards earned by actively staked funds. See [`RewardPool`] and
//!   [`RewardPools`]. Reward pools are identified via the pools bonded account.
//! * unbonding sub pools: Collection of pools at different phases of the unbonding lifecycle. See
//!   [`SubPools`] and [`SubPoolsStorage`]. Sub pools are identified via the pools bonded account.
//! * delegators: Accounts that are members of pools. See [`Delegator`] and [`Delegators`].
//!   Delegators are identified via their account.
//! * point: A unit of measure for a delegators portion of a pool's funds.
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
//! A pool has 3 administrative roles (see [`PoolRoles`]):
//!
//! * Depositor: creates the pool and is the initial delegator. They can only leave pool once all
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
//! in addition to the unbonding pools. For maintenance simplicity these are not implemented.
//! Related: https://github.com/paritytech/substrate/issues/10860
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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use frame_support::{
	ensure,
	pallet_prelude::{MaxEncodedLen, *},
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{
		Currency, Defensive, DefensiveOption, DefensiveResult, DefensiveSaturating,
		ExistenceRequirement, Get,
	},
	DefaultNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_core::U256;
use sp_runtime::traits::{AccountIdConversion, Bounded, Convert, Saturating, Zero};
use sp_staking::{EraIndex, OnStakerSlash, StakingInterface};
use sp_std::{collections::btree_map::BTreeMap, fmt::Debug, ops::Div, vec::Vec};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type SubPoolsWithEra<T> = BoundedBTreeMap<EraIndex, UnbondPool<T>, TotalUnbondingPools<T>>;
pub type RewardPoints = U256;
pub type PoolId = u32;

const POINTS_TO_BALANCE_INIT_RATIO: u32 = 1;

/// Possible operations on the configuration values of this pallet.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound, PartialEq, Clone)]
pub enum ConfigOp<T: Default + Codec + Debug> {
	/// Don't change.
	Noop,
	/// Set the given value.
	Set(T),
	/// Remove from storage.
	Remove,
}

/// The type of binding that can happen to a pool.
enum BondType {
	/// Someone is bonding into the pool upon creation.
	Create,
	/// Someone is adding more funds later to this pool.
	Later,
}

/// How to increase the bond of a delegator.
#[derive(Encode, Decode, Clone, Copy, Debug, PartialEq, Eq, TypeInfo)]
pub enum BondExtra<Balance> {
	/// Take from the free balance.
	FreeBalance(Balance),
	/// Take the entire amount from the accumulated rewards.
	Rewards,
}

/// The type of account being created.
#[derive(Encode, Decode)]
enum AccountType {
	Bonded,
	Reward,
}

/// A delegator in a pool.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Delegator<T: Config> {
	/// The identifier of the pool to which `who` belongs.
	pub pool_id: PoolId,
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
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, RuntimeDebugNoBound, Clone, Copy)]
pub enum PoolState {
	/// The pool is open to be joined, and is working normally.
	Open,
	/// The pool is blocked. No one else can join.
	Blocked,
	/// The pool is in the process of being destroyed.
	///
	/// All delegators can now be permissionlessly unbonded, and the pool can never go back to any
	/// other state other than being dissolved.
	Destroying,
}

/// Pool adminstration roles.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Debug, PartialEq, Clone)]
pub struct PoolRoles<AccountId> {
	/// Creates the pool and is the initial delegator. They can only leave the pool once all
	/// other delegators have left. Once they fully leave, the pool is destroyed.
	pub depositor: AccountId,
	/// Can change the nominator, state-toggler, or itself and can perform any of the actions
	/// the nominator or state-toggler can.
	pub root: AccountId,
	/// Can select which validators the pool nominates.
	pub nominator: AccountId,
	/// can change the pools state and kick delegators if the pool is blocked.
	pub state_toggler: AccountId,
}

/// Pool permissions and state
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DebugNoBound, PartialEq, Clone)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct BondedPoolInner<T: Config> {
	/// See [`BondedPool::points`].
	pub points: BalanceOf<T>,
	/// See [`BondedPool::state_toggler`].
	pub state: PoolState,
	/// See [`BondedPool::delegator_counter`]
	pub delegator_counter: u32,
	/// See [`PoolRoles`].
	pub roles: PoolRoles<T::AccountId>,
}

/// A wrapper for bonded pools, with utility functions.
///
/// The main purpose of this is to wrap a [`BondedPoolInner`], with the account + id of the pool,
/// for easier access.
#[derive(RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
pub struct BondedPool<T: Config> {
	/// The identifier of the pool.
	id: PoolId,
	/// The inner fields.
	inner: BondedPoolInner<T>,
}

impl<T: Config> sp_std::ops::Deref for BondedPool<T> {
	type Target = BondedPoolInner<T>;
	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl<T: Config> sp_std::ops::DerefMut for BondedPool<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner
	}
}

impl<T: Config> BondedPool<T> {
	/// Create a new bonded pool with the given roles and identifier.
	fn new(id: PoolId, roles: PoolRoles<T::AccountId>) -> Self {
		Self {
			id,
			inner: BondedPoolInner {
				roles,
				state: PoolState::Open,
				points: Zero::zero(),
				delegator_counter: Zero::zero(),
			},
		}
	}

	/// Get [`Self`] from storage. Returns `None` if no entry for `pool_account` exists.
	fn get(id: PoolId) -> Option<Self> {
		BondedPools::<T>::try_get(id).ok().map(|inner| Self { id, inner })
	}

	/// Get the bonded account id of this pool.
	fn bonded_account(&self) -> T::AccountId {
		Pallet::<T>::create_bonded_account(self.id)
	}

	/// Get the reward account id of this pool.
	fn reward_account(&self) -> T::AccountId {
		Pallet::<T>::create_reward_account(self.id)
	}

	/// Consume self and put into storage.
	fn put(self) {
		BondedPools::<T>::insert(self.id, BondedPoolInner { ..self.inner });
	}

	/// Consume self and remove from storage.
	fn remove(self) {
		BondedPools::<T>::remove(self.id);
	}

	/// Get the amount of points to issue for some new funds that will be bonded in the pool.
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		Pallet::<T>::points_to_issue(bonded_balance, self.points, new_funds)
	}

	/// Get the amount of balance to unbond from the pool based on a delegator's points of the pool.
	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		Pallet::<T>::balance_to_unbond(bonded_balance, self.points, delegator_points)
	}

	/// Issue points to [`Self`] for `new_funds`.
	fn issue(&mut self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let points_to_issue = self.points_to_issue(new_funds);
		self.points = self.points.saturating_add(points_to_issue);

		points_to_issue
	}

	/// Increment the delegator counter. Ensures that the pool and system delegator limits are
	/// respected.
	fn try_inc_delegators(&mut self) -> Result<(), DispatchError> {
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

	/// The pools balance that is transferrable.
	fn transferrable_balance(&self) -> BalanceOf<T> {
		let account = self.bonded_account();
		T::Currency::free_balance(&account)
			.saturating_sub(T::StakingInterface::active_stake(&account).unwrap_or_default())
	}

	fn can_nominate(&self, who: &T::AccountId) -> bool {
		*who == self.roles.root || *who == self.roles.nominator
	}

	fn can_kick(&self, who: &T::AccountId) -> bool {
		*who == self.roles.root ||
			*who == self.roles.state_toggler && self.state == PoolState::Blocked
	}

	fn can_toggle_state(&self, who: &T::AccountId) -> bool {
		*who == self.roles.root || *who == self.roles.state_toggler && !self.is_destroying()
	}

	fn can_set_metadata(&self, who: &T::AccountId) -> bool {
		*who == self.roles.root || *who == self.roles.state_toggler
	}

	fn is_destroying(&self) -> bool {
		matches!(self.state, PoolState::Destroying)
	}

	/// Whether or not the pool is ok to be in `PoolSate::Open`. If this returns an `Err`, then the
	/// pool is unrecoverable and should be in the destroying state.
	fn ok_to_be_open(&self) -> Result<(), DispatchError> {
		ensure!(!self.is_destroying(), Error::<T>::CanNotChangeState);

		let bonded_balance =
			T::StakingInterface::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		ensure!(!bonded_balance.is_zero(), Error::<T>::OverflowRisk);

		let points_to_balance_ratio_floor = self
			.points
			// We checked for zero above
			.div(bonded_balance);

		// Pool points can inflate relative to balance, but only if the pool is slashed.
		// If we cap the ratio of points:balance so one cannot join a pool that has been slashed
		// 90%,
		ensure!(points_to_balance_ratio_floor < 10u32.into(), Error::<T>::OverflowRisk);
		// while restricting the balance to 1/10th of max total issuance,
		ensure!(
			bonded_balance < BalanceOf::<T>::max_value().div(10u32.into()),
			Error::<T>::OverflowRisk
		);
		// then we can be decently confident the bonding pool points will not overflow
		// `BalanceOf<T>`. Note that these are just heuristics.

		Ok(())
	}

	/// Check that the pool can accept a member with `new_funds`.
	fn ok_to_join(&self) -> Result<(), DispatchError> {
		ensure!(self.state == PoolState::Open, Error::<T>::NotOpen);
		self.ok_to_be_open()?;
		Ok(())
	}

	fn ok_to_unbond_other_with(
		&self,
		caller: &T::AccountId,
		target_account: &T::AccountId,
		target_delegator: &Delegator<T>,
	) -> Result<(), DispatchError> {
		let is_permissioned = caller == target_account;
		let is_depositor = *target_account == self.roles.depositor;
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
		};
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
		if *target_account == self.roles.depositor {
			// This is a depositor
			if !sub_pools.no_era.points.is_zero() {
				// Unbonded pool has some points, so if they are the last delegator they must be
				// here. Since the depositor is the last to unbond, this should never be possible.
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

	/// Bond exactly `amount` from `who`'s funds into this pool.
	///
	/// If the bond type is `Create`, `StakingInterface::bond` is called, and `who`
	/// is allowed to be killed. Otherwise, `StakingInterface::bond_extra` is called and `who`
	/// cannot be killed.
	///
	/// Returns `Ok(points_issues)`, `Err` otherwise.
	fn try_bond_funds(
		&mut self,
		who: &T::AccountId,
		amount: BalanceOf<T>,
		ty: BondType,
	) -> Result<BalanceOf<T>, DispatchError> {
		T::Currency::transfer(
			&who,
			&self.bonded_account(),
			amount,
			match ty {
				BondType::Create => ExistenceRequirement::AllowDeath,
				BondType::Later => ExistenceRequirement::KeepAlive,
			},
		)?;
		// We must calculate the points issued *before* we bond who's funds, else points:balance
		// ratio will be wrong.
		let points_issued = self.issue(amount);

		match ty {
			BondType::Create => T::StakingInterface::bond(
				self.bonded_account(),
				self.bonded_account(),
				amount,
				self.reward_account(),
			)?,
			// The pool should always be created in such a way its in a state to bond extra, but if
			// the active balance is slashed below the minimum bonded or the account cannot be
			// found, we exit early.
			BondType::Later => T::StakingInterface::bond_extra(self.bonded_account(), amount)?,
		}

		Ok(points_issued)
	}

	/// If `n` saturates at it's upper bound, mark the pool as destroying. This is useful when a
	/// number saturating indicates the pool can no longer correctly keep track of state.
	fn bound_check(&mut self, n: U256) -> U256 {
		if n == U256::max_value() {
			self.set_state(PoolState::Destroying)
		}

		n
	}

	// Set the state of `self`, and deposit an event if the state changed. State should never be set
	// directly in in order to ensure a state change event is always correctly deposited.
	fn set_state(&mut self, state: PoolState) {
		if self.state != state {
			self.state = state;
			Pallet::<T>::deposit_event(Event::<T>::StateChanged {
				pool_id: self.id,
				new_state: state,
			});
		};
	}
}

/// A reward pool.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
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
	fn update_total_earnings_and_balance(&mut self, id: PoolId) {
		let current_balance = Self::current_balance(id);
		// The earnings since the last time it was updated
		let new_earnings = current_balance.saturating_sub(self.balance);
		// The lifetime earnings of the of the reward pool
		self.total_earnings = new_earnings.saturating_add(self.total_earnings);
		self.balance = current_balance;
	}

	/// Get a reward pool and update its total earnings and balance
	fn get_and_update(id: PoolId) -> Option<Self> {
		RewardPools::<T>::get(id).map(|mut r| {
			r.update_total_earnings_and_balance(id);
			r
		})
	}

	/// The current balance of the reward pool. Never access the reward pools free balance directly.
	/// The existential deposit was not received as a reward, so the reward pool can not use it.
	fn current_balance(id: PoolId) -> BalanceOf<T> {
		T::Currency::free_balance(&Pallet::<T>::create_reward_account(id))
			.saturating_sub(T::Currency::minimum_balance())
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
		Pallet::<T>::points_to_issue(self.balance, self.points, new_funds)
	}

	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		Pallet::<T>::balance_to_unbond(self.balance, self.points, delegator_points)
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
	/// Map of era in which a pool becomes unbonded in => unbond pools.
	with_era: SubPoolsWithEra<T>,
}

impl<T: Config> SubPools<T> {
	/// Merge the oldest `with_era` unbond pools into the `no_era` unbond pool.
	///
	/// This is often used whilst getting the sub-pool from storage, thus it consumes and returns
	/// `Self` for ergonomic purposes.
	fn maybe_merge_pools(mut self, unbond_era: EraIndex) -> Self {
		// Ex: if `TotalUnbondingPools` is 5 and current era is 10, we only want to retain pools
		// 6..=10. Note that in the first few eras where `checked_sub` is `None`, we don't remove
		// anything.
		if let Some(newest_era_to_remove) = unbond_era.checked_sub(TotalUnbondingPools::<T>::get())
		{
			self.with_era.retain(|k, v| {
				if *k > newest_era_to_remove {
					// keep
					true
				} else {
					// merge into the no-era pool
					self.no_era.points = self.no_era.points.saturating_add(v.points);
					self.no_era.balance = self.no_era.balance.saturating_add(v.balance);
					false
				}
			});
		}

		self
	}
}

/// The maximum amount of eras an unbonding pool can exist prior to being merged with the
/// `no_era` pool. This is guaranteed to at least be equal to the staking `UnbondingDuration`. For
/// improved UX [`Config::PostUnbondingPoolsWindow`] should be configured to a non-zero value.
pub struct TotalUnbondingPools<T: Config>(PhantomData<T>);
impl<T: Config> Get<u32> for TotalUnbondingPools<T> {
	fn get() -> u32 {
		// NOTE: this may be dangerous in the scenario bonding_duration gets decreased because
		// we would no longer be able to decode `SubPoolsWithEra`, which uses `TotalUnbondingPools`
		// as the bound
		T::StakingInterface::bonding_duration() + T::PostUnbondingPoolsWindow::get()
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::transactional;
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

		/// The nominating balance.
		type Currency: Currency<Self::AccountId>;

		/// The nomination pool's pallet id.
		#[pallet::constant]
		type PalletId: Get<frame_support::PalletId>;

		/// Infallible method for converting `Currency::Balance` to `U256`.
		type BalanceToU256: Convert<BalanceOf<Self>, U256>;

		/// Infallible method for converting `U256` to `Currency::Balance`.
		type U256ToBalance: Convert<U256, BalanceOf<Self>>;

		/// The interface for nominating.
		type StakingInterface: StakingInterface<
			Balance = BalanceOf<Self>,
			AccountId = Self::AccountId,
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
		CountedStorageMap<_, Twox64Concat, PoolId, BondedPoolInner<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool. Keyed by the bonded pools account.
	#[pallet::storage]
	pub type RewardPools<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a bonded pool,
	/// hence the name sub-pools. Keyed by the bonded pools account.
	#[pallet::storage]
	pub type SubPoolsStorage<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, SubPools<T>>;

	/// Metadata for the pool.
	#[pallet::storage]
	pub type Metadata<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, BoundedVec<u8, T::MaxMetadataLen>, ValueQuery>;

	#[pallet::storage]
	pub type LastPoolId<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type ReversePoolIdLookup<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, PoolId, OptionQuery>;

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

	/// Events of this pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A pool has been created.
		Created { depositor: T::AccountId, pool_id: PoolId },
		/// A delegator has became bonded in a pool.
		Bonded { delegator: T::AccountId, pool_id: PoolId, bonded: BalanceOf<T>, joined: bool },
		/// A payout has been made to a delegator.
		PaidOut { delegator: T::AccountId, pool_id: PoolId, payout: BalanceOf<T> },
		/// A delegator has unbonded from their pool.
		Unbonded { delegator: T::AccountId, pool_id: PoolId, amount: BalanceOf<T> },
		/// A delegator has withdrawn from their pool.
		Withdrawn { delegator: T::AccountId, pool_id: PoolId, amount: BalanceOf<T> },
		/// A pool has been destroyed.
		Destroyed { pool_id: PoolId },
		/// The state of a pool has changed
		StateChanged { pool_id: PoolId, new_state: PoolState },
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
		/// Some error occurred that should never happen. This should be reported to the
		/// maintainers.
		DefensiveError,
		/// The caller has insufficient balance to create the pool.
		InsufficientBalanceToCreate,
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
		pub fn join(origin: OriginFor<T>, amount: BalanceOf<T>, pool_id: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(amount >= MinJoinBond::<T>::get(), Error::<T>::MinimumBondNotMet);
			// If a delegator already exists that means they already belong to a pool
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_join()?;

			// don't actually care about writing the reward pool, we just need its total earnings at
			// this point in time.
			let reward_pool = RewardPool::<T>::get_and_update(pool_id)
				.defensive_ok_or_else(|| Error::<T>::RewardPoolNotFound)?;

			bonded_pool.try_inc_delegators()?;
			let points_issued = bonded_pool.try_bond_funds(&who, amount, BondType::Later)?;

			Delegators::insert(
				who.clone(),
				Delegator::<T> {
					pool_id,
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
			Self::deposit_event(Event::<T>::Bonded {
				delegator: who,
				pool_id,
				bonded: amount,
				joined: true,
			});

			Ok(())
		}

		/// Bond `extra` more funds from `origin` into the pool to which they already belong.
		///
		/// Additional funds can come from either the free balance of the account, of from the
		/// accumulated rewards, see [`BondExtra`].
		// NOTE: this transaction is implemented with the sole purpose of readability and
		// correctness, not optimization. We read/write several storage items multiple times instead
		// of just once, in the spirit reusing code.
		#[pallet::weight(0)]
		#[transactional]
		pub fn bond_extra(origin: OriginFor<T>, extra: BondExtra<BalanceOf<T>>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let (mut delegator, mut bonded_pool, mut reward_pool) =
				Self::get_delegator_with_pools(&who)?;

			let (points_issued, bonded) = match extra {
				BondExtra::FreeBalance(amount) =>
					(bonded_pool.try_bond_funds(&who, amount, BondType::Later)?, amount),
				BondExtra::Rewards => {
					let claimed = Self::do_reward_payout(
						&who,
						&mut delegator,
						&mut bonded_pool,
						&mut reward_pool,
					)?;
					(bonded_pool.try_bond_funds(&who, claimed, BondType::Later)?, claimed)
				},
			};
			delegator.points = delegator.points.saturating_add(points_issued);

			Self::deposit_event(Event::<T>::Bonded {
				delegator: who.clone(),
				pool_id: delegator.pool_id,
				bonded,
				joined: false,
			});
			Self::put_delegator_with_pools(&who, delegator, bonded_pool, reward_pool);

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
			let (mut delegator, mut bonded_pool, mut reward_pool) =
				Self::get_delegator_with_pools(&who)?;

			let _ =
				Self::do_reward_payout(&who, &mut delegator, &mut bonded_pool, &mut reward_pool)?;

			Self::put_delegator_with_pools(&who, delegator, bonded_pool, reward_pool);
			Ok(())
		}

		/// Unbond _all_ of the `delegator_account`'s funds from the pool.
		///
		/// Under certain conditions, this call can be dispatched permissionlessly (i.e. by any
		/// account).
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
		/// Note: If there are too many unlocking chunks to unbond with the pool account,
		/// [`Self::withdraw_unbonded_pool`] can be called to try and minimize unlocking chunks.
		#[pallet::weight(T::WeightInfo::unbond_other())]
		#[frame_support::transactional]
		pub fn unbond_other(
			origin: OriginFor<T>,
			delegator_account: T::AccountId,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;
			let (mut delegator, mut bonded_pool, mut reward_pool) =
				Self::get_delegator_with_pools(&delegator_account)?;

			bonded_pool.ok_to_unbond_other_with(&caller, &delegator_account, &delegator)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points
			// no longer exist in the bonded pool and thus they can no longer claim their payouts.
			// It is not strictly necessary to claim the rewards, but we do it here for UX.
			Self::do_reward_payout(
				&delegator_account,
				&mut delegator,
				&mut bonded_pool,
				&mut reward_pool,
			)?;

			let balance_to_unbond = bonded_pool.balance_to_unbond(delegator.points);

			// Update the bonded pool. Note that we must do this *after* calculating the balance
			// to unbond so we have the correct points for the balance:share ratio.
			bonded_pool.points = bonded_pool.points.saturating_sub(delegator.points);

			// Unbond in the actual underlying pool
			T::StakingInterface::unbond(bonded_pool.bonded_account(), balance_to_unbond)?;

			let current_era = T::StakingInterface::current_era();
			let unbond_era = T::StakingInterface::bonding_duration().saturating_add(current_era);
			// Note that we lazily create the unbonding pools here if they don't already exist
			let mut sub_pools = SubPoolsStorage::<T>::get(delegator.pool_id)
				.unwrap_or_default()
				.maybe_merge_pools(unbond_era);

			// Update the unbond pool associated with the current era with the unbonded funds. Note
			// that we lazily create the unbond pool if it does not yet exist.
			if !sub_pools.with_era.contains_key(&unbond_era) {
				sub_pools
					.with_era
					.try_insert(unbond_era, UnbondPool::default())
					// The above call to `maybe_merge_pools` should ensure there is
					// always enough space to insert.
					.defensive_map_err(|_| Error::<T>::DefensiveError)?;
			}
			sub_pools
				.with_era
				.get_mut(&unbond_era)
				// The above check ensures the pool exists.
				.defensive_ok_or_else(|| Error::<T>::DefensiveError)?
				.issue(balance_to_unbond);

			delegator.unbonding_era = Some(unbond_era);

			Self::deposit_event(Event::<T>::Unbonded {
				delegator: delegator_account.clone(),
				pool_id: delegator.pool_id,
				amount: balance_to_unbond,
			});

			// Now that we know everything has worked write the items to storage.
			SubPoolsStorage::insert(&delegator.pool_id, sub_pools);
			Self::put_delegator_with_pools(&delegator_account, delegator, bonded_pool, reward_pool);

			Ok(())
		}

		/// Call `withdraw_unbonded` for the pools account. This call can be made by any account.
		///
		/// This is useful if their are too many unlocking chunks to call `unbond_other`, and some
		/// can be cleared by withdrawing.
		#[pallet::weight(T::WeightInfo::pool_withdraw_unbonded(*num_slashing_spans))]
		pub fn pool_withdraw_unbonded(
			origin: OriginFor<T>,
			pool_id: PoolId,
			num_slashing_spans: u32,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			let pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			// For now we only allow a pool to withdraw unbonded if its not destroying. If the pool
			// is destroying then `withdraw_unbonded_other` can be used.
			ensure!(pool.state != PoolState::Destroying, Error::<T>::NotDestroying);
			T::StakingInterface::withdraw_unbonded(pool.bonded_account(), num_slashing_spans)?;
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
			delegator_account: T::AccountId,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let caller = ensure_signed(origin)?;
			let delegator =
				Delegators::<T>::get(&delegator_account).ok_or(Error::<T>::DelegatorNotFound)?;
			let unbonding_era = delegator.unbonding_era.ok_or(Error::<T>::NotUnbonding)?;
			let current_era = T::StakingInterface::current_era();
			ensure!(current_era >= unbonding_era, Error::<T>::NotUnbondedYet);

			let mut sub_pools = SubPoolsStorage::<T>::get(delegator.pool_id)
				.defensive_ok_or_else(|| Error::<T>::SubPoolsNotFound)?;
			let bonded_pool = BondedPool::<T>::get(delegator.pool_id)
				.defensive_ok_or_else(|| Error::<T>::PoolNotFound)?;
			let should_remove_pool = bonded_pool.ok_to_withdraw_unbonded_other_with(
				&caller,
				&delegator_account,
				&delegator,
				&sub_pools,
			)?;

			// Before calculate the `balance_to_unbond`, with call withdraw unbonded to ensure the
			// `non_locked_balance` is correct.
			T::StakingInterface::withdraw_unbonded(
				bonded_pool.bonded_account(),
				num_slashing_spans,
			)?;

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
				.min(bonded_pool.transferrable_balance());

			T::Currency::transfer(
				&bonded_pool.bonded_account(),
				&delegator_account,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)
			.defensive_map_err(|e| e)?;
			Self::deposit_event(Event::<T>::Withdrawn {
				delegator: delegator_account.clone(),
				pool_id: delegator.pool_id,
				amount: balance_to_unbond,
			});

			let post_info_weight = if should_remove_pool {
				ReversePoolIdLookup::<T>::remove(bonded_pool.bonded_account());
				RewardPools::<T>::remove(delegator.pool_id);
				Self::deposit_event(Event::<T>::Destroyed { pool_id: delegator.pool_id });
				SubPoolsStorage::<T>::remove(delegator.pool_id);
				// Kill accounts from storage by making their balance go below ED. We assume that
				// the accounts have no references that would prevent destruction once we get to
				// this point.
				debug_assert_eq!(
					T::Currency::free_balance(&bonded_pool.bonded_account()),
					Zero::zero()
				);
				debug_assert_eq!(
					T::StakingInterface::total_stake(&bonded_pool.bonded_account())
						.unwrap_or_default(),
					Zero::zero()
				);
				T::Currency::make_free_balance_be(&bonded_pool.reward_account(), Zero::zero());
				T::Currency::make_free_balance_be(&bonded_pool.bonded_account(), Zero::zero());
				bonded_pool.remove();
				None
			} else {
				bonded_pool.dec_delegators().put();
				SubPoolsStorage::<T>::insert(&delegator.pool_id, sub_pools);
				Some(T::WeightInfo::withdraw_unbonded_other_update(num_slashing_spans))
			};
			Delegators::<T>::remove(&delegator_account);

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
		/// * `root` - The account to set as [`PoolRoles::root`].
		/// * `nominator` - The account to set as the [`PoolRoles::nominator`].
		/// * `state_toggler` - The account to set as the [`PoolRoles::state_toggler`].
		///
		/// # Note
		///
		/// In addition to `amount`, the caller will transfer the existential deposit; so the caller
		/// needs at have at least `amount + existential_deposit` transferrable.
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
				amount >=
					T::StakingInterface::minimum_bond()
						.max(MinCreateBond::<T>::get())
						.max(MinJoinBond::<T>::get()),
				Error::<T>::MinimumBondNotMet
			);
			ensure!(
				MaxPools::<T>::get()
					.map_or(true, |max_pools| BondedPools::<T>::count() < max_pools),
				Error::<T>::MaxPools
			);
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);
			ensure!(
				T::Currency::free_balance(&who) >=
					amount.saturating_add(T::Currency::minimum_balance()),
				Error::<T>::InsufficientBalanceToCreate
			);

			let pool_id = LastPoolId::<T>::mutate(|id| {
				*id += 1;
				*id
			});
			let mut bonded_pool = BondedPool::<T>::new(
				pool_id,
				PoolRoles { root, nominator, state_toggler, depositor: who.clone() },
			);

			bonded_pool.try_inc_delegators()?;
			let points = bonded_pool.try_bond_funds(&who, amount, BondType::Create)?;

			T::Currency::transfer(
				&who,
				&bonded_pool.reward_account(),
				T::Currency::minimum_balance(),
				ExistenceRequirement::AllowDeath,
			)
			.defensive()?;

			Delegators::<T>::insert(
				who.clone(),
				Delegator::<T> {
					pool_id,
					points,
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None,
				},
			);
			RewardPools::<T>::insert(
				pool_id,
				RewardPool::<T> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
				},
			);
			ReversePoolIdLookup::<T>::insert(bonded_pool.bonded_account(), pool_id);
			Self::deposit_event(Event::<T>::Created { depositor: who, pool_id });
			bonded_pool.put();

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::nominate())]
		pub fn nominate(
			origin: OriginFor<T>,
			pool_id: PoolId,
			validators: Vec<T::AccountId>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_nominate(&who), Error::<T>::NotNominator);
			T::StakingInterface::nominate(bonded_pool.bonded_account(), validators)?;
			Ok(())
		}

		#[pallet::weight(T::WeightInfo::set_state_other())]
		pub fn set_state_other(
			origin: OriginFor<T>,
			pool_id: PoolId,
			state: PoolState,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.state != PoolState::Destroying, Error::<T>::CanNotChangeState);

			if bonded_pool.can_toggle_state(&who) {
				bonded_pool.set_state(state);
			} else if bonded_pool.ok_to_be_open().is_err() && state == PoolState::Destroying {
				// If the pool has bad properties, then anyone can set it as destroying
				bonded_pool.set_state(PoolState::Destroying);
			} else {
				Err(Error::<T>::CanNotChangeState)?;
			}

			bonded_pool.put();

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::set_metadata())]
		pub fn set_metadata(
			origin: OriginFor<T>,
			pool_id: PoolId,
			metadata: Vec<u8>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let metadata: BoundedVec<_, _> =
				metadata.try_into().map_err(|_| Error::<T>::MetadataExceedsMaxLen)?;
			ensure!(
				BondedPool::<T>::get(pool_id)
					.ok_or(Error::<T>::PoolNotFound)?
					.can_set_metadata(&who),
				Error::<T>::DoesNotHavePermission
			);

			Metadata::<T>::mutate(pool_id, |pool_meta| *pool_meta = metadata);

			Ok(())
		}

		/// Update configurations for the nomination pools. The origin must for this call must be
		/// Root.
		///
		/// # Arguments
		///
		/// * `min_join_bond` - Set [`Self::MinJoinBond`].
		/// * `min_create_bond` - Set [`Self::MinCreateBond`].
		/// * `max_pools` - Set [`Self::MaxPools`].
		/// * `max_delegators` - Set [`Self::MaxDelegators`].
		/// * `max_delegators_per_pool` - Set [`Self::MaxDelegatorsPerPool`].
		#[pallet::weight(T::WeightInfo::set_configs())]
		pub fn set_configs(
			origin: OriginFor<T>,
			min_join_bond: ConfigOp<BalanceOf<T>>,
			min_create_bond: ConfigOp<BalanceOf<T>>,
			max_pools: ConfigOp<u32>,
			max_delegators: ConfigOp<u32>,
			max_delegators_per_pool: ConfigOp<u32>,
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

			config_op_exp!(MinJoinBond::<T>, min_join_bond);
			config_op_exp!(MinCreateBond::<T>, min_create_bond);
			config_op_exp!(MaxPools::<T>, max_pools);
			config_op_exp!(MaxDelegators::<T>, max_delegators);
			config_op_exp!(MaxDelegatorsPerPool::<T>, max_delegators_per_pool);

			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(
				sp_std::mem::size_of::<RewardPoints>() >=
					2 * sp_std::mem::size_of::<BalanceOf<T>>(),
				"bit-length of the reward points must be at least twice as much as balance"
			);

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
	/// Create the main, bonded account of a pool with the given id.
	pub fn create_bonded_account(id: PoolId) -> T::AccountId {
		T::PalletId::get().into_sub_account((AccountType::Bonded, id))
	}

	/// Create the reward account of a pool with the given id.
	pub fn create_reward_account(id: PoolId) -> T::AccountId {
		// NOTE: in order to have a distinction in the test account id type (u128), we put
		// account_type first so it does not get truncated out.
		T::PalletId::get().into_sub_account((AccountType::Reward, id))
	}

	/// Get the delegator with their associated bonded and reward pool.
	fn get_delegator_with_pools(
		who: &T::AccountId,
	) -> Result<(Delegator<T>, BondedPool<T>, RewardPool<T>), Error<T>> {
		let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
		let bonded_pool =
			BondedPool::<T>::get(delegator.pool_id).defensive_ok_or(Error::<T>::PoolNotFound)?;
		let reward_pool =
			RewardPools::<T>::get(delegator.pool_id).defensive_ok_or(Error::<T>::PoolNotFound)?;
		Ok((delegator, bonded_pool, reward_pool))
	}

	/// Persist the delegator with their associated bonded and reward pool into storage, consuming
	/// all of them.
	fn put_delegator_with_pools(
		delegator_account: &T::AccountId,
		delegator: Delegator<T>,
		bonded_pool: BondedPool<T>,
		reward_pool: RewardPool<T>,
	) {
		bonded_pool.put();
		RewardPools::insert(delegator.pool_id, reward_pool);
		Delegators::<T>::insert(delegator_account, delegator);
	}

	/// Calculate the number of points to issue from a pool as `(current_points / current_balance) *
	/// new_funds` except for some zero edge cases; see logic and tests for details.
	fn points_to_issue(
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
	fn balance_to_unbond(
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

	/// Calculate the rewards for `delegator`.
	///
	/// Returns the payout amount, and whether the pool state has been switched to destroying during
	/// this call.
	fn calculate_delegator_payout(
		bonded_pool: &mut BondedPool<T>,
		reward_pool: &mut RewardPool<T>,
		delegator: &mut Delegator<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		// Presentation Notes:
		// Reward pool points
		// Essentially we make it so each plank is inflated by the number of points in bonded pool.
		// So if we have earned 10 plank and 100 bonded pool points, we get 1,000 reward pool
		// points. The delegator scales up their points as well (say 10 for this example) and we get
		// the delegator has virtual points of 10points * 10rewards (100reward-points).
		// So the payout calc is 100 / 1,000 * 100 = 10
		//
		// Keep in mind we subtract the delegators virtual points from the pool points to account
		// for the fact that we transferred their portion of rewards out of the pool account.

		let u256 = |x| T::BalanceToU256::convert(x);
		let balance = |x| T::U256ToBalance::convert(x);
		// If the delegator is unbonding they cannot claim rewards. Note that when the delegator
		// goes to unbond, the unbond function should claim rewards for the final time.
		ensure!(delegator.unbonding_era.is_none(), Error::<T>::AlreadyUnbonding);

		let last_total_earnings = reward_pool.total_earnings;
		reward_pool.update_total_earnings_and_balance(bonded_pool.id);

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
		let current_points = bonded_pool.bound_check(reward_pool.points.saturating_add(new_points));

		// The rewards pool's earnings since the last time this delegator claimed a payout.
		let new_earnings_since_last_claim =
			reward_pool.total_earnings.saturating_sub(delegator.reward_pool_total_earnings);

		// The points of the reward pool that belong to the delegator.
		let delegator_virtual_points =
			// The delegators portion of the reward pool
			u256(delegator.points)
			// times the amount the pool has earned since the delegator last claimed.
			.saturating_mul(u256(new_earnings_since_last_claim));

		let delegator_payout = if delegator_virtual_points.is_zero() ||
			current_points.is_zero() ||
			reward_pool.balance.is_zero()
		{
			Zero::zero()
		} else {
			// Equivalent to `(delegator_virtual_points / current_points) * reward_pool.balance`
			let numerator = {
				let numerator = delegator_virtual_points.saturating_mul(u256(reward_pool.balance));
				bonded_pool.bound_check(numerator)
			};
			balance(
				numerator
					// We check for zero above
					.div(current_points),
			)
		};

		// Record updates
		if reward_pool.total_earnings == BalanceOf::<T>::max_value() {
			bonded_pool.set_state(PoolState::Destroying);
		};
		delegator.reward_pool_total_earnings = reward_pool.total_earnings;
		reward_pool.points = current_points.saturating_sub(delegator_virtual_points);
		reward_pool.balance = reward_pool.balance.saturating_sub(delegator_payout);

		Ok(delegator_payout)
	}

	/// If the delegator has some rewards, transfer a payout from the reward pool to the delegator.
	// Emits events and potentially modifies pool state if any arithmetic saturates, but does
	// not persist any of the mutable inputs to storage.
	fn do_reward_payout(
		delegator_account: &T::AccountId,
		delegator: &mut Delegator<T>,
		bonded_pool: &mut BondedPool<T>,
		reward_pool: &mut RewardPool<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		debug_assert_eq!(delegator.pool_id, bonded_pool.id);
		let was_destroying = bonded_pool.is_destroying();

		let delegator_payout =
			Self::calculate_delegator_payout(bonded_pool, reward_pool, delegator)?;

		// Transfer payout to the delegator.
		T::Currency::transfer(
			&bonded_pool.reward_account(),
			&delegator_account,
			delegator_payout,
			ExistenceRequirement::AllowDeath,
		)?;

		Self::deposit_event(Event::<T>::PaidOut {
			delegator: delegator_account.clone(),
			pool_id: delegator.pool_id,
			payout: delegator_payout,
		});

		if bonded_pool.is_destroying() && !was_destroying {
			Self::deposit_event(Event::<T>::StateChanged {
				pool_id: delegator.pool_id,
				new_state: PoolState::Destroying,
			});
		}

		Ok(delegator_payout)
	}

	/// Ensure the correctness of the state of this pallet.
	///
	/// This should be valid before or after each state transition of this pallet.
	///
	/// ## Invariants:
	///
	/// First, let's consider pools:
	///
	/// * `BondedPools` and `RewardPools` must all have the EXACT SAME key-set.
	/// * `SubPoolsStorage` must be a subset of the above superset.
	/// * `Metadata` keys must be a subset of the above superset.
	/// * the count of the above set must be less than `MaxPools`.
	///
	/// Then, considering delegators as well:
	///
	/// * each `BondedPool.delegator_counter` must be:
	///   - correct (compared to actual count of delegator who have `.pool_id` this pool)
	///   - less than `MaxDelegatorsPerPool`.
	/// * each `delegator.pool_id` must correspond to an existing `BondedPool.id` (which implies the
	///   existence of the reward pool as well).
	/// * count of all delegators must be less than `MaxDelegators`.
	///
	/// Then, considering unbonding delegators:
	///
	/// for each pool:
	///   * sum of the balance that's tracked in all unbonding pools must be the same as the
	///     unbonded balance of the main account, as reported by the staking interface.
	///   * sum of the balance that's tracked in all unbonding pools, plus the bonded balance of the
	///     main account should be less than or qual to the total balance of the main account.
	///
	/// ## Sanity check level
	///
	/// To cater for tests that want to escape parts of these checks, this function is split into
	/// multiple `level`s, where the higher the level, the more checks we performs. So,
	/// `sanity_check(255)` is the strongest sanity check, and `0` performs no checks.
	#[cfg(any(test, debug_assertions))]
	pub fn sanity_checks(level: u8) -> Result<(), &'static str> {
		if level.is_zero() {
			return Ok(())
		}
		// note: while a bit wacky, since they have the same key, even collecting to vec should
		// result in the same set of keys, in the same order.
		let bonded_pools = BondedPools::<T>::iter_keys().collect::<Vec<_>>();
		let reward_pools = RewardPools::<T>::iter_keys().collect::<Vec<_>>();
		assert_eq!(bonded_pools, reward_pools);

		assert!(Metadata::<T>::iter_keys().all(|k| bonded_pools.contains(&k)));
		assert!(SubPoolsStorage::<T>::iter_keys().all(|k| bonded_pools.contains(&k)));

		assert!(MaxPools::<T>::get().map_or(true, |max| bonded_pools.len() <= (max as usize)));

		for id in reward_pools {
			let account = Self::create_reward_account(id);
			assert!(T::Currency::free_balance(&account) >= T::Currency::minimum_balance());
		}

		let mut pools_delegators = BTreeMap::<PoolId, u32>::new();
		let mut all_delegators = 0u32;
		Delegators::<T>::iter().for_each(|(_, d)| {
			assert!(BondedPools::<T>::contains_key(d.pool_id));
			*pools_delegators.entry(d.pool_id).or_default() += 1;
			all_delegators += 1;
		});

		BondedPools::<T>::iter().for_each(|(id, bonded_pool)| {
			assert_eq!(
				pools_delegators.get(&id).map(|x| *x).unwrap_or_default(),
				bonded_pool.delegator_counter
			);
			assert!(MaxDelegatorsPerPool::<T>::get()
				.map_or(true, |max| bonded_pool.delegator_counter <= max));
		});
		assert!(MaxDelegators::<T>::get().map_or(true, |max| all_delegators <= max));

		if level <= 1 {
			return Ok(())
		}

		for (pool_id, _) in BondedPools::<T>::iter() {
			let pool_account = Pallet::<T>::create_bonded_account(pool_id);
			let subs = SubPoolsStorage::<T>::get(pool_id).unwrap_or_default();
			let sum_unbonding_balance = subs
				.with_era
				.into_iter()
				.map(|(_, v)| v)
				.chain(sp_std::iter::once(subs.no_era))
				.map(|unbond_pool| unbond_pool.balance)
				.fold(Zero::zero(), |a, b| a + b);

			let bonded_balance =
				T::StakingInterface::active_stake(&pool_account).unwrap_or_default();
			let total_balance = T::Currency::total_balance(&pool_account);

			assert!(
				total_balance >= bonded_balance + sum_unbonding_balance,
				"total_balance {:?} >= bonded_balance {:?} + sum_unbonding_balance {:?}",
				total_balance,
				bonded_balance,
				sum_unbonding_balance
			);
		}

		Ok(())
	}
}

impl<T: Config> OnStakerSlash<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_slash(
		pool_account: &T::AccountId,
		// Bonded balance is always read directly from staking, therefore we need not update
		// anything here.
		_slashed_bonded: BalanceOf<T>,
		slashed_unlocking: &BTreeMap<EraIndex, BalanceOf<T>>,
	) {
		if let Some(pool_id) = ReversePoolIdLookup::<T>::get(pool_account) {
			let mut sub_pools = match SubPoolsStorage::<T>::get(pool_id).defensive() {
				Some(sub_pools) => sub_pools,
				None => return,
			};
			for (era, slashed_balance) in slashed_unlocking.iter() {
				if let Some(pool) = sub_pools.with_era.get_mut(era) {
					pool.balance = *slashed_balance
				}
			}
			SubPoolsStorage::<T>::insert(pool_id, sub_pools);
		}
	}
}
