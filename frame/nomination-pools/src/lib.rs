// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Nomination Pools for Staking Delegation
//!
//! A pallet that allows members to delegate their stake to nominating pools. A nomination pool acts
//! as nominator and nominates validators on the members behalf.
//!
//! # Index
//!
//! * [Key terms](#key-terms)
//! * [Usage](#usage)
//! * [Implementor's Guide](#implementors-guide)
//! * [Design](#design)
//!
//! ## Key Terms
//!
//!  * pool id: A unique identifier of each pool. Set to u32.
//!  * bonded pool: Tracks the distribution of actively staked funds. See [`BondedPool`] and
//! [`BondedPoolInner`].
//! * reward pool: Tracks rewards earned by actively staked funds. See [`RewardPool`] and
//!   [`RewardPools`].
//! * unbonding sub pools: Collection of pools at different phases of the unbonding lifecycle. See
//!   [`SubPools`] and [`SubPoolsStorage`].
//! * members: Accounts that are members of pools. See [`PoolMember`] and [`PoolMembers`].
//! * roles: Administrative roles of each pool, capable of controlling nomination, and the state of
//!   the pool.
//! * point: A unit of measure for a members portion of a pool's funds. Points initially have a
//!   ratio of 1 (as set by `POINTS_TO_BALANCE_INIT_RATIO`) to balance, but as slashing happens,
//!   this can change.
//! * kick: The act of a pool administrator forcibly ejecting a member.
//! * bonded account: A key-less account id derived from the pool id that acts as the bonded
//!   account. This account registers itself as a nominator in the staking system, and follows
//!   exactly the same rules and conditions as a normal staker. Its bond increases or decreases as
//!   members join, it can `nominate` or `chill`, and might not even earn staking rewards if it is
//!   not nominating proper validators.
//! * reward account: A similar key-less account, that is set as the `Payee` account for the bonded
//!   account for all staking rewards.
//! * change rate: The rate at which pool commission can be changed. A change rate consists of a
//!   `max_increase` and `min_delay`, dictating the maximum percentage increase that can be applied
//!   to the commission per number of blocks.
//! * throttle: An attempted commission increase is throttled if the attempted change falls outside
//!   the change rate bounds.
//!
//! ## Usage
//!
//! ### Join
//!
//! An account can stake funds with a nomination pool by calling [`Call::join`].
//!
//! ### Claim rewards
//!
//! After joining a pool, a member can claim rewards by calling [`Call::claim_payout`].
//!
//! A pool member can also set a `ClaimPermission` with [`Call::set_claim_permission`], to allow
//! other members to permissionlessly bond or withdraw their rewards by calling
//! [`Call::bond_extra_other`] or [`Call::claim_payout_other`] respectively.
//!
//! For design docs see the [reward pool](#reward-pool) section.
//!
//! ### Leave
//!
//! In order to leave, a member must take two steps.
//!
//! First, they must call [`Call::unbond`]. The unbond extrinsic will start the unbonding process by
//! unbonding all or a portion of the members funds.
//!
//! > A member can have up to [`Config::MaxUnbonding`] distinct active unbonding requests.
//!
//! Second, once [`sp_staking::StakingInterface::bonding_duration`] eras have passed, the member can
//! call [`Call::withdraw_unbonded`] to withdraw any funds that are free.
//!
//! For design docs see the [bonded pool](#bonded-pool) and [unbonding sub
//! pools](#unbonding-sub-pools) sections.
//!
//! ### Slashes
//!
//! Slashes are distributed evenly across the bonded pool and the unbonding pools from slash era+1
//! through the slash apply era. Thus, any member who either
//!
//! 1. unbonded, or
//! 2. was actively bonded
//
//! in the aforementioned range of eras will be affected by the slash. A member is slashed pro-rata
//! based on its stake relative to the total slash amount.
//!
//! Slashing does not change any single member's balance. Instead, the slash will only reduce the
//! balance associated with a particular pool. But, we never change the total *points* of a pool
//! because of slashing. Therefore, when a slash happens, the ratio of points to balance changes in
//! a pool. In other words, the value of one point, which is initially 1-to-1 against a unit of
//! balance, is now less than one balance because of the slash.
//!
//! ### Administration
//!
//! A pool can be created with the [`Call::create`] call. Once created, the pools nominator or root
//! user must call [`Call::nominate`] to start nominating. [`Call::nominate`] can be called at
//! anytime to update validator selection.
//!
//! Similar to [`Call::nominate`], [`Call::chill`] will chill to pool in the staking system, and
//! [`Call::pool_withdraw_unbonded`] will withdraw any unbonding chunks of the pool bonded account.
//! The latter call is permissionless and can be called by anyone at any time.
//!
//! To help facilitate pool administration the pool has one of three states (see [`PoolState`]):
//!
//! * Open: Anyone can join the pool and no members can be permissionlessly removed.
//! * Blocked: No members can join and some admin roles can kick members. Kicking is not instant,
//!   and follows the same process of `unbond` and then `withdraw_unbonded`. In other words,
//!   administrators can permissionlessly unbond other members.
//! * Destroying: No members can join and all members can be permissionlessly removed with
//!   [`Call::unbond`] and [`Call::withdraw_unbonded`]. Once a pool is in destroying state, it
//!   cannot be reverted to another state.
//!
//! A pool has 4 administrative roles (see [`PoolRoles`]):
//!
//! * Depositor: creates the pool and is the initial member. They can only leave the pool once all
//!   other members have left. Once they fully withdraw their funds, the pool is destroyed.
//! * Nominator: can select which validators the pool nominates.
//! * Bouncer: can change the pools state and kick members if the pool is blocked.
//! * Root: can change the nominator, bouncer, or itself, manage and claim commission, and can
//!   perform any of the actions the nominator or bouncer can.
//!
//! ### Commission
//!
//! A pool can optionally have a commission configuration, via the `root` role, set with
//! [`Call::set_commission`] and claimed with [`Call::claim_commission`]. A payee account must be
//! supplied with the desired commission percentage. Beyond the commission itself, a pool can have a
//! maximum commission and a change rate.
//!
//! Importantly, both max commission  [`Call::set_commission_max`] and change rate
//! [`Call::set_commission_change_rate`] can not be removed once set, and can only be set to more
//! restrictive values (i.e. a lower max commission or a slower change rate) in subsequent updates.
//!
//! If set, a pool's commission is bound to [`GlobalMaxCommission`] at the time it is applied to
//! pending rewards. [`GlobalMaxCommission`] is intended to be updated only via governance.
//!
//! When a pool is dissolved, any outstanding pending commission that has not been claimed will be
//! transferred to the depositor.
//!
//! Implementation note: Commission is analogous to a separate member account of the pool, with its
//! own reward counter in the form of `current_pending_commission`.
//!
//! Crucially, commission is applied to rewards based on the current commission in effect at the
//! time rewards are transferred into the reward pool. This is to prevent the malicious behaviour of
//! changing the commission rate to a very high value after rewards are accumulated, and thus claim
//! an unexpectedly high chunk of the reward.
//!
//! ### Dismantling
//!
//! As noted, a pool is destroyed once
//!
//! 1. First, all members need to fully unbond and withdraw. If the pool state is set to
//!    `Destroying`, this can happen permissionlessly.
//! 2. The depositor itself fully unbonds and withdraws.
//!
//! > Note that at this point, based on the requirements of the staking system, the pool's bonded
//! > account's stake might not be able to ge below a certain threshold as a nominator. At this
//! > point, the pool should `chill` itself to allow the depositor to leave. See [`Call::chill`].
//!
//! ## Implementor's Guide
//!
//! Some notes and common mistakes that wallets/apps wishing to implement this pallet should be
//! aware of:
//!
//!
//! ### Pool Members
//!
//! * In general, whenever a pool member changes their total point, the chain will automatically
//!   claim all their pending rewards for them. This is not optional, and MUST happen for the reward
//!   calculation to remain correct (see the documentation of `bond` as an example). So, make sure
//!   you are warning your users about it. They might be surprised if they see that they bonded an
//!   extra 100 DOTs, and now suddenly their 5.23 DOTs in pending reward is gone. It is not gone, it
//!   has been paid out to you!
//! * Joining a pool implies transferring funds to the pool account. So it might be (based on which
//!   wallet that you are using) that you no longer see the funds that are moved to the pool in your
//!   “free balance” section. Make sure the user is aware of this, and not surprised by seeing this.
//!   Also, the transfer that happens here is configured to to never accidentally destroy the sender
//!   account. So to join a Pool, your sender account must remain alive with 1 DOT left in it. This
//!   means, with 1 DOT as existential deposit, and 1 DOT as minimum to join a pool, you need at
//!   least 2 DOT to join a pool. Consequently, if you are suggesting members to join a pool with
//!   “Maximum possible value”, you must subtract 1 DOT to remain in the sender account to not
//!   accidentally kill it.
//! * Points and balance are not the same! Any pool member, at any point in time, can have points in
//!   either the bonded pool or any of the unbonding pools. The crucial fact is that in any of these
//!   pools, the ratio of point to balance is different and might not be 1. Each pool starts with a
//!   ratio of 1, but as time goes on, for reasons such as slashing, the ratio gets broken. Over
//!   time, 100 points in a bonded pool can be worth 90 DOTs. Make sure you are either representing
//!   points as points (not as DOTs), or even better, always display both: “You have x points in
//!   pool y which is worth z DOTs”. See here and here for examples of how to calculate point to
//!   balance ratio of each pool (it is almost trivial ;))
//!
//! ### Pool Management
//!
//! * The pool will be seen from the perspective of the rest of the system as a single nominator.
//!   Ergo, This nominator must always respect the `staking.minNominatorBond` limit. Similar to a
//!   normal nominator, who has to first `chill` before fully unbonding, the pool must also do the
//!   same. The pool’s bonded account will be fully unbonded only when the depositor wants to leave
//!   and dismantle the pool. All that said, the message is: the depositor can only leave the chain
//!   when they chill the pool first.
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
//!   members that where in the pool while it was backing a validator that got slashed.
//! * Maximize scalability in terms of member count.
//!
//! In order to maintain scalability, all operations are independent of the number of members. To do
//! this, delegation specific information is stored local to the member while the pool data
//! structures have bounded datum.
//!
//! ### Bonded pool
//!
//! A bonded pool nominates with its total balance, excluding that which has been withdrawn for
//! unbonding. The total points of a bonded pool are always equal to the sum of points of the
//! delegation members. A bonded pool tracks its points and reads its bonded balance.
//!
//! When a member joins a pool, `amount_transferred` is transferred from the members account to the
//! bonded pools account. Then the pool calls `staking::bond_extra(amount_transferred)` and issues
//! new points which are tracked by the member and added to the bonded pool's points.
//!
//! When the pool already has some balance, we want the value of a point before the transfer to
//! equal the value of a point after the transfer. So, when a member joins a bonded pool with a
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
//! When a pool is first bonded it sets up a deterministic, inaccessible account as its reward
//! destination. This reward account combined with `RewardPool` compose a reward pool.
//!
//! Reward pools are completely separate entities to bonded pools. Along with its account, a reward
//! pool also tracks its outstanding and claimed rewards as counters, in addition to pending and
//! claimed commission. These counters are updated with `RewardPool::update_records`. The current
//! reward counter of the pool (the total outstanding rewards, in points) is also callable with the
//! `RewardPool::current_reward_counter` method.
//!
//! See [this link](https://hackmd.io/PFGn6wI5TbCmBYoEA_f2Uw) for an in-depth explanation of the
//! reward pool mechanism.
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::claim_payout`]
//!
//! ### Unbonding sub pools
//!
//! When a member unbonds, it's balance is unbonded in the bonded pool's account and tracked in an
//! unbonding pool associated with the active era. If no such pool exists, one is created. To track
//! which unbonding sub pool a member belongs too, a member tracks it's `unbonding_era`.
//!
//! When a member initiates unbonding it's claim on the bonded pool (`balance_to_unbond`) is
//! computed as:
//!
//! ```text
//! balance_to_unbond = (bonded_pool.balance / bonded_pool.points) * member.points;
//! ```
//!
//! If this is the first transfer into an unbonding pool arbitrary amount of points can be issued
//! per balance. In this implementation unbonding pools are initialized with a 1 point to 1 balance
//! ratio (see [`POINTS_TO_BALANCE_INIT_RATIO`]). Otherwise, the unbonding pools hold the same
//! points to balance ratio properties as the bonded pool, so member points in the unbonding pool
//! are issued based on
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
//! Once a members `unbonding_era` is older than `current_era -
//! [sp_staking::StakingInterface::bonding_duration]`, it can can cash it's points out of the
//! corresponding unbonding pool. If it's `unbonding_era` is older than `current_era -
//! TotalUnbondingPools`, it can cash it's points from the unbonded pool.
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::unbond`]
//! * [`Call::withdraw_unbonded`]
//!
//! ### Slashing
//!
//! This section assumes that the slash computation is executed by
//! `pallet_staking::StakingLedger::slash`, which passes the information to this pallet via
//! [`sp_staking::OnStakingUpdate::on_slash`].
//!
//! Unbonding pools need to be slashed to ensure all nominators whom where in the bonded pool while
//! it was backing a validator that equivocated are punished. Without these measures a member could
//! unbond right after a validator equivocated with no consequences.
//!
//! This strategy is unfair to members who joined after the slash, because they get slashed as well,
//! but spares members who unbond. The latter is much more important for security: if a pool's
//! validators are attacking the network, their members need to unbond fast! Avoiding slashes gives
//! them an incentive to do that if validators get repeatedly slashed.
//!
//! To be fair to joiners, this implementation also need joining pools, which are actively staking,
//! in addition to the unbonding pools. For maintenance simplicity these are not implemented.
//! Related: <https://github.com/paritytech/substrate/issues/10860>
//!
//! ### Limitations
//!
//! * PoolMembers cannot vote with their staked funds because they are transferred into the pools
//!   account. In the future this can be overcome by allowing the members to vote with their bonded
//!   funds via vote splitting.
//! * PoolMembers cannot quickly transfer to another pool if they do no like nominations, instead
//!   they must wait for the unbonding duration.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use frame_support::{
	defensive, ensure,
	pallet_prelude::{MaxEncodedLen, *},
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{
		Currency, Defensive, DefensiveOption, DefensiveResult, DefensiveSaturating,
		ExistenceRequirement, Get,
	},
	DefaultNoBound, PalletError,
};
use frame_system::pallet_prelude::BlockNumberFor;
use scale_info::TypeInfo;
use sp_core::U256;
use sp_runtime::{
	traits::{
		AccountIdConversion, Bounded, CheckedAdd, CheckedSub, Convert, Saturating, StaticLookup,
		Zero,
	},
	FixedPointNumber, Perbill,
};
use sp_staking::{EraIndex, StakingInterface};
use sp_std::{collections::btree_map::BTreeMap, fmt::Debug, ops::Div, vec::Vec};

#[cfg(any(feature = "try-runtime", feature = "fuzzing", test, debug_assertions))]
use sp_runtime::TryRuntimeError;

/// The log target of this pallet.
pub const LOG_TARGET: &str = "runtime::nomination-pools";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: $crate::LOG_TARGET,
			concat!("[{:?}] 🏊‍♂️ ", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
		)
	};
}

#[cfg(any(test, feature = "fuzzing"))]
pub mod mock;
#[cfg(test)]
mod tests;

pub mod migration;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// The balance type used by the currency system.
pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
/// Type used for unique identifier of each pool.
pub type PoolId = u32;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

pub const POINTS_TO_BALANCE_INIT_RATIO: u32 = 1;

/// Possible operations on the configuration values of this pallet.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound, PartialEq, Clone)]
pub enum ConfigOp<T: Codec + Debug> {
	/// Don't change.
	Noop,
	/// Set the given value.
	Set(T),
	/// Remove from storage.
	Remove,
}

/// The type of bonding that can happen to a pool.
enum BondType {
	/// Someone is bonding into the pool upon creation.
	Create,
	/// Someone is adding more funds later to this pool.
	Later,
}

/// How to increase the bond of a member.
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

/// The permission a pool member can set for other accounts to claim rewards on their behalf.
#[derive(Encode, Decode, MaxEncodedLen, Clone, Copy, Debug, PartialEq, Eq, TypeInfo)]
pub enum ClaimPermission {
	/// Only the pool member themself can claim their rewards.
	Permissioned,
	/// Anyone can compound rewards on a pool member's behalf.
	PermissionlessCompound,
	/// Anyone can withdraw rewards on a pool member's behalf.
	PermissionlessWithdraw,
	/// Anyone can withdraw and compound rewards on a member's behalf.
	PermissionlessAll,
}

impl ClaimPermission {
	fn can_bond_extra(&self) -> bool {
		matches!(self, ClaimPermission::PermissionlessAll | ClaimPermission::PermissionlessCompound)
	}

	fn can_claim_payout(&self) -> bool {
		matches!(self, ClaimPermission::PermissionlessAll | ClaimPermission::PermissionlessWithdraw)
	}
}

impl Default for ClaimPermission {
	fn default() -> Self {
		Self::Permissioned
	}
}

/// A member in a pool.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound, CloneNoBound)]
#[cfg_attr(feature = "std", derive(frame_support::PartialEqNoBound, DefaultNoBound))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct PoolMember<T: Config> {
	/// The identifier of the pool to which `who` belongs.
	pub pool_id: PoolId,
	/// The quantity of points this member has in the bonded pool or in a sub pool if
	/// `Self::unbonding_era` is some.
	pub points: BalanceOf<T>,
	/// The reward counter at the time of this member's last payout claim.
	pub last_recorded_reward_counter: T::RewardCounter,
	/// The eras in which this member is unbonding, mapped from era index to the number of
	/// points scheduled to unbond in the given era.
	pub unbonding_eras: BoundedBTreeMap<EraIndex, BalanceOf<T>, T::MaxUnbonding>,
}

impl<T: Config> PoolMember<T> {
	/// The pending rewards of this member.
	fn pending_rewards(
		&self,
		current_reward_counter: T::RewardCounter,
	) -> Result<BalanceOf<T>, Error<T>> {
		// accuracy note: Reward counters are `FixedU128` with base of 10^18. This value is being
		// multiplied by a point. The worse case of a point is 10x the granularity of the balance
		// (10x is the common configuration of `MaxPointsToBalance`).
		//
		// Assuming roughly the current issuance of polkadot (12,047,781,394,999,601,455, which is
		// 1.2 * 10^9 * 10^10 = 1.2 * 10^19), the worse case point value is around 10^20.
		//
		// The final multiplication is:
		//
		// rc * 10^20 / 10^18 = rc * 100
		//
		// the implementation of `multiply_by_rational_with_rounding` shows that it will only fail
		// if the final division is not enough to fit in u128. In other words, if `rc * 100` is more
		// than u128::max. Given that RC is interpreted as reward per unit of point, and unit of
		// point is equal to balance (normally), and rewards are usually a proportion of the points
		// in the pool, the likelihood of rc reaching near u128::MAX is near impossible.

		(current_reward_counter.defensive_saturating_sub(self.last_recorded_reward_counter))
			.checked_mul_int(self.active_points())
			.ok_or(Error::<T>::OverflowRisk)
	}

	/// Active balance of the member.
	///
	/// This is derived from the ratio of points in the pool to which the member belongs to.
	/// Might return different values based on the pool state for the same member and points.
	fn active_balance(&self) -> BalanceOf<T> {
		if let Some(pool) = BondedPool::<T>::get(self.pool_id).defensive() {
			pool.points_to_balance(self.points)
		} else {
			Zero::zero()
		}
	}

	/// Total points of this member, both active and unbonding.
	fn total_points(&self) -> BalanceOf<T> {
		self.active_points().saturating_add(self.unbonding_points())
	}

	/// Active points of the member.
	fn active_points(&self) -> BalanceOf<T> {
		self.points
	}

	/// Inactive points of the member, waiting to be withdrawn.
	fn unbonding_points(&self) -> BalanceOf<T> {
		self.unbonding_eras
			.as_ref()
			.iter()
			.fold(BalanceOf::<T>::zero(), |acc, (_, v)| acc.saturating_add(*v))
	}

	/// Try and unbond `points_dissolved` from self, and in return mint `points_issued` into the
	/// corresponding `era`'s unlock schedule.
	///
	/// In the absence of slashing, these two points are always the same. In the presence of
	/// slashing, the value of points in different pools varies.
	///
	/// Returns `Ok(())` and updates `unbonding_eras` and `points` if success, `Err(_)` otherwise.
	fn try_unbond(
		&mut self,
		points_dissolved: BalanceOf<T>,
		points_issued: BalanceOf<T>,
		unbonding_era: EraIndex,
	) -> Result<(), Error<T>> {
		if let Some(new_points) = self.points.checked_sub(&points_dissolved) {
			match self.unbonding_eras.get_mut(&unbonding_era) {
				Some(already_unbonding_points) =>
					*already_unbonding_points =
						already_unbonding_points.saturating_add(points_issued),
				None => self
					.unbonding_eras
					.try_insert(unbonding_era, points_issued)
					.map(|old| {
						if old.is_some() {
							defensive!("value checked to not exist in the map; qed");
						}
					})
					.map_err(|_| Error::<T>::MaxUnbondingLimit)?,
			}
			self.points = new_points;
			Ok(())
		} else {
			Err(Error::<T>::MinimumBondNotMet)
		}
	}

	/// Withdraw any funds in [`Self::unbonding_eras`] who's deadline in reached and is fully
	/// unlocked.
	///
	/// Returns a a subset of [`Self::unbonding_eras`] that got withdrawn.
	///
	/// Infallible, noop if no unbonding eras exist.
	fn withdraw_unlocked(
		&mut self,
		current_era: EraIndex,
	) -> BoundedBTreeMap<EraIndex, BalanceOf<T>, T::MaxUnbonding> {
		// NOTE: if only drain-filter was stable..
		let mut removed_points =
			BoundedBTreeMap::<EraIndex, BalanceOf<T>, T::MaxUnbonding>::default();
		self.unbonding_eras.retain(|e, p| {
			if *e > current_era {
				true
			} else {
				removed_points
					.try_insert(*e, *p)
					.expect("source map is bounded, this is a subset, will be bounded; qed");
				false
			}
		});
		removed_points
	}
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
	/// All members can now be permissionlessly unbonded, and the pool can never go back to any
	/// other state other than being dissolved.
	Destroying,
}

/// Pool administration roles.
///
/// Any pool has a depositor, which can never change. But, all the other roles are optional, and
/// cannot exist. Note that if `root` is set to `None`, it basically means that the roles of this
/// pool can never change again (except via governance).
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Debug, PartialEq, Clone)]
pub struct PoolRoles<AccountId> {
	/// Creates the pool and is the initial member. They can only leave the pool once all other
	/// members have left. Once they fully leave, the pool is destroyed.
	pub depositor: AccountId,
	/// Can change the nominator, bouncer, or itself and can perform any of the actions the
	/// nominator or bouncer can.
	pub root: Option<AccountId>,
	/// Can select which validators the pool nominates.
	pub nominator: Option<AccountId>,
	/// Can change the pools state and kick members if the pool is blocked.
	pub bouncer: Option<AccountId>,
}

/// Pool commission.
///
/// The pool `root` can set commission configuration after pool creation. By default, all commission
/// values are `None`. Pool `root` can also set `max` and `change_rate` configurations before
/// setting an initial `current` commission.
///
/// `current` is a tuple of the commission percentage and payee of commission. `throttle_from`
/// keeps track of which block `current` was last updated. A `max` commission value can only be
/// decreased after the initial value is set, to prevent commission from repeatedly increasing.
///
/// An optional commission `change_rate` allows the pool to set strict limits to how much commission
/// can change in each update, and how often updates can take place.
#[derive(
	Encode, Decode, DefaultNoBound, MaxEncodedLen, TypeInfo, DebugNoBound, PartialEq, Copy, Clone,
)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Commission<T: Config> {
	/// Optional commission rate of the pool along with the account commission is paid to.
	pub current: Option<(Perbill, T::AccountId)>,
	/// Optional maximum commission that can be set by the pool `root`. Once set, this value can
	/// only be updated to a decreased value.
	pub max: Option<Perbill>,
	/// Optional configuration around how often commission can be updated, and when the last
	/// commission update took place.
	pub change_rate: Option<CommissionChangeRate<BlockNumberFor<T>>>,
	/// The block from where throttling should be checked from. This value will be updated on all
	/// commission updates and when setting an initial `change_rate`.
	pub throttle_from: Option<BlockNumberFor<T>>,
}

impl<T: Config> Commission<T> {
	/// Returns true if the current commission updating to `to` would exhaust the change rate
	/// limits.
	///
	/// A commission update will be throttled (disallowed) if:
	/// 1. not enough blocks have passed since the `throttle_from` block, if exists, or
	/// 2. the new commission is greater than the maximum allowed increase.
	fn throttling(&self, to: &Perbill) -> bool {
		if let Some(t) = self.change_rate.as_ref() {
			let commission_as_percent =
				self.current.as_ref().map(|(x, _)| *x).unwrap_or(Perbill::zero());

			// do not throttle if `to` is the same or a decrease in commission.
			if *to <= commission_as_percent {
				return false
			}
			// Test for `max_increase` throttling.
			//
			// Throttled if the attempted increase in commission is greater than `max_increase`.
			if (*to).saturating_sub(commission_as_percent) > t.max_increase {
				return true
			}

			// Test for `min_delay` throttling.
			//
			// Note: matching `None` is defensive only. `throttle_from` should always exist where
			// `change_rate` has already been set, so this scenario should never happen.
			return self.throttle_from.map_or_else(
				|| {
					defensive!("throttle_from should exist if change_rate is set");
					true
				},
				|f| {
					// if `min_delay` is zero (no delay), not throttling.
					if t.min_delay == Zero::zero() {
						false
					} else {
						// throttling if blocks passed is less than `min_delay`.
						let blocks_surpassed =
							<frame_system::Pallet<T>>::block_number().saturating_sub(f);
						blocks_surpassed < t.min_delay
					}
				},
			)
		}
		false
	}

	/// Gets the pool's current commission, or returns Perbill::zero if none is set.
	/// Bounded to global max if current is greater than `GlobalMaxCommission`.
	fn current(&self) -> Perbill {
		self.current
			.as_ref()
			.map_or(Perbill::zero(), |(c, _)| *c)
			.min(GlobalMaxCommission::<T>::get().unwrap_or(Bounded::max_value()))
	}

	/// Set the pool's commission.
	///
	/// Update commission based on `current`. If a `None` is supplied, allow the commission to be
	/// removed without any change rate restrictions. Updates `throttle_from` to the current block.
	/// If the supplied commission is zero, `None` will be inserted and `payee` will be ignored.
	fn try_update_current(&mut self, current: &Option<(Perbill, T::AccountId)>) -> DispatchResult {
		self.current = match current {
			None => None,
			Some((commission, payee)) => {
				ensure!(!self.throttling(commission), Error::<T>::CommissionChangeThrottled);
				ensure!(
					commission <= &GlobalMaxCommission::<T>::get().unwrap_or(Bounded::max_value()),
					Error::<T>::CommissionExceedsGlobalMaximum
				);
				ensure!(
					self.max.map_or(true, |m| commission <= &m),
					Error::<T>::CommissionExceedsMaximum
				);
				if commission.is_zero() {
					None
				} else {
					Some((*commission, payee.clone()))
				}
			},
		};
		self.register_update();
		Ok(())
	}

	/// Set the pool's maximum commission.
	///
	/// The pool's maximum commission can initially be set to any value, and only smaller values
	/// thereafter. If larger values are attempted, this function will return a dispatch error.
	///
	/// If `current.0` is larger than the updated max commission value, `current.0` will also be
	/// updated to the new maximum. This will also register a `throttle_from` update.
	/// A `PoolCommissionUpdated` event is triggered if `current.0` is updated.
	fn try_update_max(&mut self, pool_id: PoolId, new_max: Perbill) -> DispatchResult {
		ensure!(
			new_max <= GlobalMaxCommission::<T>::get().unwrap_or(Bounded::max_value()),
			Error::<T>::CommissionExceedsGlobalMaximum
		);
		if let Some(old) = self.max.as_mut() {
			if new_max > *old {
				return Err(Error::<T>::MaxCommissionRestricted.into())
			}
			*old = new_max;
		} else {
			self.max = Some(new_max)
		};
		let updated_current = self
			.current
			.as_mut()
			.map(|(c, _)| {
				let u = *c > new_max;
				*c = (*c).min(new_max);
				u
			})
			.unwrap_or(false);

		if updated_current {
			if let Some((_, payee)) = self.current.as_ref() {
				Pallet::<T>::deposit_event(Event::<T>::PoolCommissionUpdated {
					pool_id,
					current: Some((new_max, payee.clone())),
				});
			}
			self.register_update();
		}
		Ok(())
	}

	/// Set the pool's commission `change_rate`.
	///
	/// Once a change rate configuration has been set, only more restrictive values can be set
	/// thereafter. These restrictions translate to increased `min_delay` values and decreased
	/// `max_increase` values.
	///
	/// Update `throttle_from` to the current block upon setting change rate for the first time, so
	/// throttling can be checked from this block.
	fn try_update_change_rate(
		&mut self,
		change_rate: CommissionChangeRate<BlockNumberFor<T>>,
	) -> DispatchResult {
		ensure!(!&self.less_restrictive(&change_rate), Error::<T>::CommissionChangeRateNotAllowed);

		if self.change_rate.is_none() {
			self.register_update();
		}
		self.change_rate = Some(change_rate);
		Ok(())
	}

	/// Updates a commission's `throttle_from` field to the current block.
	fn register_update(&mut self) {
		self.throttle_from = Some(<frame_system::Pallet<T>>::block_number());
	}

	/// Checks whether a change rate is less restrictive than the current change rate, if any.
	///
	/// No change rate will always be less restrictive than some change rate, so where no
	/// `change_rate` is currently set, `false` is returned.
	fn less_restrictive(&self, new: &CommissionChangeRate<BlockNumberFor<T>>) -> bool {
		self.change_rate
			.as_ref()
			.map(|c| new.max_increase > c.max_increase || new.min_delay < c.min_delay)
			.unwrap_or(false)
	}
}

/// Pool commission change rate preferences.
///
/// The pool root is able to set a commission change rate for their pool. A commission change rate
/// consists of 2 values; (1) the maximum allowed commission change, and (2) the minimum amount of
/// blocks that must elapse before commission updates are allowed again.
///
/// Commission change rates are not applied to decreases in commission.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Debug, PartialEq, Copy, Clone)]
pub struct CommissionChangeRate<BlockNumber> {
	/// The maximum amount the commission can be updated by per `min_delay` period.
	pub max_increase: Perbill,
	/// How often an update can take place.
	pub min_delay: BlockNumber,
}

/// Pool permissions and state
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DebugNoBound, PartialEq, Clone)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct BondedPoolInner<T: Config> {
	/// The commission rate of the pool.
	pub commission: Commission<T>,
	/// Count of members that belong to the pool.
	pub member_counter: u32,
	/// Total points of all the members in the pool who are actively bonded.
	pub points: BalanceOf<T>,
	/// See [`PoolRoles`].
	pub roles: PoolRoles<T::AccountId>,
	/// The current state of the pool.
	pub state: PoolState,
}

/// A wrapper for bonded pools, with utility functions.
///
/// The main purpose of this is to wrap a [`BondedPoolInner`], with the account
/// + id of the pool, for easier access.
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
				commission: Commission::default(),
				member_counter: Zero::zero(),
				points: Zero::zero(),
				roles,
				state: PoolState::Open,
			},
		}
	}

	/// Get [`Self`] from storage. Returns `None` if no entry for `pool_account` exists.
	pub fn get(id: PoolId) -> Option<Self> {
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
		BondedPools::<T>::insert(self.id, self.inner);
	}

	/// Consume self and remove from storage.
	fn remove(self) {
		BondedPools::<T>::remove(self.id);
	}

	/// Convert the given amount of balance to points given the current pool state.
	///
	/// This is often used for bonding and issuing new funds into the pool.
	fn balance_to_point(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::Staking::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		Pallet::<T>::balance_to_point(bonded_balance, self.points, new_funds)
	}

	/// Convert the given number of points to balance given the current pool state.
	///
	/// This is often used for unbonding.
	fn points_to_balance(&self, points: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::Staking::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		Pallet::<T>::point_to_balance(bonded_balance, self.points, points)
	}

	/// Issue points to [`Self`] for `new_funds`.
	fn issue(&mut self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let points_to_issue = self.balance_to_point(new_funds);
		self.points = self.points.saturating_add(points_to_issue);
		points_to_issue
	}

	/// Dissolve some points from the pool i.e. unbond the given amount of points from this pool.
	/// This is the opposite of issuing some funds into the pool.
	///
	/// Mutates self in place, but does not write anything to storage.
	///
	/// Returns the equivalent balance amount that actually needs to get unbonded.
	fn dissolve(&mut self, points: BalanceOf<T>) -> BalanceOf<T> {
		// NOTE: do not optimize by removing `balance`. it must be computed before mutating
		// `self.point`.
		let balance = self.points_to_balance(points);
		self.points = self.points.saturating_sub(points);
		balance
	}

	/// Increment the member counter. Ensures that the pool and system member limits are
	/// respected.
	fn try_inc_members(&mut self) -> Result<(), DispatchError> {
		ensure!(
			MaxPoolMembersPerPool::<T>::get()
				.map_or(true, |max_per_pool| self.member_counter < max_per_pool),
			Error::<T>::MaxPoolMembers
		);
		ensure!(
			MaxPoolMembers::<T>::get().map_or(true, |max| PoolMembers::<T>::count() < max),
			Error::<T>::MaxPoolMembers
		);
		self.member_counter = self.member_counter.checked_add(1).ok_or(Error::<T>::OverflowRisk)?;
		Ok(())
	}

	/// Decrement the member counter.
	fn dec_members(mut self) -> Self {
		self.member_counter = self.member_counter.defensive_saturating_sub(1);
		self
	}

	/// The pools balance that is transferrable.
	fn transferrable_balance(&self) -> BalanceOf<T> {
		let account = self.bonded_account();
		T::Currency::free_balance(&account)
			.saturating_sub(T::Staking::active_stake(&account).unwrap_or_default())
	}

	fn is_root(&self, who: &T::AccountId) -> bool {
		self.roles.root.as_ref().map_or(false, |root| root == who)
	}

	fn is_bouncer(&self, who: &T::AccountId) -> bool {
		self.roles.bouncer.as_ref().map_or(false, |bouncer| bouncer == who)
	}

	fn can_update_roles(&self, who: &T::AccountId) -> bool {
		self.is_root(who)
	}

	fn can_nominate(&self, who: &T::AccountId) -> bool {
		self.is_root(who) ||
			self.roles.nominator.as_ref().map_or(false, |nominator| nominator == who)
	}

	fn can_kick(&self, who: &T::AccountId) -> bool {
		self.state == PoolState::Blocked && (self.is_root(who) || self.is_bouncer(who))
	}

	fn can_toggle_state(&self, who: &T::AccountId) -> bool {
		(self.is_root(who) || self.is_bouncer(who)) && !self.is_destroying()
	}

	fn can_set_metadata(&self, who: &T::AccountId) -> bool {
		self.is_root(who) || self.is_bouncer(who)
	}

	fn can_manage_commission(&self, who: &T::AccountId) -> bool {
		self.is_root(who)
	}

	fn is_destroying(&self) -> bool {
		matches!(self.state, PoolState::Destroying)
	}

	fn is_destroying_and_only_depositor(&self, alleged_depositor_points: BalanceOf<T>) -> bool {
		// we need to ensure that `self.member_counter == 1` as well, because the depositor's
		// initial `MinCreateBond` (or more) is what guarantees that the ledger of the pool does not
		// get killed in the staking system, and that it does not fall below `MinimumNominatorBond`,
		// which could prevent other non-depositor members from fully leaving. Thus, all members
		// must withdraw, then depositor can unbond, and finally withdraw after waiting another
		// cycle.
		self.is_destroying() && self.points == alleged_depositor_points && self.member_counter == 1
	}

	/// Whether or not the pool is ok to be in `PoolSate::Open`. If this returns an `Err`, then the
	/// pool is unrecoverable and should be in the destroying state.
	fn ok_to_be_open(&self) -> Result<(), DispatchError> {
		ensure!(!self.is_destroying(), Error::<T>::CanNotChangeState);

		let bonded_balance =
			T::Staking::active_stake(&self.bonded_account()).unwrap_or(Zero::zero());
		ensure!(!bonded_balance.is_zero(), Error::<T>::OverflowRisk);

		let points_to_balance_ratio_floor = self
			.points
			// We checked for zero above
			.div(bonded_balance);

		let max_points_to_balance = T::MaxPointsToBalance::get();

		// Pool points can inflate relative to balance, but only if the pool is slashed.
		// If we cap the ratio of points:balance so one cannot join a pool that has been slashed
		// by `max_points_to_balance`%, if not zero.
		ensure!(
			points_to_balance_ratio_floor < max_points_to_balance.into(),
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

	fn ok_to_unbond_with(
		&self,
		caller: &T::AccountId,
		target_account: &T::AccountId,
		target_member: &PoolMember<T>,
		unbonding_points: BalanceOf<T>,
	) -> Result<(), DispatchError> {
		let is_permissioned = caller == target_account;
		let is_depositor = *target_account == self.roles.depositor;
		let is_full_unbond = unbonding_points == target_member.active_points();

		let balance_after_unbond = {
			let new_depositor_points =
				target_member.active_points().saturating_sub(unbonding_points);
			let mut target_member_after_unbond = (*target_member).clone();
			target_member_after_unbond.points = new_depositor_points;
			target_member_after_unbond.active_balance()
		};

		// any partial unbonding is only ever allowed if this unbond is permissioned.
		ensure!(
			is_permissioned || is_full_unbond,
			Error::<T>::PartialUnbondNotAllowedPermissionlessly
		);

		// any unbond must comply with the balance condition:
		ensure!(
			is_full_unbond ||
				balance_after_unbond >=
					if is_depositor {
						Pallet::<T>::depositor_min_bond()
					} else {
						MinJoinBond::<T>::get()
					},
			Error::<T>::MinimumBondNotMet
		);

		// additional checks:
		match (is_permissioned, is_depositor) {
			(true, false) => (),
			(true, true) => {
				// permission depositor unbond: if destroying and pool is empty, always allowed,
				// with no additional limits.
				if self.is_destroying_and_only_depositor(target_member.active_points()) {
					// everything good, let them unbond anything.
				} else {
					// depositor cannot fully unbond yet.
					ensure!(!is_full_unbond, Error::<T>::MinimumBondNotMet);
				}
			},
			(false, false) => {
				// If the pool is blocked, then an admin with kicking permissions can remove a
				// member. If the pool is being destroyed, anyone can remove a member
				debug_assert!(is_full_unbond);
				ensure!(
					self.can_kick(caller) || self.is_destroying(),
					Error::<T>::NotKickerOrDestroying
				)
			},
			(false, true) => {
				// the depositor can simply not be unbonded permissionlessly, period.
				return Err(Error::<T>::DoesNotHavePermission.into())
			},
		};

		Ok(())
	}

	/// # Returns
	///
	/// * Ok(()) if [`Call::withdraw_unbonded`] can be called, `Err(DispatchError)` otherwise.
	fn ok_to_withdraw_unbonded_with(
		&self,
		caller: &T::AccountId,
		target_account: &T::AccountId,
	) -> Result<(), DispatchError> {
		// This isn't a depositor
		let is_permissioned = caller == target_account;
		ensure!(
			is_permissioned || self.can_kick(caller) || self.is_destroying(),
			Error::<T>::NotKickerOrDestroying
		);
		Ok(())
	}

	/// Bond exactly `amount` from `who`'s funds into this pool.
	///
	/// If the bond type is `Create`, `Staking::bond` is called, and `who`
	/// is allowed to be killed. Otherwise, `Staking::bond_extra` is called and `who`
	/// cannot be killed.
	///
	/// Returns `Ok(points_issues)`, `Err` otherwise.
	fn try_bond_funds(
		&mut self,
		who: &T::AccountId,
		amount: BalanceOf<T>,
		ty: BondType,
	) -> Result<BalanceOf<T>, DispatchError> {
		// Cache the value
		let bonded_account = self.bonded_account();
		T::Currency::transfer(
			who,
			&bonded_account,
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
			BondType::Create => T::Staking::bond(&bonded_account, amount, &self.reward_account())?,
			// The pool should always be created in such a way its in a state to bond extra, but if
			// the active balance is slashed below the minimum bonded or the account cannot be
			// found, we exit early.
			BondType::Later => T::Staking::bond_extra(&bonded_account, amount)?,
		}

		Ok(points_issued)
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
///
/// A reward pool is not so much a pool anymore, since it does not contain any shares or points.
/// Rather, simply to fit nicely next to bonded pool and unbonding pools in terms of terminology. In
/// reality, a reward pool is just a container for a few pool-dependent data related to the rewards.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq, DefaultNoBound))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
	/// The last recorded value of the reward counter.
	///
	/// This is updated ONLY when the points in the bonded pool change, which means `join`,
	/// `bond_extra` and `unbond`, all of which is done through `update_recorded`.
	last_recorded_reward_counter: T::RewardCounter,
	/// The last recorded total payouts of the reward pool.
	///
	/// Payouts is essentially income of the pool.
	///
	/// Update criteria is same as that of `last_recorded_reward_counter`.
	last_recorded_total_payouts: BalanceOf<T>,
	/// Total amount that this pool has paid out so far to the members.
	total_rewards_claimed: BalanceOf<T>,
	/// The amount of commission pending to be claimed.
	total_commission_pending: BalanceOf<T>,
	/// The amount of commission that has been claimed.
	total_commission_claimed: BalanceOf<T>,
}

impl<T: Config> RewardPool<T> {
	/// Getter for [`RewardPool::last_recorded_reward_counter`].
	pub(crate) fn last_recorded_reward_counter(&self) -> T::RewardCounter {
		self.last_recorded_reward_counter
	}

	/// Register some rewards that are claimed from the pool by the members.
	fn register_claimed_reward(&mut self, reward: BalanceOf<T>) {
		self.total_rewards_claimed = self.total_rewards_claimed.saturating_add(reward);
	}

	/// Update the recorded values of the reward pool.
	///
	/// This function MUST be called whenever the points in the bonded pool change, AND whenever the
	/// the pools commission is updated. The reason for the former is that a change in pool points
	/// will alter the share of the reward balance among pool members, and the reason for the latter
	/// is that a change in commission will alter the share of the reward balance among the pool.
	fn update_records(
		&mut self,
		id: PoolId,
		bonded_points: BalanceOf<T>,
		commission: Perbill,
	) -> Result<(), Error<T>> {
		let balance = Self::current_balance(id);

		let (current_reward_counter, new_pending_commission) =
			self.current_reward_counter(id, bonded_points, commission)?;

		// Store the reward counter at the time of this update. This is used in subsequent calls to
		// `current_reward_counter`, whereby newly pending rewards (in points) are added to this
		// value.
		self.last_recorded_reward_counter = current_reward_counter;

		// Add any new pending commission that has been calculated from `current_reward_counter` to
		// determine the total pending commission at the time of this update.
		self.total_commission_pending =
			self.total_commission_pending.saturating_add(new_pending_commission);

		// Store the total payouts at the time of this update. Total payouts are essentially the
		// entire historical balance of the reward pool, equating to the current balance + the total
		// rewards that have left the pool + the total commission that has left the pool.
		self.last_recorded_total_payouts = balance
			.checked_add(&self.total_rewards_claimed.saturating_add(self.total_commission_claimed))
			.ok_or(Error::<T>::OverflowRisk)?;

		Ok(())
	}

	/// Get the current reward counter, based on the given `bonded_points` being the state of the
	/// bonded pool at this time.
	fn current_reward_counter(
		&self,
		id: PoolId,
		bonded_points: BalanceOf<T>,
		commission: Perbill,
	) -> Result<(T::RewardCounter, BalanceOf<T>), Error<T>> {
		let balance = Self::current_balance(id);

		// Calculate the current payout balance. The first 3 values of this calculation added
		// together represent what the balance would be if no payouts were made. The
		// `last_recorded_total_payouts` is then subtracted from this value to cancel out previously
		// recorded payouts, leaving only the remaining payouts that have not been claimed.
		let current_payout_balance = balance
			.saturating_add(self.total_rewards_claimed)
			.saturating_add(self.total_commission_claimed)
			.saturating_sub(self.last_recorded_total_payouts);

		// Split the `current_payout_balance` into claimable rewards and claimable commission
		// according to the current commission rate.
		let new_pending_commission = commission * current_payout_balance;
		let new_pending_rewards = current_payout_balance.saturating_sub(new_pending_commission);

		// * accuracy notes regarding the multiplication in `checked_from_rational`:
		// `current_payout_balance` is a subset of the total_issuance at the very worse.
		// `bonded_points` are similarly, in a non-slashed pool, have the same granularity as
		// balance, and are thus below within the range of total_issuance. In the worse case
		// scenario, for `saturating_from_rational`, we have:
		//
		// dot_total_issuance * 10^18 / `minJoinBond`
		//
		// assuming `MinJoinBond == ED`
		//
		// dot_total_issuance * 10^18 / 10^10 = dot_total_issuance * 10^8
		//
		// which, with the current numbers, is a miniscule fraction of the u128 capacity.
		//
		// Thus, adding two values of type reward counter should be safe for ages in a chain like
		// Polkadot. The important note here is that `reward_pool.last_recorded_reward_counter` only
		// ever accumulates, but its semantics imply that it is less than total_issuance, when
		// represented as `FixedU128`, which means it is less than `total_issuance * 10^18`.
		//
		// * accuracy notes regarding `checked_from_rational` collapsing to zero, meaning that no
		//   reward can be claimed:
		//
		// largest `bonded_points`, such that the reward counter is non-zero, with `FixedU128` will
		// be when the payout is being computed. This essentially means `payout/bonded_points` needs
		// to be more than 1/1^18. Thus, assuming that `bonded_points` will always be less than `10
		// * dot_total_issuance`, if the reward_counter is the smallest possible value, the value of
		//   the
		// reward being calculated is:
		//
		// x / 10^20 = 1/ 10^18
		//
		// x = 100
		//
		// which is basically 10^-8 DOTs. See `smallest_claimable_reward` for an example of this.
		let current_reward_counter =
			T::RewardCounter::checked_from_rational(new_pending_rewards, bonded_points)
				.and_then(|ref r| self.last_recorded_reward_counter.checked_add(r))
				.ok_or(Error::<T>::OverflowRisk)?;

		Ok((current_reward_counter, new_pending_commission))
	}

	/// Current free balance of the reward pool.
	///
	/// This is sum of all the rewards that are claimable by pool members.
	fn current_balance(id: PoolId) -> BalanceOf<T> {
		T::Currency::free_balance(&Pallet::<T>::create_reward_account(id))
			.saturating_sub(T::Currency::minimum_balance())
	}
}

/// An unbonding pool. This is always mapped with an era.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq, Eq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct UnbondPool<T: Config> {
	/// The points in this pool.
	points: BalanceOf<T>,
	/// The funds in the pool.
	balance: BalanceOf<T>,
}

impl<T: Config> UnbondPool<T> {
	fn balance_to_point(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		Pallet::<T>::balance_to_point(self.balance, self.points, new_funds)
	}

	fn point_to_balance(&self, points: BalanceOf<T>) -> BalanceOf<T> {
		Pallet::<T>::point_to_balance(self.balance, self.points, points)
	}

	/// Issue the equivalent points of `new_funds` into self.
	///
	/// Returns the actual amounts of points issued.
	fn issue(&mut self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let new_points = self.balance_to_point(new_funds);
		self.points = self.points.saturating_add(new_points);
		self.balance = self.balance.saturating_add(new_funds);
		new_points
	}

	/// Dissolve some points from the unbonding pool, reducing the balance of the pool
	/// proportionally.
	///
	/// This is the opposite of `issue`.
	///
	/// Returns the actual amount of `Balance` that was removed from the pool.
	fn dissolve(&mut self, points: BalanceOf<T>) -> BalanceOf<T> {
		let balance_to_unbond = self.point_to_balance(points);
		self.points = self.points.saturating_sub(points);
		self.balance = self.balance.saturating_sub(balance_to_unbond);

		balance_to_unbond
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
	with_era: BoundedBTreeMap<EraIndex, UnbondPool<T>, TotalUnbondingPools<T>>,
}

impl<T: Config> SubPools<T> {
	/// Merge the oldest `with_era` unbond pools into the `no_era` unbond pool.
	///
	/// This is often used whilst getting the sub-pool from storage, thus it consumes and returns
	/// `Self` for ergonomic purposes.
	fn maybe_merge_pools(mut self, current_era: EraIndex) -> Self {
		// Ex: if `TotalUnbondingPools` is 5 and current era is 10, we only want to retain pools
		// 6..=10. Note that in the first few eras where `checked_sub` is `None`, we don't remove
		// anything.
		if let Some(newest_era_to_remove) =
			current_era.checked_sub(T::PostUnbondingPoolsWindow::get())
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

	/// The sum of all unbonding balance, regardless of whether they are actually unlocked or not.
	#[cfg(any(feature = "try-runtime", feature = "fuzzing", test, debug_assertions))]
	fn sum_unbonding_balance(&self) -> BalanceOf<T> {
		self.no_era.balance.saturating_add(
			self.with_era
				.values()
				.fold(BalanceOf::<T>::zero(), |acc, pool| acc.saturating_add(pool.balance)),
		)
	}
}

/// The maximum amount of eras an unbonding pool can exist prior to being merged with the
/// `no_era` pool. This is guaranteed to at least be equal to the staking `UnbondingDuration`. For
/// improved UX [`Config::PostUnbondingPoolsWindow`] should be configured to a non-zero value.
pub struct TotalUnbondingPools<T: Config>(PhantomData<T>);
impl<T: Config> Get<u32> for TotalUnbondingPools<T> {
	fn get() -> u32 {
		// NOTE: this may be dangerous in the scenario bonding_duration gets decreased because
		// we would no longer be able to decode `BoundedBTreeMap::<EraIndex, UnbondPool<T>,
		// TotalUnbondingPools<T>>`, which uses `TotalUnbondingPools` as the bound
		T::Staking::bonding_duration() + T::PostUnbondingPoolsWindow::get()
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::traits::StorageVersion;
	use frame_system::{ensure_signed, pallet_prelude::*};
	use sp_runtime::Perbill;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(5);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		/// The nominating balance.
		type Currency: Currency<Self::AccountId>;

		/// The type that is used for reward counter.
		///
		/// The arithmetic of the reward counter might saturate based on the size of the
		/// `Currency::Balance`. If this happens, operations fails. Nonetheless, this type should be
		/// chosen such that this failure almost never happens, as if it happens, the pool basically
		/// needs to be dismantled (or all pools migrated to a larger `RewardCounter` type, which is
		/// a PITA to do).
		///
		/// See the inline code docs of `Member::pending_rewards` and `RewardPool::update_recorded`
		/// for example analysis. A [`sp_runtime::FixedU128`] should be fine for chains with balance
		/// types similar to that of Polkadot and Kusama, in the absence of severe slashing (or
		/// prevented via a reasonable `MaxPointsToBalance`), for many many years to come.
		type RewardCounter: FixedPointNumber + MaxEncodedLen + TypeInfo + Default + codec::FullCodec;

		/// The nomination pool's pallet id.
		#[pallet::constant]
		type PalletId: Get<frame_support::PalletId>;

		/// The maximum pool points-to-balance ratio that an `open` pool can have.
		///
		/// This is important in the event slashing takes place and the pool's points-to-balance
		/// ratio becomes disproportional.
		///
		/// Moreover, this relates to the `RewardCounter` type as well, as the arithmetic operations
		/// are a function of number of points, and by setting this value to e.g. 10, you ensure
		/// that the total number of points in the system are at most 10 times the total_issuance of
		/// the chain, in the absolute worse case.
		///
		/// For a value of 10, the threshold would be a pool points-to-balance ratio of 10:1.
		/// Such a scenario would also be the equivalent of the pool being 90% slashed.
		#[pallet::constant]
		type MaxPointsToBalance: Get<u8>;

		/// Infallible method for converting `Currency::Balance` to `U256`.
		type BalanceToU256: Convert<BalanceOf<Self>, U256>;

		/// Infallible method for converting `U256` to `Currency::Balance`.
		type U256ToBalance: Convert<U256, BalanceOf<Self>>;

		/// The interface for nominating.
		type Staking: StakingInterface<Balance = BalanceOf<Self>, AccountId = Self::AccountId>;

		/// The amount of eras a `SubPools::with_era` pool can exist before it gets merged into the
		/// `SubPools::no_era` pool. In other words, this is the amount of eras a member will be
		/// able to withdraw from an unbonding pool which is guaranteed to have the correct ratio of
		/// points to balance; once the `with_era` pool is merged into the `no_era` pool, the ratio
		/// can become skewed due to some slashed ratio getting merged in at some point.
		type PostUnbondingPoolsWindow: Get<u32>;

		/// The maximum length, in bytes, that a pools metadata maybe.
		type MaxMetadataLen: Get<u32>;

		/// The maximum number of simultaneous unbonding chunks that can exist per member.
		type MaxUnbonding: Get<u32>;
	}

	/// Minimum amount to bond to join a pool.
	#[pallet::storage]
	pub type MinJoinBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Minimum bond required to create a pool.
	///
	/// This is the amount that the depositor must put as their initial stake in the pool, as an
	/// indication of "skin in the game".
	///
	/// This is the value that will always exist in the staking ledger of the pool bonded account
	/// while all other accounts leave.
	#[pallet::storage]
	pub type MinCreateBond<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Maximum number of nomination pools that can exist. If `None`, then an unbounded number of
	/// pools can exist.
	#[pallet::storage]
	pub type MaxPools<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// Maximum number of members that can exist in the system. If `None`, then the count
	/// members are not bound on a system wide basis.
	#[pallet::storage]
	pub type MaxPoolMembers<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// Maximum number of members that may belong to pool. If `None`, then the count of
	/// members is not bound on a per pool basis.
	#[pallet::storage]
	pub type MaxPoolMembersPerPool<T: Config> = StorageValue<_, u32, OptionQuery>;

	/// The maximum commission that can be charged by a pool. Used on commission payouts to bound
	/// pool commissions that are > `GlobalMaxCommission`, necessary if a future
	/// `GlobalMaxCommission` is lower than some current pool commissions.
	#[pallet::storage]
	pub type GlobalMaxCommission<T: Config> = StorageValue<_, Perbill, OptionQuery>;

	/// Active members.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	pub type PoolMembers<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, PoolMember<T>>;

	/// Storage for bonded pools.
	// To get or insert a pool see [`BondedPool::get`] and [`BondedPool::put`]
	#[pallet::storage]
	pub type BondedPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, BondedPoolInner<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a members payout is
	/// claimed, the balance comes out fo the reward pool. Keyed by the bonded pools account.
	#[pallet::storage]
	pub type RewardPools<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a
	/// bonded pool, hence the name sub-pools. Keyed by the bonded pools account.
	#[pallet::storage]
	pub type SubPoolsStorage<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, SubPools<T>>;

	/// Metadata for the pool.
	#[pallet::storage]
	pub type Metadata<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, BoundedVec<u8, T::MaxMetadataLen>, ValueQuery>;

	/// Ever increasing number of all pools created so far.
	#[pallet::storage]
	pub type LastPoolId<T: Config> = StorageValue<_, u32, ValueQuery>;

	/// A reverse lookup from the pool's account id to its id.
	///
	/// This is only used for slashing. In all other instances, the pool id is used, and the
	/// accounts are deterministically derived from it.
	#[pallet::storage]
	pub type ReversePoolIdLookup<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, PoolId, OptionQuery>;

	/// Map from a pool member account to their opted claim permission.
	#[pallet::storage]
	pub type ClaimPermissions<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, ClaimPermission, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub min_join_bond: BalanceOf<T>,
		pub min_create_bond: BalanceOf<T>,
		pub max_pools: Option<u32>,
		pub max_members_per_pool: Option<u32>,
		pub max_members: Option<u32>,
		pub global_max_commission: Option<Perbill>,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				min_join_bond: Zero::zero(),
				min_create_bond: Zero::zero(),
				max_pools: Some(16),
				max_members_per_pool: Some(32),
				max_members: Some(16 * 32),
				global_max_commission: None,
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			MinJoinBond::<T>::put(self.min_join_bond);
			MinCreateBond::<T>::put(self.min_create_bond);
			if let Some(max_pools) = self.max_pools {
				MaxPools::<T>::put(max_pools);
			}
			if let Some(max_members_per_pool) = self.max_members_per_pool {
				MaxPoolMembersPerPool::<T>::put(max_members_per_pool);
			}
			if let Some(max_members) = self.max_members {
				MaxPoolMembers::<T>::put(max_members);
			}
			if let Some(global_max_commission) = self.global_max_commission {
				GlobalMaxCommission::<T>::put(global_max_commission);
			}
		}
	}

	/// Events of this pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A pool has been created.
		Created { depositor: T::AccountId, pool_id: PoolId },
		/// A member has became bonded in a pool.
		Bonded { member: T::AccountId, pool_id: PoolId, bonded: BalanceOf<T>, joined: bool },
		/// A payout has been made to a member.
		PaidOut { member: T::AccountId, pool_id: PoolId, payout: BalanceOf<T> },
		/// A member has unbonded from their pool.
		///
		/// - `balance` is the corresponding balance of the number of points that has been
		///   requested to be unbonded (the argument of the `unbond` transaction) from the bonded
		///   pool.
		/// - `points` is the number of points that are issued as a result of `balance` being
		/// dissolved into the corresponding unbonding pool.
		/// - `era` is the era in which the balance will be unbonded.
		/// In the absence of slashing, these values will match. In the presence of slashing, the
		/// number of points that are issued in the unbonding pool will be less than the amount
		/// requested to be unbonded.
		Unbonded {
			member: T::AccountId,
			pool_id: PoolId,
			balance: BalanceOf<T>,
			points: BalanceOf<T>,
			era: EraIndex,
		},
		/// A member has withdrawn from their pool.
		///
		/// The given number of `points` have been dissolved in return of `balance`.
		///
		/// Similar to `Unbonded` event, in the absence of slashing, the ratio of point to balance
		/// will be 1.
		Withdrawn {
			member: T::AccountId,
			pool_id: PoolId,
			balance: BalanceOf<T>,
			points: BalanceOf<T>,
		},
		/// A pool has been destroyed.
		Destroyed { pool_id: PoolId },
		/// The state of a pool has changed
		StateChanged { pool_id: PoolId, new_state: PoolState },
		/// A member has been removed from a pool.
		///
		/// The removal can be voluntary (withdrawn all unbonded funds) or involuntary (kicked).
		MemberRemoved { pool_id: PoolId, member: T::AccountId },
		/// The roles of a pool have been updated to the given new roles. Note that the depositor
		/// can never change.
		RolesUpdated {
			root: Option<T::AccountId>,
			bouncer: Option<T::AccountId>,
			nominator: Option<T::AccountId>,
		},
		/// The active balance of pool `pool_id` has been slashed to `balance`.
		PoolSlashed { pool_id: PoolId, balance: BalanceOf<T> },
		/// The unbond pool at `era` of pool `pool_id` has been slashed to `balance`.
		UnbondingPoolSlashed { pool_id: PoolId, era: EraIndex, balance: BalanceOf<T> },
		/// A pool's commission setting has been changed.
		PoolCommissionUpdated { pool_id: PoolId, current: Option<(Perbill, T::AccountId)> },
		/// A pool's maximum commission setting has been changed.
		PoolMaxCommissionUpdated { pool_id: PoolId, max_commission: Perbill },
		/// A pool's commission `change_rate` has been changed.
		PoolCommissionChangeRateUpdated {
			pool_id: PoolId,
			change_rate: CommissionChangeRate<BlockNumberFor<T>>,
		},
		/// Pool commission has been claimed.
		PoolCommissionClaimed { pool_id: PoolId, commission: BalanceOf<T> },
	}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// A (bonded) pool id does not exist.
		PoolNotFound,
		/// An account is not a member.
		PoolMemberNotFound,
		/// A reward pool does not exist. In all cases this is a system logic error.
		RewardPoolNotFound,
		/// A sub pool does not exist.
		SubPoolsNotFound,
		/// An account is already delegating in another pool. An account may only belong to one
		/// pool at a time.
		AccountBelongsToOtherPool,
		/// The member is fully unbonded (and thus cannot access the bonded and reward pool
		/// anymore to, for example, collect rewards).
		FullyUnbonding,
		/// The member cannot unbond further chunks due to reaching the limit.
		MaxUnbondingLimit,
		/// None of the funds can be withdrawn yet because the bonding duration has not passed.
		CannotWithdrawAny,
		/// The amount does not meet the minimum bond to either join or create a pool.
		///
		/// The depositor can never unbond to a value less than
		/// `Pallet::depositor_min_bond`. The caller does not have nominating
		/// permissions for the pool. Members can never unbond to a value below `MinJoinBond`.
		MinimumBondNotMet,
		/// The transaction could not be executed due to overflow risk for the pool.
		OverflowRisk,
		/// A pool must be in [`PoolState::Destroying`] in order for the depositor to unbond or for
		/// other members to be permissionlessly unbonded.
		NotDestroying,
		/// The caller does not have nominating permissions for the pool.
		NotNominator,
		/// Either a) the caller cannot make a valid kick or b) the pool is not destroying.
		NotKickerOrDestroying,
		/// The pool is not open to join
		NotOpen,
		/// The system is maxed out on pools.
		MaxPools,
		/// Too many members in the pool or system.
		MaxPoolMembers,
		/// The pools state cannot be changed.
		CanNotChangeState,
		/// The caller does not have adequate permissions.
		DoesNotHavePermission,
		/// Metadata exceeds [`Config::MaxMetadataLen`]
		MetadataExceedsMaxLen,
		/// Some error occurred that should never happen. This should be reported to the
		/// maintainers.
		Defensive(DefensiveError),
		/// Partial unbonding now allowed permissionlessly.
		PartialUnbondNotAllowedPermissionlessly,
		/// The pool's max commission cannot be set higher than the existing value.
		MaxCommissionRestricted,
		/// The supplied commission exceeds the max allowed commission.
		CommissionExceedsMaximum,
		/// The supplied commission exceeds global maximum commission.
		CommissionExceedsGlobalMaximum,
		/// Not enough blocks have surpassed since the last commission update.
		CommissionChangeThrottled,
		/// The submitted changes to commission change rate are not allowed.
		CommissionChangeRateNotAllowed,
		/// There is no pending commission to claim.
		NoPendingCommission,
		/// No commission current has been set.
		NoCommissionCurrentSet,
		/// Pool id currently in use.
		PoolIdInUse,
		/// Pool id provided is not correct/usable.
		InvalidPoolId,
		/// Bonding extra is restricted to the exact pending reward amount.
		BondExtraRestricted,
	}

	#[derive(Encode, Decode, PartialEq, TypeInfo, PalletError, RuntimeDebug)]
	pub enum DefensiveError {
		/// There isn't enough space in the unbond pool.
		NotEnoughSpaceInUnbondPool,
		/// A (bonded) pool id does not exist.
		PoolNotFound,
		/// A reward pool does not exist. In all cases this is a system logic error.
		RewardPoolNotFound,
		/// A sub pool does not exist.
		SubPoolsNotFound,
		/// The bonded account should only be killed by the staking system when the depositor is
		/// withdrawing
		BondedStashKilledPrematurely,
	}

	impl<T> From<DefensiveError> for Error<T> {
		fn from(e: DefensiveError) -> Error<T> {
			Error::<T>::Defensive(e)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Stake funds with a pool. The amount to bond is transferred from the member to the
		/// pools account and immediately increases the pools bond.
		///
		/// # Note
		///
		/// * An account can only be a member of a single pool.
		/// * An account cannot join the same pool multiple times.
		/// * This call will *not* dust the member account, so the member must have at least
		///   `existential deposit + amount` in their account.
		/// * Only a pool with [`PoolState::Open`] can be joined
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::join())]
		pub fn join(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			pool_id: PoolId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(amount >= MinJoinBond::<T>::get(), Error::<T>::MinimumBondNotMet);
			// If a member already exists that means they already belong to a pool
			ensure!(!PoolMembers::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_join()?;

			let mut reward_pool = RewardPools::<T>::get(pool_id)
				.defensive_ok_or::<Error<T>>(DefensiveError::RewardPoolNotFound.into())?;
			// IMPORTANT: reward pool records must be updated with the old points.
			reward_pool.update_records(
				pool_id,
				bonded_pool.points,
				bonded_pool.commission.current(),
			)?;

			bonded_pool.try_inc_members()?;
			let points_issued = bonded_pool.try_bond_funds(&who, amount, BondType::Later)?;

			PoolMembers::insert(
				who.clone(),
				PoolMember::<T> {
					pool_id,
					points: points_issued,
					// we just updated `last_known_reward_counter` to the current one in
					// `update_recorded`.
					last_recorded_reward_counter: reward_pool.last_recorded_reward_counter(),
					unbonding_eras: Default::default(),
				},
			);

			Self::deposit_event(Event::<T>::Bonded {
				member: who,
				pool_id,
				bonded: amount,
				joined: true,
			});

			bonded_pool.put();
			RewardPools::<T>::insert(pool_id, reward_pool);

			Ok(())
		}

		/// Bond `extra` more funds from `origin` into the pool to which they already belong.
		///
		/// Additional funds can come from either the free balance of the account, of from the
		/// accumulated rewards, see [`BondExtra`].
		///
		/// Bonding extra funds implies an automatic payout of all pending rewards as well.
		/// See `bond_extra_other` to bond pending rewards of `other` members.
		// NOTE: this transaction is implemented with the sole purpose of readability and
		// correctness, not optimization. We read/write several storage items multiple times instead
		// of just once, in the spirit reusing code.
		#[pallet::call_index(1)]
		#[pallet::weight(
			T::WeightInfo::bond_extra_transfer()
			.max(T::WeightInfo::bond_extra_other())
		)]
		pub fn bond_extra(origin: OriginFor<T>, extra: BondExtra<BalanceOf<T>>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_bond_extra(who.clone(), who, extra)
		}

		/// A bonded member can use this to claim their payout based on the rewards that the pool
		/// has accumulated since their last claimed payout (OR since joining if this is their first
		/// time claiming rewards). The payout will be transferred to the member's account.
		///
		/// The member will earn rewards pro rata based on the members stake vs the sum of the
		/// members in the pools stake. Rewards do not "expire".
		///
		/// See `claim_payout_other` to caim rewards on bahalf of some `other` pool member.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::claim_payout())]
		pub fn claim_payout(origin: OriginFor<T>) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			Self::do_claim_payout(signer.clone(), signer)
		}

		/// Unbond up to `unbonding_points` of the `member_account`'s funds from the pool. It
		/// implicitly collects the rewards one last time, since not doing so would mean some
		/// rewards would be forfeited.
		///
		/// Under certain conditions, this call can be dispatched permissionlessly (i.e. by any
		/// account).
		///
		/// # Conditions for a permissionless dispatch.
		///
		/// * The pool is blocked and the caller is either the root or bouncer. This is refereed to
		///   as a kick.
		/// * The pool is destroying and the member is not the depositor.
		/// * The pool is destroying, the member is the depositor and no other members are in the
		///   pool.
		///
		/// ## Conditions for permissioned dispatch (i.e. the caller is also the
		/// `member_account`):
		///
		/// * The caller is not the depositor.
		/// * The caller is the depositor, the pool is destroying and no other members are in the
		///   pool.
		///
		/// # Note
		///
		/// If there are too many unlocking chunks to unbond with the pool account,
		/// [`Call::pool_withdraw_unbonded`] can be called to try and minimize unlocking chunks.
		/// The [`StakingInterface::unbond`] will implicitly call [`Call::pool_withdraw_unbonded`]
		/// to try to free chunks if necessary (ie. if unbound was called and no unlocking chunks
		/// are available). However, it may not be possible to release the current unlocking chunks,
		/// in which case, the result of this call will likely be the `NoMoreChunks` error from the
		/// staking system.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::unbond())]
		pub fn unbond(
			origin: OriginFor<T>,
			member_account: AccountIdLookupOf<T>,
			#[pallet::compact] unbonding_points: BalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let member_account = T::Lookup::lookup(member_account)?;
			let (mut member, mut bonded_pool, mut reward_pool) =
				Self::get_member_with_pools(&member_account)?;

			bonded_pool.ok_to_unbond_with(&who, &member_account, &member, unbonding_points)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points no
			// longer exist in the bonded pool and thus they can no longer claim their payouts. It
			// is not strictly necessary to claim the rewards, but we do it here for UX.
			reward_pool.update_records(
				bonded_pool.id,
				bonded_pool.points,
				bonded_pool.commission.current(),
			)?;
			let _ = Self::do_reward_payout(&who, &mut member, &mut bonded_pool, &mut reward_pool)?;

			let current_era = T::Staking::current_era();
			let unbond_era = T::Staking::bonding_duration().saturating_add(current_era);

			// Unbond in the actual underlying nominator.
			let unbonding_balance = bonded_pool.dissolve(unbonding_points);
			T::Staking::unbond(&bonded_pool.bonded_account(), unbonding_balance)?;

			// Note that we lazily create the unbonding pools here if they don't already exist
			let mut sub_pools = SubPoolsStorage::<T>::get(member.pool_id)
				.unwrap_or_default()
				.maybe_merge_pools(current_era);

			// Update the unbond pool associated with the current era with the unbonded funds. Note
			// that we lazily create the unbond pool if it does not yet exist.
			if !sub_pools.with_era.contains_key(&unbond_era) {
				sub_pools
					.with_era
					.try_insert(unbond_era, UnbondPool::default())
					// The above call to `maybe_merge_pools` should ensure there is
					// always enough space to insert.
					.defensive_map_err::<Error<T>, _>(|_| {
						DefensiveError::NotEnoughSpaceInUnbondPool.into()
					})?;
			}

			let points_unbonded = sub_pools
				.with_era
				.get_mut(&unbond_era)
				// The above check ensures the pool exists.
				.defensive_ok_or::<Error<T>>(DefensiveError::PoolNotFound.into())?
				.issue(unbonding_balance);

			// Try and unbond in the member map.
			member.try_unbond(unbonding_points, points_unbonded, unbond_era)?;

			Self::deposit_event(Event::<T>::Unbonded {
				member: member_account.clone(),
				pool_id: member.pool_id,
				points: points_unbonded,
				balance: unbonding_balance,
				era: unbond_era,
			});

			// Now that we know everything has worked write the items to storage.
			SubPoolsStorage::insert(member.pool_id, sub_pools);
			Self::put_member_with_pools(&member_account, member, bonded_pool, reward_pool);
			Ok(())
		}

		/// Call `withdraw_unbonded` for the pools account. This call can be made by any account.
		///
		/// This is useful if their are too many unlocking chunks to call `unbond`, and some
		/// can be cleared by withdrawing. In the case there are too many unlocking chunks, the user
		/// would probably see an error like `NoMoreChunks` emitted from the staking system when
		/// they attempt to unbond.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::pool_withdraw_unbonded(*num_slashing_spans))]
		pub fn pool_withdraw_unbonded(
			origin: OriginFor<T>,
			pool_id: PoolId,
			num_slashing_spans: u32,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			let pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			// For now we only allow a pool to withdraw unbonded if its not destroying. If the pool
			// is destroying then `withdraw_unbonded` can be used.
			ensure!(pool.state != PoolState::Destroying, Error::<T>::NotDestroying);
			T::Staking::withdraw_unbonded(pool.bonded_account(), num_slashing_spans)?;
			Ok(())
		}

		/// Withdraw unbonded funds from `member_account`. If no bonded funds can be unbonded, an
		/// error is returned.
		///
		/// Under certain conditions, this call can be dispatched permissionlessly (i.e. by any
		/// account).
		///
		/// # Conditions for a permissionless dispatch
		///
		/// * The pool is in destroy mode and the target is not the depositor.
		/// * The target is the depositor and they are the only member in the sub pools.
		/// * The pool is blocked and the caller is either the root or bouncer.
		///
		/// # Conditions for permissioned dispatch
		///
		/// * The caller is the target and they are not the depositor.
		///
		/// # Note
		///
		/// If the target is the depositor, the pool will be destroyed.
		#[pallet::call_index(5)]
		#[pallet::weight(
			T::WeightInfo::withdraw_unbonded_kill(*num_slashing_spans)
		)]
		pub fn withdraw_unbonded(
			origin: OriginFor<T>,
			member_account: AccountIdLookupOf<T>,
			num_slashing_spans: u32,
		) -> DispatchResultWithPostInfo {
			let caller = ensure_signed(origin)?;
			let member_account = T::Lookup::lookup(member_account)?;
			let mut member =
				PoolMembers::<T>::get(&member_account).ok_or(Error::<T>::PoolMemberNotFound)?;
			let current_era = T::Staking::current_era();

			let bonded_pool = BondedPool::<T>::get(member.pool_id)
				.defensive_ok_or::<Error<T>>(DefensiveError::PoolNotFound.into())?;
			let mut sub_pools =
				SubPoolsStorage::<T>::get(member.pool_id).ok_or(Error::<T>::SubPoolsNotFound)?;

			bonded_pool.ok_to_withdraw_unbonded_with(&caller, &member_account)?;

			// NOTE: must do this after we have done the `ok_to_withdraw_unbonded_other_with` check.
			let withdrawn_points = member.withdraw_unlocked(current_era);
			ensure!(!withdrawn_points.is_empty(), Error::<T>::CannotWithdrawAny);

			// Before calculating the `balance_to_unbond`, we call withdraw unbonded to ensure the
			// `transferrable_balance` is correct.
			let stash_killed =
				T::Staking::withdraw_unbonded(bonded_pool.bonded_account(), num_slashing_spans)?;

			// defensive-only: the depositor puts enough funds into the stash so that it will only
			// be destroyed when they are leaving.
			ensure!(
				!stash_killed || caller == bonded_pool.roles.depositor,
				Error::<T>::Defensive(DefensiveError::BondedStashKilledPrematurely)
			);

			let mut sum_unlocked_points: BalanceOf<T> = Zero::zero();
			let balance_to_unbond = withdrawn_points
				.iter()
				.fold(BalanceOf::<T>::zero(), |accumulator, (era, unlocked_points)| {
					sum_unlocked_points = sum_unlocked_points.saturating_add(*unlocked_points);
					if let Some(era_pool) = sub_pools.with_era.get_mut(era) {
						let balance_to_unbond = era_pool.dissolve(*unlocked_points);
						if era_pool.points.is_zero() {
							sub_pools.with_era.remove(era);
						}
						accumulator.saturating_add(balance_to_unbond)
					} else {
						// A pool does not belong to this era, so it must have been merged to the
						// era-less pool.
						accumulator.saturating_add(sub_pools.no_era.dissolve(*unlocked_points))
					}
				})
				// A call to this transaction may cause the pool's stash to get dusted. If this
				// happens before the last member has withdrawn, then all subsequent withdraws will
				// be 0. However the unbond pools do no get updated to reflect this. In the
				// aforementioned scenario, this check ensures we don't try to withdraw funds that
				// don't exist. This check is also defensive in cases where the unbond pool does not
				// update its balance (e.g. a bug in the slashing hook.) We gracefully proceed in
				// order to ensure members can leave the pool and it can be destroyed.
				.min(bonded_pool.transferrable_balance());

			T::Currency::transfer(
				&bonded_pool.bonded_account(),
				&member_account,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)
			.defensive()?;

			Self::deposit_event(Event::<T>::Withdrawn {
				member: member_account.clone(),
				pool_id: member.pool_id,
				points: sum_unlocked_points,
				balance: balance_to_unbond,
			});

			let post_info_weight = if member.total_points().is_zero() {
				// remove any `ClaimPermission` associated with the member.
				ClaimPermissions::<T>::remove(&member_account);

				// member being reaped.
				PoolMembers::<T>::remove(&member_account);
				Self::deposit_event(Event::<T>::MemberRemoved {
					pool_id: member.pool_id,
					member: member_account.clone(),
				});

				if member_account == bonded_pool.roles.depositor {
					Pallet::<T>::dissolve_pool(bonded_pool);
					None
				} else {
					bonded_pool.dec_members().put();
					SubPoolsStorage::<T>::insert(member.pool_id, sub_pools);
					Some(T::WeightInfo::withdraw_unbonded_update(num_slashing_spans))
				}
			} else {
				// we certainly don't need to delete any pools, because no one is being removed.
				SubPoolsStorage::<T>::insert(member.pool_id, sub_pools);
				PoolMembers::<T>::insert(&member_account, member);
				Some(T::WeightInfo::withdraw_unbonded_update(num_slashing_spans))
			};

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
		/// * `bouncer` - The account to set as the [`PoolRoles::bouncer`].
		///
		/// # Note
		///
		/// In addition to `amount`, the caller will transfer the existential deposit; so the caller
		/// needs at have at least `amount + existential_deposit` transferrable.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::create())]
		pub fn create(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			root: AccountIdLookupOf<T>,
			nominator: AccountIdLookupOf<T>,
			bouncer: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let depositor = ensure_signed(origin)?;

			let pool_id = LastPoolId::<T>::try_mutate::<_, Error<T>, _>(|id| {
				*id = id.checked_add(1).ok_or(Error::<T>::OverflowRisk)?;
				Ok(*id)
			})?;

			Self::do_create(depositor, amount, root, nominator, bouncer, pool_id)
		}

		/// Create a new delegation pool with a previously used pool id
		///
		/// # Arguments
		///
		/// same as `create` with the inclusion of
		/// * `pool_id` - `A valid PoolId.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::create())]
		pub fn create_with_pool_id(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			root: AccountIdLookupOf<T>,
			nominator: AccountIdLookupOf<T>,
			bouncer: AccountIdLookupOf<T>,
			pool_id: PoolId,
		) -> DispatchResult {
			let depositor = ensure_signed(origin)?;

			ensure!(!BondedPools::<T>::contains_key(pool_id), Error::<T>::PoolIdInUse);
			ensure!(pool_id < LastPoolId::<T>::get(), Error::<T>::InvalidPoolId);

			Self::do_create(depositor, amount, root, nominator, bouncer, pool_id)
		}

		/// Nominate on behalf of the pool.
		///
		/// The dispatch origin of this call must be signed by the pool nominator or the pool
		/// root role.
		///
		/// This directly forward the call to the staking pallet, on behalf of the pool bonded
		/// account.
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::nominate(validators.len() as u32))]
		pub fn nominate(
			origin: OriginFor<T>,
			pool_id: PoolId,
			validators: Vec<T::AccountId>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_nominate(&who), Error::<T>::NotNominator);
			T::Staking::nominate(&bonded_pool.bonded_account(), validators)
		}

		/// Set a new state for the pool.
		///
		/// If a pool is already in the `Destroying` state, then under no condition can its state
		/// change again.
		///
		/// The dispatch origin of this call must be either:
		///
		/// 1. signed by the bouncer, or the root role of the pool,
		/// 2. if the pool conditions to be open are NOT met (as described by `ok_to_be_open`), and
		///    then the state of the pool can be permissionlessly changed to `Destroying`.
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::set_state())]
		pub fn set_state(
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

		/// Set a new metadata for the pool.
		///
		/// The dispatch origin of this call must be signed by the bouncer, or the root role of the
		/// pool.
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::set_metadata(metadata.len() as u32))]
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

		/// Update configurations for the nomination pools. The origin for this call must be
		/// Root.
		///
		/// # Arguments
		///
		/// * `min_join_bond` - Set [`MinJoinBond`].
		/// * `min_create_bond` - Set [`MinCreateBond`].
		/// * `max_pools` - Set [`MaxPools`].
		/// * `max_members` - Set [`MaxPoolMembers`].
		/// * `max_members_per_pool` - Set [`MaxPoolMembersPerPool`].
		/// * `global_max_commission` - Set [`GlobalMaxCommission`].
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::set_configs())]
		pub fn set_configs(
			origin: OriginFor<T>,
			min_join_bond: ConfigOp<BalanceOf<T>>,
			min_create_bond: ConfigOp<BalanceOf<T>>,
			max_pools: ConfigOp<u32>,
			max_members: ConfigOp<u32>,
			max_members_per_pool: ConfigOp<u32>,
			global_max_commission: ConfigOp<Perbill>,
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
			config_op_exp!(MaxPoolMembers::<T>, max_members);
			config_op_exp!(MaxPoolMembersPerPool::<T>, max_members_per_pool);
			config_op_exp!(GlobalMaxCommission::<T>, global_max_commission);
			Ok(())
		}

		/// Update the roles of the pool.
		///
		/// The root is the only entity that can change any of the roles, including itself,
		/// excluding the depositor, who can never change.
		///
		/// It emits an event, notifying UIs of the role change. This event is quite relevant to
		/// most pool members and they should be informed of changes to pool roles.
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::update_roles())]
		pub fn update_roles(
			origin: OriginFor<T>,
			pool_id: PoolId,
			new_root: ConfigOp<T::AccountId>,
			new_nominator: ConfigOp<T::AccountId>,
			new_bouncer: ConfigOp<T::AccountId>,
		) -> DispatchResult {
			let mut bonded_pool = match ensure_root(origin.clone()) {
				Ok(()) => BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?,
				Err(frame_support::error::BadOrigin) => {
					let who = ensure_signed(origin)?;
					let bonded_pool =
						BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
					ensure!(bonded_pool.can_update_roles(&who), Error::<T>::DoesNotHavePermission);
					bonded_pool
				},
			};

			match new_root {
				ConfigOp::Noop => (),
				ConfigOp::Remove => bonded_pool.roles.root = None,
				ConfigOp::Set(v) => bonded_pool.roles.root = Some(v),
			};
			match new_nominator {
				ConfigOp::Noop => (),
				ConfigOp::Remove => bonded_pool.roles.nominator = None,
				ConfigOp::Set(v) => bonded_pool.roles.nominator = Some(v),
			};
			match new_bouncer {
				ConfigOp::Noop => (),
				ConfigOp::Remove => bonded_pool.roles.bouncer = None,
				ConfigOp::Set(v) => bonded_pool.roles.bouncer = Some(v),
			};

			Self::deposit_event(Event::<T>::RolesUpdated {
				root: bonded_pool.roles.root.clone(),
				nominator: bonded_pool.roles.nominator.clone(),
				bouncer: bonded_pool.roles.bouncer.clone(),
			});

			bonded_pool.put();
			Ok(())
		}

		/// Chill on behalf of the pool.
		///
		/// The dispatch origin of this call must be signed by the pool nominator or the pool
		/// root role, same as [`Pallet::nominate`].
		///
		/// This directly forward the call to the staking pallet, on behalf of the pool bonded
		/// account.
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::chill())]
		pub fn chill(origin: OriginFor<T>, pool_id: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_nominate(&who), Error::<T>::NotNominator);
			T::Staking::chill(&bonded_pool.bonded_account())
		}

		/// `origin` bonds funds from `extra` for some pool member `member` into their respective
		/// pools.
		///
		/// `origin` can bond extra funds from free balance or pending rewards when `origin ==
		/// other`.
		///
		/// In the case of `origin != other`, `origin` can only bond extra pending rewards of
		/// `other` members assuming set_claim_permission for the given member is
		/// `PermissionlessAll` or `PermissionlessCompound`.
		#[pallet::call_index(14)]
		#[pallet::weight(
			T::WeightInfo::bond_extra_transfer()
			.max(T::WeightInfo::bond_extra_other())
		)]
		pub fn bond_extra_other(
			origin: OriginFor<T>,
			member: AccountIdLookupOf<T>,
			extra: BondExtra<BalanceOf<T>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_bond_extra(who, T::Lookup::lookup(member)?, extra)
		}

		/// Allows a pool member to set a claim permission to allow or disallow permissionless
		/// bonding and withdrawing.
		///
		/// By default, this is `Permissioned`, which implies only the pool member themselves can
		/// claim their pending rewards. If a pool member wishes so, they can set this to
		/// `PermissionlessAll` to allow any account to claim their rewards and bond extra to the
		/// pool.
		///
		/// # Arguments
		///
		/// * `origin` - Member of a pool.
		/// * `actor` - Account to claim reward. // improve this
		#[pallet::call_index(15)]
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn set_claim_permission(
			origin: OriginFor<T>,
			permission: ClaimPermission,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(PoolMembers::<T>::contains_key(&who), Error::<T>::PoolMemberNotFound);
			ClaimPermissions::<T>::mutate(who, |source| {
				*source = permission;
			});
			Ok(())
		}

		/// `origin` can claim payouts on some pool member `other`'s behalf.
		///
		/// Pool member `other` must have a `PermissionlessAll` or `PermissionlessWithdraw` in order
		/// for this call to be successful.
		#[pallet::call_index(16)]
		#[pallet::weight(T::WeightInfo::claim_payout())]
		pub fn claim_payout_other(origin: OriginFor<T>, other: T::AccountId) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			Self::do_claim_payout(signer, other)
		}

		/// Set the commission of a pool.
		//
		/// Both a commission percentage and a commission payee must be provided in the `current`
		/// tuple. Where a `current` of `None` is provided, any current commission will be removed.
		///
		/// - If a `None` is supplied to `new_commission`, existing commission will be removed.
		#[pallet::call_index(17)]
		#[pallet::weight(T::WeightInfo::set_commission())]
		pub fn set_commission(
			origin: OriginFor<T>,
			pool_id: PoolId,
			new_commission: Option<(Perbill, T::AccountId)>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_manage_commission(&who), Error::<T>::DoesNotHavePermission);

			let mut reward_pool = RewardPools::<T>::get(pool_id)
				.defensive_ok_or::<Error<T>>(DefensiveError::RewardPoolNotFound.into())?;
			// IMPORTANT: make sure that everything up to this point is using the current commission
			// before it updates. Note that `try_update_current` could still fail at this point.
			reward_pool.update_records(
				pool_id,
				bonded_pool.points,
				bonded_pool.commission.current(),
			)?;
			RewardPools::insert(pool_id, reward_pool);

			bonded_pool.commission.try_update_current(&new_commission)?;
			bonded_pool.put();
			Self::deposit_event(Event::<T>::PoolCommissionUpdated {
				pool_id,
				current: new_commission,
			});
			Ok(())
		}

		/// Set the maximum commission of a pool.
		///
		/// - Initial max can be set to any `Perbill`, and only smaller values thereafter.
		/// - Current commission will be lowered in the event it is higher than a new max
		///   commission.
		#[pallet::call_index(18)]
		#[pallet::weight(T::WeightInfo::set_commission_max())]
		pub fn set_commission_max(
			origin: OriginFor<T>,
			pool_id: PoolId,
			max_commission: Perbill,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_manage_commission(&who), Error::<T>::DoesNotHavePermission);

			bonded_pool.commission.try_update_max(pool_id, max_commission)?;
			bonded_pool.put();

			Self::deposit_event(Event::<T>::PoolMaxCommissionUpdated { pool_id, max_commission });
			Ok(())
		}

		/// Set the commission change rate for a pool.
		///
		/// Initial change rate is not bounded, whereas subsequent updates can only be more
		/// restrictive than the current.
		#[pallet::call_index(19)]
		#[pallet::weight(T::WeightInfo::set_commission_change_rate())]
		pub fn set_commission_change_rate(
			origin: OriginFor<T>,
			pool_id: PoolId,
			change_rate: CommissionChangeRate<BlockNumberFor<T>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
			ensure!(bonded_pool.can_manage_commission(&who), Error::<T>::DoesNotHavePermission);

			bonded_pool.commission.try_update_change_rate(change_rate)?;
			bonded_pool.put();

			Self::deposit_event(Event::<T>::PoolCommissionChangeRateUpdated {
				pool_id,
				change_rate,
			});
			Ok(())
		}

		/// Claim pending commission.
		///
		/// The dispatch origin of this call must be signed by the `root` role of the pool. Pending
		/// commission is paid out and added to total claimed commission`. Total pending commission
		/// is reset to zero. the current.
		#[pallet::call_index(20)]
		#[pallet::weight(T::WeightInfo::claim_commission())]
		pub fn claim_commission(origin: OriginFor<T>, pool_id: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_claim_commission(who, pool_id)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		#[cfg(feature = "try-runtime")]
		fn try_state(_n: BlockNumberFor<T>) -> Result<(), TryRuntimeError> {
			Self::do_try_state(u8::MAX)
		}

		fn integrity_test() {
			assert!(
				T::MaxPointsToBalance::get() > 0,
				"Minimum points to balance ratio must be greater than 0"
			);
			assert!(
				T::Staking::bonding_duration() < TotalUnbondingPools::<T>::get(),
				"There must be more unbonding pools then the bonding duration /
				so a slash can be applied to relevant unboding pools. (We assume /
				the bonding duration > slash deffer duration.",
			);
		}
	}
}

impl<T: Config> Pallet<T> {
	/// The amount of bond that MUST REMAIN IN BONDED in ALL POOLS.
	///
	/// It is the responsibility of the depositor to put these funds into the pool initially. Upon
	/// unbond, they can never unbond to a value below this amount.
	///
	/// It is essentially `max { MinNominatorBond, MinCreateBond, MinJoinBond }`, where the former
	/// is coming from the staking pallet and the latter two are configured in this pallet.
	pub fn depositor_min_bond() -> BalanceOf<T> {
		T::Staking::minimum_nominator_bond()
			.max(MinCreateBond::<T>::get())
			.max(MinJoinBond::<T>::get())
			.max(T::Currency::minimum_balance())
	}
	/// Remove everything related to the given bonded pool.
	///
	/// Metadata and all of the sub-pools are also deleted. All accounts are dusted and the leftover
	/// of the reward account is returned to the depositor.
	pub fn dissolve_pool(bonded_pool: BondedPool<T>) {
		let reward_account = bonded_pool.reward_account();
		let bonded_account = bonded_pool.bonded_account();

		ReversePoolIdLookup::<T>::remove(&bonded_account);
		RewardPools::<T>::remove(bonded_pool.id);
		SubPoolsStorage::<T>::remove(bonded_pool.id);

		// Kill accounts from storage by making their balance go below ED. We assume that the
		// accounts have no references that would prevent destruction once we get to this point. We
		// don't work with the system pallet directly, but
		// 1. we drain the reward account and kill it. This account should never have any extra
		// consumers anyway.
		// 2. the bonded account should become a 'killed stash' in the staking system, and all of
		//    its consumers removed.
		debug_assert_eq!(frame_system::Pallet::<T>::consumers(&reward_account), 0);
		debug_assert_eq!(frame_system::Pallet::<T>::consumers(&bonded_account), 0);
		debug_assert_eq!(
			T::Staking::total_stake(&bonded_account).unwrap_or_default(),
			Zero::zero()
		);

		// This shouldn't fail, but if it does we don't really care. Remaining balance can consist
		// of unclaimed pending commission, errorneous transfers to the reward account, etc.
		let reward_pool_remaining = T::Currency::free_balance(&reward_account);
		let _ = T::Currency::transfer(
			&reward_account,
			&bonded_pool.roles.depositor,
			reward_pool_remaining,
			ExistenceRequirement::AllowDeath,
		);

		// NOTE: this is purely defensive.
		T::Currency::make_free_balance_be(&reward_account, Zero::zero());
		T::Currency::make_free_balance_be(&bonded_pool.bonded_account(), Zero::zero());

		Self::deposit_event(Event::<T>::Destroyed { pool_id: bonded_pool.id });
		// Remove bonded pool metadata.
		Metadata::<T>::remove(bonded_pool.id);

		bonded_pool.remove();
	}

	/// Create the main, bonded account of a pool with the given id.
	pub fn create_bonded_account(id: PoolId) -> T::AccountId {
		T::PalletId::get().into_sub_account_truncating((AccountType::Bonded, id))
	}

	/// Create the reward account of a pool with the given id.
	pub fn create_reward_account(id: PoolId) -> T::AccountId {
		// NOTE: in order to have a distinction in the test account id type (u128), we put
		// account_type first so it does not get truncated out.
		T::PalletId::get().into_sub_account_truncating((AccountType::Reward, id))
	}

	/// Get the member with their associated bonded and reward pool.
	fn get_member_with_pools(
		who: &T::AccountId,
	) -> Result<(PoolMember<T>, BondedPool<T>, RewardPool<T>), Error<T>> {
		let member = PoolMembers::<T>::get(who).ok_or(Error::<T>::PoolMemberNotFound)?;
		let bonded_pool =
			BondedPool::<T>::get(member.pool_id).defensive_ok_or(DefensiveError::PoolNotFound)?;
		let reward_pool =
			RewardPools::<T>::get(member.pool_id).defensive_ok_or(DefensiveError::PoolNotFound)?;
		Ok((member, bonded_pool, reward_pool))
	}

	/// Persist the member with their associated bonded and reward pool into storage, consuming
	/// all of them.
	fn put_member_with_pools(
		member_account: &T::AccountId,
		member: PoolMember<T>,
		bonded_pool: BondedPool<T>,
		reward_pool: RewardPool<T>,
	) {
		bonded_pool.put();
		RewardPools::insert(member.pool_id, reward_pool);
		PoolMembers::<T>::insert(member_account, member);
	}

	/// Calculate the equivalent point of `new_funds` in a pool with `current_balance` and
	/// `current_points`.
	fn balance_to_point(
		current_balance: BalanceOf<T>,
		current_points: BalanceOf<T>,
		new_funds: BalanceOf<T>,
	) -> BalanceOf<T> {
		let u256 = T::BalanceToU256::convert;
		let balance = T::U256ToBalance::convert;
		match (current_balance.is_zero(), current_points.is_zero()) {
			(_, true) => new_funds.saturating_mul(POINTS_TO_BALANCE_INIT_RATIO.into()),
			(true, false) => {
				// The pool was totally slashed.
				// This is the equivalent of `(current_points / 1) * new_funds`.
				new_funds.saturating_mul(current_points)
			},
			(false, false) => {
				// Equivalent to (current_points / current_balance) * new_funds
				balance(
					u256(current_points)
						.saturating_mul(u256(new_funds))
						// We check for zero above
						.div(u256(current_balance)),
				)
			},
		}
	}

	/// Calculate the equivalent balance of `points` in a pool with `current_balance` and
	/// `current_points`.
	fn point_to_balance(
		current_balance: BalanceOf<T>,
		current_points: BalanceOf<T>,
		points: BalanceOf<T>,
	) -> BalanceOf<T> {
		let u256 = T::BalanceToU256::convert;
		let balance = T::U256ToBalance::convert;
		if current_balance.is_zero() || current_points.is_zero() || points.is_zero() {
			// There is nothing to unbond
			return Zero::zero()
		}

		// Equivalent of (current_balance / current_points) * points
		balance(u256(current_balance).saturating_mul(u256(points)))
			// We check for zero above
			.div(current_points)
	}

	/// If the member has some rewards, transfer a payout from the reward pool to the member.
	// Emits events and potentially modifies pool state if any arithmetic saturates, but does
	// not persist any of the mutable inputs to storage.
	fn do_reward_payout(
		member_account: &T::AccountId,
		member: &mut PoolMember<T>,
		bonded_pool: &mut BondedPool<T>,
		reward_pool: &mut RewardPool<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		debug_assert_eq!(member.pool_id, bonded_pool.id);

		// a member who has no skin in the game anymore cannot claim any rewards.
		ensure!(!member.active_points().is_zero(), Error::<T>::FullyUnbonding);

		let (current_reward_counter, _) = reward_pool.current_reward_counter(
			bonded_pool.id,
			bonded_pool.points,
			bonded_pool.commission.current(),
		)?;

		// Determine the pending rewards. In scenarios where commission is 100%, `pending_rewards`
		// will be zero.
		let pending_rewards = member.pending_rewards(current_reward_counter)?;
		if pending_rewards.is_zero() {
			return Ok(pending_rewards)
		}

		// IFF the reward is non-zero alter the member and reward pool info.
		member.last_recorded_reward_counter = current_reward_counter;
		reward_pool.register_claimed_reward(pending_rewards);

		T::Currency::transfer(
			&bonded_pool.reward_account(),
			member_account,
			pending_rewards,
			// defensive: the depositor has put existential deposit into the pool and it stays
			// untouched, reward account shall not die.
			ExistenceRequirement::KeepAlive,
		)?;

		Self::deposit_event(Event::<T>::PaidOut {
			member: member_account.clone(),
			pool_id: member.pool_id,
			payout: pending_rewards,
		});

		Ok(pending_rewards)
	}

	fn do_create(
		who: T::AccountId,
		amount: BalanceOf<T>,
		root: AccountIdLookupOf<T>,
		nominator: AccountIdLookupOf<T>,
		bouncer: AccountIdLookupOf<T>,
		pool_id: PoolId,
	) -> DispatchResult {
		let root = T::Lookup::lookup(root)?;
		let nominator = T::Lookup::lookup(nominator)?;
		let bouncer = T::Lookup::lookup(bouncer)?;

		ensure!(amount >= Pallet::<T>::depositor_min_bond(), Error::<T>::MinimumBondNotMet);
		ensure!(
			MaxPools::<T>::get().map_or(true, |max_pools| BondedPools::<T>::count() < max_pools),
			Error::<T>::MaxPools
		);
		ensure!(!PoolMembers::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);
		let mut bonded_pool = BondedPool::<T>::new(
			pool_id,
			PoolRoles {
				root: Some(root),
				nominator: Some(nominator),
				bouncer: Some(bouncer),
				depositor: who.clone(),
			},
		);

		bonded_pool.try_inc_members()?;
		let points = bonded_pool.try_bond_funds(&who, amount, BondType::Create)?;

		T::Currency::transfer(
			&who,
			&bonded_pool.reward_account(),
			T::Currency::minimum_balance(),
			ExistenceRequirement::AllowDeath,
		)?;

		PoolMembers::<T>::insert(
			who.clone(),
			PoolMember::<T> {
				pool_id,
				points,
				last_recorded_reward_counter: Zero::zero(),
				unbonding_eras: Default::default(),
			},
		);
		RewardPools::<T>::insert(
			pool_id,
			RewardPool::<T> {
				last_recorded_reward_counter: Zero::zero(),
				last_recorded_total_payouts: Zero::zero(),
				total_rewards_claimed: Zero::zero(),
				total_commission_pending: Zero::zero(),
				total_commission_claimed: Zero::zero(),
			},
		);
		ReversePoolIdLookup::<T>::insert(bonded_pool.bonded_account(), pool_id);

		Self::deposit_event(Event::<T>::Created { depositor: who.clone(), pool_id });

		Self::deposit_event(Event::<T>::Bonded {
			member: who,
			pool_id,
			bonded: amount,
			joined: true,
		});
		bonded_pool.put();

		Ok(())
	}

	fn do_bond_extra(
		signer: T::AccountId,
		who: T::AccountId,
		extra: BondExtra<BalanceOf<T>>,
	) -> DispatchResult {
		if signer != who {
			ensure!(
				ClaimPermissions::<T>::get(&who).can_bond_extra(),
				Error::<T>::DoesNotHavePermission
			);
			ensure!(extra == BondExtra::Rewards, Error::<T>::BondExtraRestricted);
		}

		let (mut member, mut bonded_pool, mut reward_pool) = Self::get_member_with_pools(&who)?;

		// payout related stuff: we must claim the payouts, and updated recorded payout data
		// before updating the bonded pool points, similar to that of `join` transaction.
		reward_pool.update_records(
			bonded_pool.id,
			bonded_pool.points,
			bonded_pool.commission.current(),
		)?;
		let claimed =
			Self::do_reward_payout(&who, &mut member, &mut bonded_pool, &mut reward_pool)?;

		let (points_issued, bonded) = match extra {
			BondExtra::FreeBalance(amount) =>
				(bonded_pool.try_bond_funds(&who, amount, BondType::Later)?, amount),
			BondExtra::Rewards =>
				(bonded_pool.try_bond_funds(&who, claimed, BondType::Later)?, claimed),
		};

		bonded_pool.ok_to_be_open()?;
		member.points =
			member.points.checked_add(&points_issued).ok_or(Error::<T>::OverflowRisk)?;

		Self::deposit_event(Event::<T>::Bonded {
			member: who.clone(),
			pool_id: member.pool_id,
			bonded,
			joined: false,
		});
		Self::put_member_with_pools(&who, member, bonded_pool, reward_pool);

		Ok(())
	}

	fn do_claim_commission(who: T::AccountId, pool_id: PoolId) -> DispatchResult {
		let bonded_pool = BondedPool::<T>::get(pool_id).ok_or(Error::<T>::PoolNotFound)?;
		ensure!(bonded_pool.can_manage_commission(&who), Error::<T>::DoesNotHavePermission);

		let mut reward_pool = RewardPools::<T>::get(pool_id)
			.defensive_ok_or::<Error<T>>(DefensiveError::RewardPoolNotFound.into())?;

		// IMPORTANT: make sure that any newly pending commission not yet processed is added to
		// `total_commission_pending`.
		reward_pool.update_records(
			pool_id,
			bonded_pool.points,
			bonded_pool.commission.current(),
		)?;

		let commission = reward_pool.total_commission_pending;
		ensure!(!commission.is_zero(), Error::<T>::NoPendingCommission);

		let payee = bonded_pool
			.commission
			.current
			.as_ref()
			.map(|(_, p)| p.clone())
			.ok_or(Error::<T>::NoCommissionCurrentSet)?;

		// Payout claimed commission.
		T::Currency::transfer(
			&bonded_pool.reward_account(),
			&payee,
			commission,
			ExistenceRequirement::KeepAlive,
		)?;

		// Add pending commission to total claimed counter.
		reward_pool.total_commission_claimed =
			reward_pool.total_commission_claimed.saturating_add(commission);
		// Reset total pending commission counter to zero.
		reward_pool.total_commission_pending = Zero::zero();
		// Commit reward pool updates
		RewardPools::<T>::insert(pool_id, reward_pool);

		Self::deposit_event(Event::<T>::PoolCommissionClaimed { pool_id, commission });
		Ok(())
	}

	fn do_claim_payout(signer: T::AccountId, who: T::AccountId) -> DispatchResult {
		if signer != who {
			ensure!(
				ClaimPermissions::<T>::get(&who).can_claim_payout(),
				Error::<T>::DoesNotHavePermission
			);
		}
		let (mut member, mut bonded_pool, mut reward_pool) = Self::get_member_with_pools(&who)?;

		let _ = Self::do_reward_payout(&who, &mut member, &mut bonded_pool, &mut reward_pool)?;

		Self::put_member_with_pools(&who, member, bonded_pool, reward_pool);
		Ok(())
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
	/// Then, considering members as well:
	///
	/// * each `BondedPool.member_counter` must be:
	///   - correct (compared to actual count of member who have `.pool_id` this pool)
	///   - less than `MaxPoolMembersPerPool`.
	/// * each `member.pool_id` must correspond to an existing `BondedPool.id` (which implies the
	///   existence of the reward pool as well).
	/// * count of all members must be less than `MaxPoolMembers`.
	///
	/// Then, considering unbonding members:
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
	/// `try_state(255)` is the strongest sanity check, and `0` performs no checks.
	#[cfg(any(feature = "try-runtime", feature = "fuzzing", test, debug_assertions))]
	pub fn do_try_state(level: u8) -> Result<(), TryRuntimeError> {
		if level.is_zero() {
			return Ok(())
		}
		// note: while a bit wacky, since they have the same key, even collecting to vec should
		// result in the same set of keys, in the same order.
		let bonded_pools = BondedPools::<T>::iter_keys().collect::<Vec<_>>();
		let reward_pools = RewardPools::<T>::iter_keys().collect::<Vec<_>>();
		ensure!(
			bonded_pools == reward_pools,
			"`BondedPools` and `RewardPools` must all have the EXACT SAME key-set."
		);

		ensure!(
			SubPoolsStorage::<T>::iter_keys().all(|k| bonded_pools.contains(&k)),
			"`SubPoolsStorage` must be a subset of the above superset."
		);
		ensure!(
			Metadata::<T>::iter_keys().all(|k| bonded_pools.contains(&k)),
			"`Metadata` keys must be a subset of the above superset."
		);

		ensure!(
			MaxPools::<T>::get().map_or(true, |max| bonded_pools.len() <= (max as usize)),
			Error::<T>::MaxPools
		);

		for id in reward_pools {
			let account = Self::create_reward_account(id);
			if T::Currency::free_balance(&account) < T::Currency::minimum_balance() {
				log!(
					warn,
					"reward pool of {:?}: {:?} (ed = {:?}), should only happen because ED has \
					changed recently. Pool operators should be notified to top up the reward \
					account",
					id,
					T::Currency::free_balance(&account),
					T::Currency::minimum_balance(),
				)
			}
		}

		let mut pools_members = BTreeMap::<PoolId, u32>::new();
		let mut pools_members_pending_rewards = BTreeMap::<PoolId, BalanceOf<T>>::new();
		let mut all_members = 0u32;
		PoolMembers::<T>::iter().try_for_each(|(_, d)| -> Result<(), TryRuntimeError> {
			let bonded_pool = BondedPools::<T>::get(d.pool_id).unwrap();
			ensure!(!d.total_points().is_zero(), "No member should have zero points");
			*pools_members.entry(d.pool_id).or_default() += 1;
			all_members += 1;

			let reward_pool = RewardPools::<T>::get(d.pool_id).unwrap();
			if !bonded_pool.points.is_zero() {
				let commission = bonded_pool.commission.current();
				let (current_rc, _) = reward_pool
					.current_reward_counter(d.pool_id, bonded_pool.points, commission)
					.unwrap();
				let pending_rewards = d.pending_rewards(current_rc).unwrap();
				*pools_members_pending_rewards.entry(d.pool_id).or_default() += pending_rewards;
			} // else this pool has been heavily slashed and cannot have any rewards anymore.

			Ok(())
		})?;

		RewardPools::<T>::iter_keys().try_for_each(|id| -> Result<(), TryRuntimeError> {
			// the sum of the pending rewards must be less than the leftover balance. Since the
			// reward math rounds down, we might accumulate some dust here.
			let pending_rewards_lt_leftover_bal = RewardPool::<T>::current_balance(id) >=
				pools_members_pending_rewards.get(&id).copied().unwrap_or_default();
			if !pending_rewards_lt_leftover_bal {
				log::warn!(
					"pool {:?}, sum pending rewards = {:?}, remaining balance = {:?}",
					id,
					pools_members_pending_rewards.get(&id),
					RewardPool::<T>::current_balance(id)
				);
			}
			ensure!(
				pending_rewards_lt_leftover_bal,
				"The sum of the pending rewards must be less than the leftover balance."
			);
			Ok(())
		})?;

		BondedPools::<T>::iter().try_for_each(|(id, inner)| -> Result<(), TryRuntimeError> {
			let bonded_pool = BondedPool { id, inner };
			ensure!(
				pools_members.get(&id).copied().unwrap_or_default() ==
				bonded_pool.member_counter,
				"Each `BondedPool.member_counter` must be equal to the actual count of members of this pool"
			);
			ensure!(
				MaxPoolMembersPerPool::<T>::get()
					.map_or(true, |max| bonded_pool.member_counter <= max),
				Error::<T>::MaxPoolMembers
			);

			let depositor = PoolMembers::<T>::get(&bonded_pool.roles.depositor).unwrap();
			ensure!(
				bonded_pool.is_destroying_and_only_depositor(depositor.active_points()) ||
					depositor.active_points() >= MinCreateBond::<T>::get(),
				"depositor must always have MinCreateBond stake in the pool, except for when the \
				pool is being destroyed and the depositor is the last member",
			);
			Ok(())
		})?;
		ensure!(
			MaxPoolMembers::<T>::get().map_or(true, |max| all_members <= max),
			Error::<T>::MaxPoolMembers
		);

		if level <= 1 {
			return Ok(())
		}

		for (pool_id, _pool) in BondedPools::<T>::iter() {
			let pool_account = Pallet::<T>::create_bonded_account(pool_id);
			let subs = SubPoolsStorage::<T>::get(pool_id).unwrap_or_default();

			let sum_unbonding_balance = subs.sum_unbonding_balance();
			let bonded_balance = T::Staking::active_stake(&pool_account).unwrap_or_default();
			let total_balance = T::Currency::total_balance(&pool_account);

			assert!(
				total_balance >= bonded_balance + sum_unbonding_balance,
				"faulty pool: {:?} / {:?}, total_balance {:?} >= bonded_balance {:?} + sum_unbonding_balance {:?}",
				pool_id,
				_pool,
				total_balance,
				bonded_balance,
				sum_unbonding_balance
			);
		}

		Ok(())
	}

	/// Fully unbond the shares of `member`, when executed from `origin`.
	///
	/// This is useful for backwards compatibility with the majority of tests that only deal with
	/// full unbonding, not partial unbonding.
	#[cfg(any(feature = "runtime-benchmarks", test))]
	pub fn fully_unbond(
		origin: frame_system::pallet_prelude::OriginFor<T>,
		member: T::AccountId,
	) -> DispatchResult {
		let points = PoolMembers::<T>::get(&member).map(|d| d.active_points()).unwrap_or_default();
		let member_lookup = T::Lookup::unlookup(member);
		Self::unbond(origin, member_lookup, points)
	}
}

impl<T: Config> Pallet<T> {
	/// Returns the pending rewards for the specified `who` account.
	///
	/// In the case of error, `None` is returned. Used by runtime API.
	pub fn api_pending_rewards(who: T::AccountId) -> Option<BalanceOf<T>> {
		if let Some(pool_member) = PoolMembers::<T>::get(who) {
			if let Some((reward_pool, bonded_pool)) = RewardPools::<T>::get(pool_member.pool_id)
				.zip(BondedPools::<T>::get(pool_member.pool_id))
			{
				let commission = bonded_pool.commission.current();
				let (current_reward_counter, _) = reward_pool
					.current_reward_counter(pool_member.pool_id, bonded_pool.points, commission)
					.ok()?;
				return pool_member.pending_rewards(current_reward_counter).ok()
			}
		}

		None
	}

	/// Returns the points to balance conversion for a specified pool.
	///
	/// If the pool ID does not exist, it returns 0 ratio points to balance. Used by runtime API.
	pub fn api_points_to_balance(pool_id: PoolId, points: BalanceOf<T>) -> BalanceOf<T> {
		if let Some(pool) = BondedPool::<T>::get(pool_id) {
			pool.points_to_balance(points)
		} else {
			Zero::zero()
		}
	}

	/// Returns the equivalent `new_funds` balance to point conversion for a specified pool.
	///
	/// If the pool ID does not exist, returns 0 ratio balance to points. Used by runtime API.
	pub fn api_balance_to_points(pool_id: PoolId, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		if let Some(pool) = BondedPool::<T>::get(pool_id) {
			let bonded_balance =
				T::Staking::active_stake(&pool.bonded_account()).unwrap_or(Zero::zero());
			Pallet::<T>::balance_to_point(bonded_balance, pool.points, new_funds)
		} else {
			Zero::zero()
		}
	}
}

impl<T: Config> sp_staking::OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_slash(
		pool_account: &T::AccountId,
		// Bonded balance is always read directly from staking, therefore we don't need to update
		// anything here.
		slashed_bonded: BalanceOf<T>,
		slashed_unlocking: &BTreeMap<EraIndex, BalanceOf<T>>,
	) {
		if let Some(pool_id) = ReversePoolIdLookup::<T>::get(pool_account) {
			let mut sub_pools = match SubPoolsStorage::<T>::get(pool_id).defensive() {
				Some(sub_pools) => sub_pools,
				None => return,
			};
			for (era, slashed_balance) in slashed_unlocking.iter() {
				if let Some(pool) = sub_pools.with_era.get_mut(era) {
					pool.balance = *slashed_balance;
					Self::deposit_event(Event::<T>::UnbondingPoolSlashed {
						era: *era,
						pool_id,
						balance: *slashed_balance,
					});
				}
			}

			Self::deposit_event(Event::<T>::PoolSlashed { pool_id, balance: slashed_bonded });
			SubPoolsStorage::<T>::insert(pool_id, sub_pools);
		}
	}
}
