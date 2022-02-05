//! # Delegation pools for nominating
//!
//! This pallet allows delegators to delegate their stake to nominating pools, each of which acts as
//! a nominator and nominates validators on their behalf.
//!
//! ## Design
//!
//! _Notes_: this section uses pseudo code to explain general design and does not necessarily
//! reflect the exact implementation. Additionally, a strong knowledge of `pallet-staking`'s api is
//! assumed.
//!
//! The delegation pool abstraction is composed of:
//!
//!  * bonded pool: Tracks the distribution of actively staked funds. See [`BondedPool`] and
//! [`BondedPools`]
//! * reward pool: Tracks rewards earned by actively staked funds. See [`RewardPool`] and
//!   [`RewardPools`].
//! * unbonding sub pools: This a collection of pools at different phases of the unbonding
//!   lifecycle. See [`SubPools`] and [`SubPoolsStorage`].
//! * delegators: Accounts that are members of pools. See [`Delegator`] and [`Delegators`].
//!
//! In order to maintain scalability, all operations are independent of the number of delegators. To
//! do this, we store delegation specific information local to the delegator while the pool data
//! structures have bounded datum .
//!
//! ### Design goals
//!
//! * Maintain integrity of slashing events, sufficiently penalizing delegators that where in the
//!   pool while it was backing a validator that got slashed.
//! * Maximize scalability in terms of delegator count.
//!
//! ### Bonded pool
//!
//! A bonded pool nominates with its total balance, excluding that which has been withdrawn for
//! unbonding. The total points of a bonded pool are always equal to the sum of points of the
//! delegation members. A bonded pool tracks its points and reads its bonded balance.
//!
//! When a delegator joins a pool, `amount_transferred` is transferred from the delegators account
//! to the bonded pools account. Then the pool calls `bond_extra(amount_transferred)` and issues new
//! points which are tracked by the delegator and added to the bonded pools points.
//!
//! When the pool already has some balance, we want the value of a point before the transfer to
//! equal the value of a point after the transfer. So, when a delegator joins a bonded pool with a
//! given `amount_transferred`, we maintain the ratio of bonded balance to points such that:
//!
//! ```
//! balance_after_transfer / points_after_transfer == balance_before_transfer / points_before_transfer;
//! ```
//!
//! To achieve this, we issue points based on the following:
//!
//! ```
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
//!     * We first compute `current_total_earnings` (`current_balance` is the free balance of the
//!       reward pool at the beginning of these operations.) ``` current_total_earnings =
//!       current_balance - reward_pool.balance + pool.total_earnings; ```
//!     * Then we compute the `current_points`. Every balance unit that was added to the reward pool
//!       since last time recorded means that we increase the `pool.points` by
//!       `bonding_pool.total_points`. In other words, for every unit of balance that has been
//!       earned by the reward pool, we inflate the reward pool points by `bonded_pool.points`. In
//!       effect this allows each, single unit of balance (e.g. planck) to be divvied up pro-rata
//!       among delegators based on points. ``` new_earnings = current_total_earnings -
//!       reward_pool.total_earnings; current_points = reward_pool.points + bonding_pool.points *
//!       new_earnings; ```
//!     * Finally, we compute `delegator_virtual_points`: the product of the delegator's points in
//!       the bonding pool and the total inflow of balance units since the last time the delegator
//!       claimed rewards ``` new_earnings_since_last_claim = current_total_earnings -
//!       delegator.reward_pool_total_earnings; delegator_virtual_points = delegator.points *
//!       new_earnings_since_last_claim; ```
//! 2) Compute the `delegator_payout`:
//!     ```
//!     delegator_pool_point_ratio = delegator_virtual_points / current_points;
//!     delegator_payout = current_balance * delegator_pool_point_ratio;
//!     ```
//! 3) Transfer `delegator_payout` to the delegator
//! 4) For the delegator set:
//!     ```
//!     delegator.reward_pool_total_earnings = current_total_earnings;
//!     ```
//! 5) For the pool set:
//!     ```
//!     reward_pool.points = current_points - delegator_virtual_points;
//!     reward_pool.balance = current_balance - delegator_payout;
//!     reward_pool.total_earnings = current_total_earnings;
//!     ```
//!
//! _Note_: One short coming of this design is that new joiners can claim rewards for the era after
//! they join in even though their funds did not contribute to the pools vote weight. When a
//! delegator joins, they set the field `reward_pool_total_earnings` equal to the `total_earnings`
//! of the reward pool at that point in time. At best the reward pool has the rewards up through the
//! previous era. If the delegator joins prior to the election snapshot they will benefit from the
//! rewards for the current era despite not contributing to the pool's vote weight. If they join
//! after the election snapshot is taken they will benefit from the rewards of the next _2_ eras
//! because their vote weight will not be counted until the election snapshot in current era + 1.
//!
//! **Relevant extrinsics:**
//!
//! * [`Call::claim_payout`]
//!
//! ### Unbonding sub pools
//!
//! When a delegator unbonds, their balance is unbonded in the bonded pool's account and tracked in
//! an unbonding pool associated with the active era. If no such pool exists, one is created. To
//! track which unbonding sub pool a delegator belongs too, the delegator tracks their
//! `unbonding_era`.
//!
//! When a delegator initiates unbonding we calculate their claim on the bonded pool
//! (`balance_to_unbond`) as:
//!
//! ```
//! balance_to_unbond = (bonded_pool.balance / bonded_pool.points) * delegator.points;
//! ```
//! If this is the first transfer into the unbonding pool we can issue an arbitrary amount of points
//! per balance. In this implementation we initialize unbonding pools with a 1 point to 1 balance
//! ratio (see [`POINTS_TO_BALANCE_INIT_RATIO`]). Otherwise, the unbonding pools hold the same
//! points to balance ratio properties as the bonded pool, so we issue the delegator points in the
//! unbonding pool based on
//!
//! ```
//! new_points_issued = (points_before_transfer / balance_before_transfer) * balance_to_unbond;
//! ```
//!
//! For scalability, we maintain a bound on the number of unbonding sub pools (see [`MaxUnboning`]).
//! Once we reach this bound the oldest unbonding pool is merged into the new unbonded pool (see
//! `no_era` field in [`SubPools`]). In other words, a unbonding pool is removed once its older than
//! `current_era - MaxUnbonding`. We merge an unbonding pool into the unbonded pool with
//!
//! ```
//! unbounded_pool.balance = unbounded_pool.balance + unbonding_pool.balance;
//! unbounded_pool.points = unbounded_pool.points + unbonding_pool.points;
//! ```
//!
//! This scheme "averages" out the points value in the unbonded pool.
//!
//! Once the delgators `unbonding_era` is older than `current_era -
//! [sp_staking::StakingInterface::bonding_duration]`, they can can cash their points out of the
//! corresponding unbonding pool. If their `unbonding_era` is older than the oldest unbonding pool
//! they cash their points out of the unbonded pool.
//!
//! **Relevant extrinsics
//!
//! * [`Call::unbond`]
//! * [`Call::with_unbonded`]
//!
//! ### Slashing
//!
//! We distribute slashes evenly across the bonded pool and the unbonding pools from slash era+1
//! through the slash apply era.
//!
//! To compute and execute the slashes:
//!
//! 1) Sum up the balances of the bonded pool and the unbonding pools in range `slash_era +
//! 1..=apply_era` and store that in `total_balance_affected`. 2) Compute `slash_ratio` as
//! `slash_amount / total_balance_affected`. 3) Compute `bonded_pool_balance_after_slash` as `(1-
//! slash_ratio) * bonded_pool_balance`. 4) For all `unbonding_pool` in range `slash_era +
//! 1..=apply_era` set their balance to `(1 - slash_ratio) * unbonding_pool_balance`.
//!
//! We need to slash the relevant unbonding pools to ensure all nominators whom where in the pool
//! while it was backing a validator that equivocated are punished. Without these measures a
//! nominator could unbond right after a validator equivocated with no consequences.
//!
//! This strategy is unfair to delegators who joined after the slash, because they get slashed as
//! well, but spares delegators who unbond. The latter is much more important for security: if a
//! pool's validators are attacking the network, we want their delegators to unbond fast! Avoiding
//! slashes gives them an incentive to do that if validators get repeatedly slashed.
//!
//! To be fair to joiners, we would also need joining pools, which are actively staking, in addition
//! to the unbonding pools. For maintenance simplicity these are not implemented.
//!
//! ### Limitations
//!
//! * Delegators cannot vote with their staked funds because they are transferred into the pools
//!   account. In the future this can be overcome by allowing the delegators to vote with their
//!   bonded funds via vote splitting.
//! * Delegators cannot quickly transfer to another pool if they do no like nominations, instead
//!   they must wait for the unbonding duration.
//!
//! # Pool creation and upkeep
//!
//! TBD - possible options:
//! * Pools can be created by anyone but nominations can never be updated
//! * Pools can be created by anyone and the creator can update the validators
//! * Pools are created by governance and governance can update the validators
//! ... Other ideas
//! * pools can have different roles assigned: creator (puts deposit down, cannot remove deposit
//!   until pool is empty), admin (can control who is nominator, destroyer and can do
//!   nominate/destroy), nominator (can adjust nominators), destroyer (can initiate destroy), etc
//!
//! # Runtime builder warnings
//!
//! * watch out for overflow of [`RewardPoints`] and [`BalanceOf`] types. Consider things like the
//!   chains total issuance, staking reward rate, and burn rate.
// Invariants
// - A `delegator.pool` must always be a valid entry in `RewardPools`, and `BondedPoolPoints`.
// - Every entry in `BondedPoolPoints` must have  a corresponding entry in `RewardPools`

#![cfg_attr(not(feature = "std"), no_std)]

// TODO:
// - make withdraw unbonded pool that just calls withdraw unbonded for the underlying pool account -
//   and remove withdraw unbonded call from unbond
// - creation
//    - CreateOrigin: the type of origin that can create a pool - can be set with governance call
//    - creator: account that cannont unbond until there are no other pool members (essentially
//      deposit)
//    - kicker: can kick (force unbond) delegators and block new delegators
//    - nominator: can set nominations
//    - admin: can change kicker, nominator, and make another account admin.
// - checks for number of pools when creating pools (param for max pools, pool creation origin)
// - post checks that rewardpool::count == bondedpool::count. delegators >= bondedpool::count,
//   subpools::count <= bondedpools

use frame_support::{
	ensure,
	pallet_prelude::*,
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{Currency, DefensiveResult, ExistenceRequirement, Get},
	DefaultNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_core::U256;
use sp_runtime::traits::{Bounded, Convert, Saturating, StaticLookup, TrailingZeroInput, Zero};
use sp_staking::{EraIndex, PoolsInterface, SlashPoolArgs, SlashPoolOut, StakingInterface};
use sp_std::{collections::btree_map::BTreeMap, ops::Div};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub use pallet::*;
pub(crate) const LOG_TARGET: &'static str = "runtime::pools";

// Syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: LOG_TARGET,
			concat!("[{:?}] 💰", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
		)
	};
}

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type SubPoolsWithEra<T> = BoundedBTreeMap<EraIndex, UnbondPool<T>, MaxUnbonding<T>>;
// NOTE: this assumes the balance type u128 or smaller.
type RewardPoints = U256;

const POINTS_TO_BALANCE_INIT_RATIO: u32 = 1;

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
	pool: T::AccountId,
	/// The quantity of points this delegator has in the bonded pool or in a sub pool if
	/// `Self::unbonding_era` is some.
	points: BalanceOf<T>,
	/// The reward pools total earnings _ever_ the last time this delegator claimed a payout.
	/// Assuming no massive burning events, we expect this value to always be below total issuance.
	/// This value lines up with the `RewardPool::total_earnings` after a delegator claims a
	/// payout.
	reward_pool_total_earnings: BalanceOf<T>,
	/// The era this delegator started unbonding at.
	unbonding_era: Option<EraIndex>,
}

#[derive(RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
// #[codec(mel_bound(T: Config))]
// #[scale_info(skip_type_params(T))]
pub struct BondedPool<T: Config> {
	points: BalanceOf<T>,
	account: T::AccountId,
}

impl<T: Config> BondedPool<T> {
	/// Get [`Self`] from storage. Returns `None` if no entry for `pool_account` exists.
	pub fn get(pool_account: &T::AccountId) -> Option<Self> {
		BondedPoolPoints::<T>::try_get(pool_account)
			.ok()
			.map(|points| Self { points, account: pool_account.clone() })
	}

	/// Insert [`Self`] into storage.
	pub fn insert(Self { account, points }: Self) {
		BondedPoolPoints::<T>::insert(account, points);
	}

	/// Get the amount of points to issue for some new funds that will be bonded in the pool.
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());
		points_to_issue::<T>(bonded_balance, self.points, new_funds)
	}

	// Get the amount of balance to unbond from the pool based on a delegator's points of the pool.
	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account).unwrap_or(Zero::zero());
		balance_to_unbond::<T>(bonded_balance, self.points, delegator_points)
	}

	// Check that the pool can accept a member with `new_funds`.
	fn ok_to_join_with(&self, new_funds: BalanceOf<T>) -> Result<(), DispatchError> {
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
			new_funds.saturating_add(bonded_balance) <
				BalanceOf::<T>::max_value().div(10u32.into()),
			Error::<T>::OverflowRisk
		);
		// then we can be decently confident the bonding pool points will not overflow
		// `BalanceOf<T>`.
		Ok(())
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
	/// The reward destination for the pool.
	account: T::AccountId,
	/// The balance of this reward pool after the last claimed payout.
	balance: BalanceOf<T>,
	/// The total earnings _ever_ of this reward pool after the last claimed payout. I.E. the sum
	/// of all incoming balance through the pools life.
	///
	/// NOTE: We assume this will always be less than total issuance and thus can use the runtimes
	/// `Balance` type. However in a chain with a burn rate higher than the rate this increases,
	/// this type should be bigger than `Balance`.
	total_earnings: BalanceOf<T>,
	/// The total points of this reward pool after the last claimed payout.
	points: RewardPoints,
}

impl<T: Config> RewardPool<T> {
	fn update_total_earnings_and_balance(mut self) -> Self {
		let current_balance = T::Currency::free_balance(&self.account);
		// The earnings since the last time it was updated
		let new_earnings = current_balance.saturating_sub(self.balance);
		// The lifetime earnings of the of the reward pool
		self.total_earnings = new_earnings.saturating_add(self.total_earnings);
		self.balance = current_balance;

		self
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
struct UnbondPool<T: Config> {
	points: BalanceOf<T>,
	balance: BalanceOf<T>,
}

impl<T: Config> UnbondPool<T> {
	#[cfg(test)]
	fn new(points: BalanceOf<T>, balance: BalanceOf<T>) -> Self {
		Self { points, balance }
	}
}

impl<T: Config> UnbondPool<T> {
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		points_to_issue::<T>(self.balance, self.points, new_funds)
	}

	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		balance_to_unbond::<T>(self.balance, self.points, delegator_points)
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
struct SubPools<T: Config> {
	/// A general, era agnostic pool of funds that have fully unbonded. The pools
	/// of `self.with_era` will lazily be merged into into this pool if they are
	/// older then `current_era - MaxUnbonding`.
	no_era: UnbondPool<T>,
	/// Map of era => unbond pools.
	with_era: SubPoolsWithEra<T>,
}

impl<T: Config> SubPools<T> {
	/// Merge the oldest unbonding pool with an era into the general unbond pool with no associated
	/// era.
	fn maybe_merge_pools(mut self, current_era: EraIndex) -> Self {
		if current_era < MaxUnbonding::<T>::get().into() {
			// For the first `0..MaxUnbonding` eras of the chain we don't need to do anything.
			// I.E. if `MaxUnbonding` is 5 and we are in era 4 we can add a pool for this era and
			// have exactly `MaxUnbonding` pools.
			return self
		}

		//  I.E. if `MaxUnbonding` is 5 and current era is 10, we only want to retain pools 6..=10.
		let newest_era_to_remove = current_era.saturating_sub(MaxUnbonding::<T>::get());

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
/// `no_era	 pool. This is guaranteed to at least be equal to the staking `UnbondingDuration`. For
/// improved UX [`Config::WithEraWithdrawWindow`] should be configured to a non-zero value.
struct MaxUnbonding<T: Config>(PhantomData<T>);
impl<T: Config> Get<u32> for MaxUnbonding<T> {
	fn get() -> u32 {
		// TODO: This may be too dangerous in the scenario bonding_duration gets decreased because
		// we would no longer be able to decode `SubPoolsWithEra`, which uses `MaxUnbonding` as the
		// bound
		T::StakingInterface::bonding_duration() + T::WithEraWithdrawWindow::get()
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
		// type WeightInfo: weights::WeightInfo;

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
		type WithEraWithdrawWindow: Get<u32>;
	}

	/// Active delegators.
	#[pallet::storage]
	pub(crate) type Delegators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator<T>>;

	/// Points for the bonded pools. Keyed by the pool's _Stash_/_Controller_. To get or insert a
	/// pool see [`BondedPool::get`] and [`BondedPool::insert`]
	#[pallet::storage]
	pub(crate) type BondedPoolPoints<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, BalanceOf<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool. Keyed by the bonded pools
	/// _Stash_/_Controller_.
	#[pallet::storage]
	pub(crate) type RewardPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a bonded pool,
	/// hence the name sub-pools. Keyed by the bonded pools _Stash_/_Controller_.
	#[pallet::storage]
	pub(crate) type SubPoolsStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, SubPools<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		Joined { delegator: T::AccountId, pool: T::AccountId, bonded: BalanceOf<T> },
		PaidOut { delegator: T::AccountId, pool: T::AccountId, payout: BalanceOf<T> },
		Unbonded { delegator: T::AccountId, pool: T::AccountId, amount: BalanceOf<T> },
		Withdrawn { delegator: T::AccountId, pool: T::AccountId, amount: BalanceOf<T> },
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
		/// Unbonded funds cannot be withdrawn yet because the bond duration has not passed.
		NotUnbondedYet,
		/// The amount does not meet the minimum bond to start nominating.
		MinimumBondNotMet,
		/// The transaction could not be executed due to overflow risk for the pool.
		OverflowRisk,
		/// An error from the staking pallet.
		StakingError,
		// Likely only an error ever encountered in poorly built tests.
		/// A pool with the generated account id already exists.
		IdInUse,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Join a pre-existing pool.
		///
		/// Notes
		/// * an account can only be a member of a single pool.
		/// * this will *not* dust the delegator account, so the delegator must have at least
		///   `existential deposit + amount` in their account.
		#[pallet::weight(666)]
		#[frame_support::transactional]
		pub fn join(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
			pool_account: T::AccountId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// If a delegator already exists that means they already belong to a pool
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			let mut bonded_pool =
				BondedPool::<T>::get(&pool_account).ok_or(Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_join_with(amount)?;

			// We don't actually care about writing the reward pool, we just need its
			// total earnings at this point in time.
			let reward_pool = RewardPools::<T>::get(&pool_account)
				.ok_or(Error::<T>::RewardPoolNotFound)?
				// This is important because we want the most up-to-date total earnings.
				.update_total_earnings_and_balance();

			let old_free_balance = T::Currency::free_balance(&pool_account);
			// Transfer the funds to be bonded from `who` to the pools account so the pool can then
			// go bond them.
			T::Currency::transfer(&who, &pool_account, amount, ExistenceRequirement::KeepAlive)?;

			// Try not to bail after the above transfer

			// This should now include the transferred balance.
			let new_free_balance = T::Currency::free_balance(&pool_account);
			// Get the exact amount we can bond extra.
			let exact_amount_to_bond = new_free_balance.saturating_sub(old_free_balance);
			// We must calculate the points to issue *before* we bond `who`'s funds, else the
			// points:balance ratio will be wrong.
			let new_points = bonded_pool.points_to_issue(exact_amount_to_bond);
			bonded_pool.points = bonded_pool.points.saturating_add(new_points);

			// The pool should always be created in such a way its in a state to bond extra, but if
			// the active balance is slashed below the minimum bonded or the account cannot be
			// found, we exit early.
			T::StakingInterface::bond_extra(pool_account.clone(), exact_amount_to_bond)?;

			Delegators::insert(
				who.clone(),
				Delegator::<T> {
					pool: pool_account.clone(),
					points: new_points,
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
			BondedPool::insert(bonded_pool);

			Self::deposit_event(Event::<T>::Joined {
				delegator: who,
				pool: pool_account,
				bonded: exact_amount_to_bond,
			});

			Ok(())
		}

		/// A bonded delegator can use this to claim their payout based on the rewards that the pool
		/// has accumulated since their last claimed payout (OR since joining if this is there first
		/// time claiming rewards).
		///
		/// Note that the payout will go to the delegator's account.
		#[pallet::weight(666)]
		pub fn claim_payout(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let bonded_pool = BondedPool::<T>::get(&delegator.pool).ok_or_else(|| {
				log!(error, "A bonded pool could not be found, this is a system logic error.");
				Error::<T>::PoolNotFound
			})?;

			Self::do_reward_payout(who, delegator, &bonded_pool)?;

			Ok(())
		}

		/// A bonded delegator can use this to unbond _all_ funds from the pool.
		/// In order to withdraw the funds, the delegator must wait
		#[pallet::weight(666)]
		pub fn unbond(origin: OriginFor<T>, num_slashing_spans: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			// let mut bonded_pool =
			// 	BondedPools::<T>::get(&delegator.pool).ok_or(Error::<T>::PoolNotFound)?;
			let mut bonded_pool =
				BondedPool::<T>::get(&delegator.pool).ok_or(Error::<T>::PoolNotFound)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points
			// no longer exist in the bonded pool and thus they can no longer claim their payouts.
			// It is not strictly necessary to claim the rewards, but we do it here for UX.
			Self::do_reward_payout(who.clone(), delegator, &bonded_pool)?;

			// Re-fetch the delegator because they where updated by `do_reward_payout`.
			let mut delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			// Note that we lazily create the unbonding pools here if they don't already exist
			let sub_pools = SubPoolsStorage::<T>::get(&delegator.pool).unwrap_or_default();
			let current_era = T::StakingInterface::current_era().unwrap_or(Zero::zero());

			let balance_to_unbond = bonded_pool.balance_to_unbond(delegator.points);

			// Update the bonded pool. Note that we must do this *after* calculating the balance
			// to unbond so we have the correct points for the balance:share ratio.
			bonded_pool.points = bonded_pool.points.saturating_sub(delegator.points);

			// Call withdraw unbonded to minimize unlocking chunks. If this is not done then we
			// would have to rely on delegators calling `withdraw_unbonded` in order to clear
			// unlocking chunks. This is a catch 22 for delegators who have not yet unbonded
			// because the pool needs to call `withdraw_unbonded` so they can `unbond`, but they
			// must call `unbond` prior to being able to call `withdraw_unbonded`.
			T::StakingInterface::withdraw_unbonded(delegator.pool.clone(), num_slashing_spans)?;
			// Unbond in the actual underlying pool
			T::StakingInterface::unbond(delegator.pool.clone(), balance_to_unbond)?;

			// Merge any older pools into the general, era agnostic unbond pool. Note that we do
			// this before inserting to ensure we don't go over the max unbonding pools.
			let mut sub_pools = sub_pools.maybe_merge_pools(current_era);

			// Update the unbond pool associated with the current era with the
			// unbonded funds. Note that we lazily create the unbond pool if it
			// does not yet exist.
			{
				let mut unbond_pool = sub_pools.unchecked_with_era_get_or_make(current_era);
				let points_to_issue = unbond_pool.points_to_issue(balance_to_unbond);
				unbond_pool.points = unbond_pool.points.saturating_add(points_to_issue);
				unbond_pool.balance = unbond_pool.balance.saturating_add(balance_to_unbond);
			}

			delegator.unbonding_era = Some(current_era);

			Self::deposit_event(Event::<T>::Unbonded {
				delegator: who.clone(),
				pool: delegator.pool.clone(),
				amount: balance_to_unbond,
			});

			// Now that we know everything has worked write the items to storage.
			BondedPool::insert(bonded_pool);
			SubPoolsStorage::insert(&delegator.pool, sub_pools);
			Delegators::insert(who, delegator);

			Ok(())
		}

		#[pallet::weight(666)]
		pub fn withdraw_unbonded(origin: OriginFor<T>, num_slashing_spans: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;

			let unbonding_era = delegator.unbonding_era.ok_or(Error::<T>::NotUnbonding)?;
			let current_era = T::StakingInterface::current_era().unwrap_or(Zero::zero());
			// TODO: make this an ensure
			if current_era.saturating_sub(unbonding_era) < T::StakingInterface::bonding_duration() {
				return Err(Error::<T>::NotUnbondedYet.into())
			};

			let mut sub_pools =
				SubPoolsStorage::<T>::get(&delegator.pool).ok_or(Error::<T>::SubPoolsNotFound)?;
			let balance_to_unbond = if let Some(pool) = sub_pools.with_era.get_mut(&unbonding_era) {
				let balance_to_unbond = pool.balance_to_unbond(delegator.points);
				pool.points = pool.points.saturating_sub(delegator.points);
				pool.balance = pool.balance.saturating_sub(balance_to_unbond);

				balance_to_unbond
			} else {
				// A pool does not belong to this era, so it must have been merged to the era-less
				// pool.
				let balance_to_unbond = sub_pools.no_era.balance_to_unbond(delegator.points);
				sub_pools.no_era.points = sub_pools.no_era.points.saturating_sub(delegator.points);
				sub_pools.no_era.balance =
					sub_pools.no_era.balance.saturating_sub(balance_to_unbond);

				balance_to_unbond
			};

			T::StakingInterface::withdraw_unbonded(delegator.pool.clone(), num_slashing_spans)?;

			T::Currency::transfer(
				&delegator.pool,
				&who,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)
			.defensive_map_err(|e| e)?;

			SubPoolsStorage::<T>::insert(&delegator.pool, sub_pools);
			Delegators::<T>::remove(&who);

			Self::deposit_event(Event::<T>::Withdrawn {
				delegator: who,
				pool: delegator.pool,
				amount: balance_to_unbond,
			});

			Ok(())
		}

		/// Create a pool.
		///
		/// * `validators`: _Stash_ addresses of the validators to nominate.
		/// * `amount`: Balance to delegate to the pool. Must meet the minimum bond.
		/// * `index`: Disambiguation index for seeding account generation. Likely only useful when
		///   creating multiple pools in the same extrinsic.
		#[pallet::weight(666)]
		#[frame_support::transactional]
		pub fn create(
			origin: OriginFor<T>,
			validators: Vec<<T::Lookup as StaticLookup>::Source>,
			amount: BalanceOf<T>,
			index: u16,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(amount >= T::StakingInterface::minimum_bond(), Error::<T>::MinimumBondNotMet);

			let (pool_account, reward_account) = Self::create_accounts(index);
			ensure!(!BondedPoolPoints::<T>::contains_key(&pool_account), Error::<T>::IdInUse);

			let mut bonded_pool =
				BondedPool::<T> { points: Zero::zero(), account: pool_account.clone() };
			// We must calculate the points to issue *before* we bond who's funds, else
			// points:balance ratio will be wrong.
			let points_to_issue = bonded_pool.points_to_issue(amount);
			bonded_pool.points = points_to_issue;

			T::Currency::transfer(&who, &pool_account, amount, ExistenceRequirement::AllowDeath)?;
			T::StakingInterface::bond(
				pool_account.clone(),
				// We make the stash and controller the same for simplicity
				pool_account.clone(),
				amount,
				reward_account.clone(),
			)?;
			T::StakingInterface::nominate(&pool_account, validators);

			Delegators::<T>::insert(
				who,
				Delegator::<T> {
					pool: pool_account.clone(),
					points: points_to_issue,
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None,
				},
			);
			BondedPool::<T>::insert(bonded_pool);
			RewardPools::<T>::insert(
				pool_account,
				RewardPool::<T> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account: reward_account,
				},
			);

			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(
				T::StakingInterface::bonding_duration() < MaxUnbonding::<T>::get(),
				"There must be more unbonding pools then the bonding duration /
				so a slash can be applied to relevant unboding pools. (We assume /
				the bonding duration > slash deffer duration.",
			);
		}
	}
}

impl<T: Config> Pallet<T> {
	fn create_accounts(index: u16) -> (T::AccountId, T::AccountId) {
		let parent_hash = frame_system::Pallet::<T>::parent_hash();
		let ext_index = frame_system::Pallet::<T>::extrinsic_index().unwrap_or_default();

		let stash_entropy =
			(b"pools/stash", index, parent_hash, ext_index).using_encoded(sp_core::blake2_256);
		let reward_entropy =
			(b"pools/rewards", index, parent_hash, ext_index).using_encoded(sp_core::blake2_256);

		(
			Decode::decode(&mut TrailingZeroInput::new(stash_entropy.as_ref()))
				.expect("infinite length input; no invalid inputs for type; qed"),
			Decode::decode(&mut TrailingZeroInput::new(reward_entropy.as_ref()))
				.expect("infinite length input; no invalid inputs for type; qed"),
		)
	}

	/// Calculate the rewards for `delegator`.
	fn calculate_delegator_payout(
		bonded_pool: &BondedPool<T>,
		reward_pool: RewardPool<T>,
		mut delegator: Delegator<T>,
	) -> Result<(RewardPool<T>, Delegator<T>, BalanceOf<T>), DispatchError> {
		// If the delegator is unbonding they cannot claim rewards. Note that when the delagator
		// goes to unbond, the unbond function should claim rewards for the final time.
		ensure!(delegator.unbonding_era.is_none(), Error::<T>::AlreadyUnbonding);

		let last_total_earnings = reward_pool.total_earnings;
		let mut reward_pool = reward_pool.update_total_earnings_and_balance();
		// Notice there is an edge case where total_earnings have not increased and this is zero
		let new_earnings = T::BalanceToU256::convert(
			reward_pool.total_earnings.saturating_sub(last_total_earnings),
		);

		// The new points that will be added to the pool. For every unit of balance that has
		// been earned by the reward pool, we inflate the reward pool points by
		// `bonded_pool.points`. In effect this allows each, single unit of balance (e.g.
		// plank) to be divvied up pro-rata among delegators based on points.
		let new_points = T::BalanceToU256::convert(bonded_pool.points).saturating_mul(new_earnings);

		// The points of the reward pool after taking into account the new earnings. Notice that
		// this only stays even or increases over time except for when we subtract delegator virtual
		// shares.
		let current_points = reward_pool.points.saturating_add(new_points);

		// The rewards pool's earnings since the last time this delegator claimed a payout
		let new_earnings_since_last_claim =
			reward_pool.total_earnings.saturating_sub(delegator.reward_pool_total_earnings);
		// The points of the reward pool that belong to the delegator.
		let delegator_virtual_points = T::BalanceToU256::convert(delegator.points)
			.saturating_mul(T::BalanceToU256::convert(new_earnings_since_last_claim));

		let delegator_payout = if delegator_virtual_points.is_zero() ||
			current_points.is_zero() ||
			reward_pool.balance.is_zero()
		{
			Zero::zero()
		} else {
			// Equivalent to `(delegator_virtual_points / current_points) * reward_pool.balance`
			T::U256ToBalance::convert(
				delegator_virtual_points
					.saturating_mul(T::BalanceToU256::convert(reward_pool.balance))
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

	/// Transfer the delegator their payout from the pool and deposit the corresponding event.
	fn transfer_reward(
		reward_pool: &T::AccountId,
		delegator: T::AccountId,
		pool: T::AccountId,
		payout: BalanceOf<T>,
	) -> Result<(), DispatchError> {
		T::Currency::transfer(reward_pool, &delegator, payout, ExistenceRequirement::AllowDeath)?;
		Self::deposit_event(Event::<T>::PaidOut { delegator, pool, payout });

		Ok(())
	}

	fn do_reward_payout(
		delegator_id: T::AccountId,
		delegator: Delegator<T>,
		bonded_pool: &BondedPool<T>,
	) -> DispatchResult {
		let reward_pool = RewardPools::<T>::get(&delegator.pool).ok_or_else(|| {
			log!(error, "A reward pool could not be found, this is a system logic error.");
			Error::<T>::RewardPoolNotFound
		})?;

		let (reward_pool, delegator, delegator_payout) =
			Self::calculate_delegator_payout(bonded_pool, reward_pool, delegator)?;

		// Transfer payout to the delegator.
		Self::transfer_reward(
			&reward_pool.account,
			delegator_id.clone(),
			delegator.pool.clone(),
			delegator_payout,
		)?;

		// Write the updated delegator and reward pool to storage
		RewardPools::insert(&delegator.pool, reward_pool);
		Delegators::insert(delegator_id, delegator);

		Ok(())
	}

	fn do_slash(
		SlashPoolArgs {
			pool_stash,
			slash_amount,
			slash_era,
			apply_era,
			active_bonded,
		}: SlashPoolArgs::<T::AccountId, BalanceOf<T>>,
	) -> Option<SlashPoolOut<BalanceOf<T>>> {
		// Make sure this is a pool account
		BondedPoolPoints::<T>::contains_key(&pool_stash).then(|| ())?;
		let mut sub_pools = SubPoolsStorage::<T>::get(pool_stash).unwrap_or_default();

		let affected_range = (slash_era + 1)..=apply_era;

		// Note that this doesn't count the balance in the `no_era` pool
		let unbonding_affected_balance: BalanceOf<T> =
			affected_range.clone().fold(BalanceOf::<T>::zero(), |balance_sum, era| {
				if let Some(unbond_pool) = sub_pools.with_era.get(&era) {
					balance_sum.saturating_add(unbond_pool.balance)
				} else {
					balance_sum
				}
			});

		// Note that the balances of the bonded pool and its affected sub-pools will saturated at
		// zero if slash_amount > total_affected_balance
		let total_affected_balance = active_bonded.saturating_add(unbonding_affected_balance);
		if total_affected_balance.is_zero() {
			return Some(SlashPoolOut {
				slashed_bonded: Zero::zero(),
				slashed_unlocking: Default::default(),
			})
		}
		let slashed_unlocking: BTreeMap<_, _> = affected_range
			.filter_map(|era| {
				if let Some(mut unbond_pool) = sub_pools.with_era.get_mut(&era) {
					let after_slash_balance = {
						// Equivalent to `(slash_amount / total_affected_balance) *
						// unbond_pool.balance`
						let pool_slash_amount = slash_amount
							.saturating_mul(unbond_pool.balance)
							// We check for zero above
							.div(total_affected_balance);

						unbond_pool.balance.saturating_sub(pool_slash_amount)
					};

					unbond_pool.balance = after_slash_balance;

					Some((era, after_slash_balance))
				} else {
					None
				}
			})
			.collect();
		SubPoolsStorage::<T>::insert(pool_stash, sub_pools);

		// Equivalent to `(slash_amount / total_affected_balance) * active_bonded`
		let slashed_bonded = {
			let bonded_pool_slash_amount = slash_amount
				.saturating_mul(active_bonded)
				// We check for zero above
				.div(total_affected_balance);

			active_bonded.saturating_sub(bonded_pool_slash_amount)
		};
		Some(SlashPoolOut { slashed_bonded, slashed_unlocking })
	}
}

impl<T: Config> PoolsInterface for Pallet<T> {
	type AccountId = T::AccountId;
	type Balance = BalanceOf<T>;

	fn slash_pool(
		args: SlashPoolArgs<Self::AccountId, Self::Balance>,
	) -> Option<SlashPoolOut<Self::Balance>> {
		Self::do_slash(args)
	}
}
