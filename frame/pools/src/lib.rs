//! Delegation pools for nominating in `pallet-staking`.
//!
//! The delegation pool abstraction is concretely composed of:
//!
//! * bonded pool: This pool represents the actively staked funds ...
//! * rewards pool: The rewards earned by actively staked funds. Delegator can withdraw rewards once
//! * sub pools: This a group of pools where we have a set of pools organized by era
//!   (`SubPools.with_era`) and one pool that is not associated with an era (`SubPools.no_era`).
//!   Once a `with_era` pool is older then `current_era - MaxUnbonding`, its points and balance get
//!   merged into the `no_era` pool.
//!
//! # Joining
//!
//! # Claiming rewards
//!
//! # Unbonding and withdrawing
//!
//! # Slashing
//!
//! # Pool creation
//!
//! # Negatives
//! - no voting
//! - ..
//!
//! RUNTIME BUILDER WARNINGS
//! - watch out for overflow of `RewardPoints` and `BalanceOf<T>` types. Consider the chains total
//!   issuance, staking reward rate, and burn rate.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	ensure,
	pallet_prelude::*,
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{Currency, ExistenceRequirement, Get},
	transactional, DefaultNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_core::U256;
use sp_runtime::traits::{Bounded, Convert, Saturating, StaticLookup, TrailingZeroInput, Zero};
use sp_staking::{EraIndex, PoolsInterface, StakingInterface};
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

type PoolId = u32;
type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type SubPoolsWithEra<T> = BoundedBTreeMap<EraIndex, UnbondPool<T>, <T as Config>::MaxUnbonding>;
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
#[cfg_attr(feature = "std", derive(Clone, PartialEq, DefaultNoBound))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Delegator<T: Config> {
	pool: PoolId,
	/// The quantity of points this delegator has in the bonded pool or in a sub pool if
	/// `Self::unbonding_era` is some.
	points: BalanceOf<T>,
	/// The reward pools total earnings _ever_ the last time this delegator claimed a payout.
	/// Assuming no massive burning events, we expect this value to always be below total issuance.
	// TODO: ^ double check the above is an OK assumption
	/// This value lines up with the `RewardPool::total_earnings` after a delegator claims a
	/// payout.
	reward_pool_total_earnings: BalanceOf<T>,
	/// The era this delegator started unbonding at.
	unbonding_era: Option<EraIndex>,
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebugNoBound)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct BondedPool<T: Config> {
	points: BalanceOf<T>,
	// The _Stash_ and _Controller_ account for the pool.
	account_id: T::AccountId,
}

impl<T: Config> BondedPool<T> {
	/// Get the amount of points to issue for some new funds that will be bonded in the pool.
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account_id).unwrap_or(Zero::zero());
		points_to_issue::<T>(bonded_balance, self.points, new_funds)
	}

	// Get the amount of balance to unbond from the pool based on a delegator's points of the pool.
	fn balance_to_unbond(&self, delegator_points: BalanceOf<T>) -> BalanceOf<T> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account_id).unwrap_or(Zero::zero());
		balance_to_unbond::<T>(bonded_balance, self.points, delegator_points)
	}

	// Check that the pool can accept a member with `new_funds`.
	fn ok_to_join_with(&self, new_funds: BalanceOf<T>) -> Result<(), DispatchError> {
		let bonded_balance =
			T::StakingInterface::bonded_balance(&self.account_id).unwrap_or(Zero::zero());
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
	account_id: T::AccountId,
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
		let current_balance = T::Currency::free_balance(&self.account_id);
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
		if current_era < T::MaxUnbonding::get().into() {
			// For the first `0..MaxUnbonding` eras of the chain we don't need to do anything.
			// I.E. if `MaxUnbonding` is 5 and we are in era 4 we can add a pool for this era and
			// have exactly `MaxUnbonding` pools.
			return self
		}

		//  I.E. if `MaxUnbonding` is 5 and current era is 10, we only want to retain pools 6..=10.
		let newest_era_to_remove = current_era.saturating_sub(T::MaxUnbonding::get());

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
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::{ensure_signed, pallet_prelude::*};

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	#[pallet::generate_storage_info]
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

		/// The maximum amount of eras an unbonding pool can exist prior to being merged with the
		/// `no_era	 pool. This should at least be greater then the `UnbondingDuration` for staking
		/// so delegator have a chance to withdraw unbonded before their pool gets merged with the
		/// `no_era` pool. This *must* at least be greater then the slash deffer duration.
		type MaxUnbonding: Get<u32>;
	}

	/// Active delegators.
	#[pallet::storage]
	pub(crate) type DelegatorStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator<T>>;

	/// `PoolId` lookup from the pool's `AccountId`. Useful for pool lookup from the slashing
	/// system.
	#[pallet::storage]
	pub(crate) type PoolIds<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, PoolId>;

	/// Bonded pools.
	#[pallet::storage]
	pub(crate) type BondedPoolStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, BondedPool<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool.
	#[pallet::storage]
	pub(crate) type RewardPoolStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a bonded pool,
	/// hence the name sub-pools.
	#[pallet::storage]
	pub(crate) type SubPoolsStorage<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, SubPools<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		Joined { delegator: T::AccountId, pool: PoolId, bonded: BalanceOf<T> },
		PaidOut { delegator: T::AccountId, pool: PoolId, payout: BalanceOf<T> },
		Unbonded { delegator: T::AccountId, pool: PoolId, amount: BalanceOf<T> },
		Withdrawn { delegator: T::AccountId, pool: PoolId, amount: BalanceOf<T> },
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
		/// The given pool id cannot be used to create a new pool because it is already in use.
		IdInUse,
		/// The amount does not meet the minimum bond to start nominating.
		MinimumBondNotMet,
		/// The transaction could not be executed due to overflow risk for the pool.
		OverflowRisk,
		/// An error from the staking pallet.
		StakingError,
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
		pub fn join(origin: OriginFor<T>, amount: BalanceOf<T>, target: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// If a delegator already exists that means they already belong to a pool
			ensure!(
				!DelegatorStorage::<T>::contains_key(&who),
				Error::<T>::AccountBelongsToOtherPool
			);

			let mut bonded_pool =
				BondedPoolStorage::<T>::get(target).ok_or(Error::<T>::PoolNotFound)?;
			bonded_pool.ok_to_join_with(amount)?;

			// The pool should always be created in such a way its in a state to bond extra, but if
			// the active balance is slashed below the minimum bonded or the account cannot be
			// found, we exit early.
			if !T::StakingInterface::can_bond_extra(&bonded_pool.account_id, amount) {
				return Err(Error::<T>::StakingError.into())
			}

			// We don't actually care about writing the reward pool, we just need its
			// total earnings at this point in time.
			let reward_pool = RewardPoolStorage::<T>::get(target)
				.ok_or(Error::<T>::RewardPoolNotFound)?
				// This is important because we want the most up-to-date total earnings.
				.update_total_earnings_and_balance();

			let old_free_balance = T::Currency::free_balance(&bonded_pool.account_id);
			// Transfer the funds to be bonded from `who` to the pools account so the pool can then
			// go bond them.
			T::Currency::transfer(
				&who,
				&bonded_pool.account_id,
				amount,
				ExistenceRequirement::KeepAlive,
			)?;

			// Try not to bail after the above transfer

			// This should now include the transferred balance.
			let new_free_balance = T::Currency::free_balance(&bonded_pool.account_id);
			// Get the exact amount we can bond extra.
			let exact_amount_to_bond = new_free_balance.saturating_sub(old_free_balance);
			// We must calculate the points to issue *before* we bond `who`'s funds, else the
			// points:balance ratio will be wrong.
			let new_points = bonded_pool.points_to_issue(exact_amount_to_bond);
			bonded_pool.points = bonded_pool.points.saturating_add(new_points);

			T::StakingInterface::bond_extra(&bonded_pool.account_id, exact_amount_to_bond)?;

			DelegatorStorage::insert(
				who.clone(),
				Delegator::<T> {
					pool: target,
					points: new_points,
					// TODO double check that this is ok.
					// At best the reward pool has the rewards up through the previous era. If the
					// delegator joins prior to the snapshot they will benefit from the rewards of
					// the current era despite not contributing to the pool's vote weight. If they
					// join after the snapshot is taken they will benefit from the rewards of the
					// next *2* eras because their vote weight will not be counted until the
					// snapshot in current era + 1.
					reward_pool_total_earnings: reward_pool.total_earnings,
					unbonding_era: None,
				},
			);
			BondedPoolStorage::insert(target, bonded_pool);

			Self::deposit_event(Event::<T>::Joined {
				delegator: who,
				pool: target,
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
			let delegator =
				DelegatorStorage::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let bonded_pool = BondedPoolStorage::<T>::get(&delegator.pool).ok_or_else(|| {
				log!(error, "A bonded pool could not be found, this is a system logic error.");
				Error::<T>::PoolNotFound
			})?;

			Self::do_reward_payout(who, delegator, &bonded_pool)?;

			Ok(())
		}

		/// A bonded delegator can use this to unbond _all_ funds from the pool.
		/// In order to withdraw the funds, the delegator must wait
		#[pallet::weight(666)]
		pub fn unbond(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator =
				DelegatorStorage::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let mut bonded_pool =
				BondedPoolStorage::<T>::get(delegator.pool).ok_or(Error::<T>::PoolNotFound)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points
			// no longer exist in the bonded pool and thus they can no longer claim their payouts.
			// It is not strictly necessary to claim the rewards, but we do it here for UX.
			Self::do_reward_payout(who.clone(), delegator, &bonded_pool)?;

			// Re-fetch the delegator because they where updated by `do_reward_payout`.
			let mut delegator =
				DelegatorStorage::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			// Note that we lazily create the unbonding pools here if they don't already exist
			let sub_pools = SubPoolsStorage::<T>::get(delegator.pool).unwrap_or_default();
			let current_era = T::StakingInterface::current_era();

			let balance_to_unbond = bonded_pool.balance_to_unbond(delegator.points);

			// Update the bonded pool. Note that we must do this *after* calculating the balance
			// to unbond so we have the correct points for the balance:share ratio.
			bonded_pool.points = bonded_pool.points.saturating_sub(delegator.points);

			// TODO: call withdraw unbonded to try and minimize unbonding chunks
			// Unbond in the actual underlying pool
			T::StakingInterface::unbond(&bonded_pool.account_id, balance_to_unbond)?;

			// Merge any older pools into the general, era agnostic unbond pool. Note that we do
			// this before inserting to ensure we don't go over the max unbonding pools.
			let mut sub_pools = sub_pools.maybe_merge_pools(current_era);

			// Update the unbond pool associated with the current era with the
			// unbonded funds. Note that we lazily create the unbond pool if it
			// does not yet exist.
			{
				let mut unbond_pool =
					sub_pools.with_era.entry(current_era).or_insert_with(|| UnbondPool::default());
				let points_to_issue = unbond_pool.points_to_issue(balance_to_unbond);
				unbond_pool.points = unbond_pool.points.saturating_add(points_to_issue);
				unbond_pool.balance = unbond_pool.balance.saturating_add(balance_to_unbond);
			}

			delegator.unbonding_era = Some(current_era);

			Self::deposit_event(Event::<T>::Unbonded {
				delegator: who.clone(),
				pool: delegator.pool,
				amount: balance_to_unbond,
			});

			// Now that we know everything has worked write the items to storage.
			BondedPoolStorage::insert(delegator.pool, bonded_pool);
			SubPoolsStorage::insert(delegator.pool, sub_pools);
			DelegatorStorage::insert(who, delegator);

			Ok(())
		}

		#[pallet::weight(666)]
		pub fn withdraw_unbonded(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator =
				DelegatorStorage::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;

			let unbonding_era = delegator.unbonding_era.ok_or(Error::<T>::NotUnbonding)?;
			let current_era = T::StakingInterface::current_era();
			if current_era.saturating_sub(unbonding_era) < T::StakingInterface::bonding_duration() {
				return Err(Error::<T>::NotUnbondedYet.into())
			};

			let mut sub_pools =
				SubPoolsStorage::<T>::get(delegator.pool).ok_or(Error::<T>::SubPoolsNotFound)?;

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

			let bonded_pool =
				BondedPoolStorage::<T>::get(delegator.pool).ok_or(Error::<T>::PoolNotFound)?;

			if T::Currency::free_balance(&bonded_pool.account_id) < balance_to_unbond {
				T::StakingInterface::withdraw_unbonded(&bonded_pool.account_id)?;
			}

			T::Currency::transfer(
				&bonded_pool.account_id,
				&who,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)
			.map_err(|e| {
				log::warn!("system logic error: pool could not withdraw_unbonded due to lack of free balance");
				e
			})?;

			SubPoolsStorage::<T>::insert(delegator.pool, sub_pools);
			DelegatorStorage::<T>::remove(&who);

			Self::deposit_event(Event::<T>::Withdrawn {
				delegator: who,
				pool: delegator.pool,
				amount: balance_to_unbond,
			});

			Ok(())
		}

		// NOTE: This is transactional because we cannot totally predict if the underlying bond will
		// work until we transfer the funds.
		#[pallet::weight(666)]
		#[transactional]
		pub fn create(
			origin: OriginFor<T>,
			id: PoolId,
			targets: Vec<<T::Lookup as StaticLookup>::Source>,
			amount: BalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(!BondedPoolStorage::<T>::contains_key(id), Error::<T>::IdInUse);
			ensure!(amount >= T::StakingInterface::minimum_bond(), Error::<T>::MinimumBondNotMet);
			// TODO create can_* fns so we can bail in the beggining if some pre-conditions are not

			let (stash, reward_dest) = Self::create_accounts(id);

			ensure!(
				T::StakingInterface::can_nominate(&stash, &targets) &&
					T::StakingInterface::can_bond(&stash, &stash, &reward_dest),
				Error::<T>::StakingError
			);

			let mut bonded_pool =
				BondedPool::<T> { points: Zero::zero(), account_id: stash.clone() };

			// We must calculate the points to issue *before* we bond who's funds, else
			// points:balance ratio will be wrong.
			let points_to_issue = bonded_pool.points_to_issue(amount);
			bonded_pool.points = points_to_issue;

			T::Currency::transfer(&who, &stash, amount, ExistenceRequirement::AllowDeath)?;

			T::StakingInterface::bond(
				stash.clone(),
				// We make the stash and controller the same for simplicity
				stash.clone(),
				amount,
				reward_dest.clone(),
			)
			.map_err(|e| {
				log!(warn, "error trying to bond new pool after a users balance was transferred.");
				e
			})?;

			T::StakingInterface::nominate(stash.clone(), targets).map_err(|e| {
				log!(warn, "error trying to nominate with a new pool after a users balance was transferred.");
				e
			})?;

			DelegatorStorage::<T>::insert(
				who,
				Delegator::<T> {
					pool: id,
					points: points_to_issue,
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None,
				},
			);
			BondedPoolStorage::<T>::insert(id, bonded_pool);
			RewardPoolStorage::<T>::insert(
				id,
				RewardPool::<T> {
					balance: Zero::zero(),
					points: U256::zero(),
					total_earnings: Zero::zero(),
					account_id: reward_dest,
				},
			);

			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(
				T::StakingInterface::bonding_duration() < T::MaxUnbonding::get(),
				"There must be more unbonding pools then the bonding duration /
				so a slash can be applied to relevant unboding pools. (We assume /
				the bonding duration > slash deffer duration.",
			);
		}
	}
}

impl<T: Config> Pallet<T> {
	fn create_accounts(id: PoolId) -> (T::AccountId, T::AccountId) {
		let parent_hash = frame_system::Pallet::<T>::parent_hash();
		let ext_index = frame_system::Pallet::<T>::extrinsic_index().unwrap_or_default();

		let stash_entropy =
			(b"pools/stash", id, parent_hash, ext_index).using_encoded(sp_core::blake2_256);
		let reward_entropy =
			(b"pools/rewards", id, parent_hash, ext_index).using_encoded(sp_core::blake2_256);

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
		// `bonded_pool.total_points`. In effect this allows each, single unit of balance (e.g.
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
		pool: PoolId,
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
		let reward_pool = RewardPoolStorage::<T>::get(&delegator.pool).ok_or_else(|| {
			log!(error, "A reward pool could not be found, this is a system logic error.");
			Error::<T>::RewardPoolNotFound
		})?;

		let (reward_pool, delegator, delegator_payout) =
			Self::calculate_delegator_payout(bonded_pool, reward_pool, delegator)?;

		// Transfer payout to the delegator.
		Self::transfer_reward(
			&reward_pool.account_id,
			delegator_id.clone(),
			delegator.pool,
			delegator_payout,
		)?;

		// Write the updated delegator and reward pool to storage
		RewardPoolStorage::insert(delegator.pool, reward_pool);
		DelegatorStorage::insert(delegator_id, delegator);

		Ok(())
	}

	fn do_slash(
		// This would be the nominator account
		pool_account: &T::AccountId,
		// Value of slash
		slash_amount: BalanceOf<T>,
		// Era the slash was initially reported
		slash_era: EraIndex,
		// Era the slash is applied in
		apply_era: EraIndex,
		// The current active bonded of the account (i.e. `StakingLedger::active`)
		active_bonded_balance: BalanceOf<T>,
	) -> Option<(BalanceOf<T>, BTreeMap<EraIndex, BalanceOf<T>>)> {
		let pool_id = PoolIds::<T>::get(pool_account)?;
		let mut sub_pools = SubPoolsStorage::<T>::get(pool_id).unwrap_or_default();

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
		let total_affected_balance =
			active_bonded_balance.saturating_add(unbonding_affected_balance);

		if total_affected_balance.is_zero() {
			return Some((Zero::zero(), Default::default()))
		}
		if slash_amount > total_affected_balance {
			// TODO this shouldn't happen as long as MaxBonding pools is greater thant the slash
			// defer duration, which it should implicitly be because we expect it be longer then the
			// UnbondindDuration. TODO clearly document these assumptions
		};

		let unlock_chunk_balances: BTreeMap<_, _> = affected_range
			.filter_map(|era| {
				if let Some(mut unbond_pool) = sub_pools.with_era.get_mut(&era) {
					// Equivalent to `(slash_amount / total_affected_balance) * unbond_pool.balance`
					let pool_slash_amount = slash_amount
						.saturating_mul(unbond_pool.balance)
						// We check for zero above
						.div(total_affected_balance);
					let after_slash_balance = unbond_pool.balance.saturating_sub(pool_slash_amount);

					unbond_pool.balance = after_slash_balance;

					Some((era, after_slash_balance))
				} else {
					None
				}
			})
			.collect();

		SubPoolsStorage::<T>::insert(pool_id, sub_pools);

		// Equivalent to `(slash_amount / total_affected_balance) * active_bonded_balance`
		let slashed_bonded_pool_balance = slash_amount
			.saturating_mul(active_bonded_balance)
			// We check for zero above
			.div(total_affected_balance);

		Some((slashed_bonded_pool_balance, unlock_chunk_balances))
	}
}

impl<T: Config> PoolsInterface for Pallet<T> {
	type AccountId = T::AccountId;
	type Balance = BalanceOf<T>;

	fn slash_pool(
		pool_account: &Self::AccountId,
		slash_amount: Self::Balance,
		slash_era: EraIndex,
		apply_era: EraIndex,
		active_bonded: BalanceOf<T>,
	) -> Option<(Self::Balance, BTreeMap<EraIndex, Self::Balance>)> {
		Self::do_slash(pool_account, slash_amount, slash_era, apply_era, active_bonded)
	}
}

// TODO
// -
// - tests
// - force pool creation
// - rebond_rewards
// - pool update targets
// - pool block - don't allow new joiners (or bond_extra)
// - pool begin destroy - unbond the entire pool balance
// - pool end destroy - once all subpools are empty delete everything from storage
// - force pool delete?
