//! Delegation pools for nominating in `pallet-staking`.
//!
//! The delegation pool abstraction is concretely composed of:
//!
//! * primary pool: This pool represents the actively staked funds ...
//! * rewards pool: The rewards earned by actively staked funds. Delegator can withdraw rewards once
//! * sub pools: This a group of pools where we have a set of pools organized by era
//!   (`SubPoolsContainer.with_era`) and one pool that is not associated with an era
//!   (`SubsPoolsContainer.no_era`). Once a `with_era` pool is older then `current_era -
//!   MaxUnbonding`, its points and balance get merged into the `no_era` pool.
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

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	ensure,
	pallet_prelude::*,
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{Currency, ExistenceRequirement, Get},
	DefaultNoBound,
};
use scale_info::TypeInfo;
use sp_arithmetic::{FixedPointNumber, FixedU128};
use sp_runtime::traits::{Convert, One, Saturating, StaticLookup, TrailingZeroInput, Zero};
use sp_staking::{EraIndex, PoolsInterface, StakingInterface};
use sp_std::collections::btree_map::BTreeMap;

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
type PointsOf<T> = BalanceOf<T>;
type SubPoolsWithEra<T> = BoundedBTreeMap<EraIndex, UnbondPool<T>, <T as Config>::MaxUnbonding>;

const POINTS_TO_BALANCE_INIT_RATIO: u32 = 1;

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Delegator<T: Config> {
	pool: PoolId,
	/// The quantity of points this delegator has in the primary pool or in an sub pool if
	/// `Self::unbonding_era` is some.
	points: PointsOf<T>,
	/// The reward pools total earnings _ever_ the last time this delegator claimed a payout.
	/// Assuming no massive burning events, we expect this value to always be below total issuance.
	/// ^ double check the above is an OK assumption
	/// This value lines up with the `RewardPool.total_earnings` after a delegator claims a payout.
	reward_pool_total_earnings: BalanceOf<T>,
	/// The era this delegator started unbonding at.
	unbonding_era: Option<EraIndex>,
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct PrimaryPool<T: Config> {
	points: PointsOf<T>, // Probably needs to be some type of BigUInt
	// The _Stash_ and _Controller_ account for the pool.
	account_id: T::AccountId,
}

impl<T: Config> PrimaryPool<T> {
	/// Get the amount of points to issue for some new funds that will be bonded in the pool.
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> PointsOf<T> {
		let bonded_balance = T::StakingInterface::bonded_balance(&self.account_id);
		if bonded_balance.is_zero() || self.points.is_zero() {
			debug_assert!(bonded_balance.is_zero() && self.points.is_zero());

			new_funds.saturating_mul(POINTS_TO_BALANCE_INIT_RATIO.into())
		} else {
			let points_per_balance = {
				let balance = T::BalanceToU128::convert(bonded_balance);
				let points = T::BalanceToU128::convert(self.points);
				// REMINDER: `saturating_from_rational` panics if denominator is zero
				FixedU128::saturating_from_rational(points, balance)
			};
			let new_funds = T::BalanceToU128::convert(new_funds);

			T::U128ToBalance::convert(points_per_balance.saturating_mul_int(new_funds))
		}
	}

	// Get the amount of balance to unbond from the pool based on a delegator's points of the pool.
	fn balance_to_unbond(&self, delegator_points: PointsOf<T>) -> BalanceOf<T> {
		let bonded_balance = T::StakingInterface::bonded_balance(&self.account_id);
		if bonded_balance.is_zero() || delegator_points.is_zero() {
			// There is nothing to unbond
			return Zero::zero()
		}

		let balance_per_share = {
			let balance = T::BalanceToU128::convert(bonded_balance);
			let points = T::BalanceToU128::convert(self.points);
			// REMINDER: `saturating_from_rational` panics if denominator is zero
			FixedU128::saturating_from_rational(balance, points)
		};
		let delegator_points = T::BalanceToU128::convert(delegator_points);

		T::U128ToBalance::convert(balance_per_share.saturating_mul_int(delegator_points))
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
	/// The balance of this reward pool after the last claimed payout.
	balance: BalanceOf<T>,
	/// The points of this reward pool after the last claimed payout
	points: BalanceOf<T>,
	/// The total earnings _ever_ of this reward pool after the last claimed payout. I.E. the sum
	/// of all incoming balance through the pools life.
	total_earnings: BalanceOf<T>,
	/// The reward destination for the pool.
	account_id: T::AccountId,
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

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
struct UnbondPool<T: Config> {
	points: PointsOf<T>,
	balance: BalanceOf<T>,
}

impl<T: Config> UnbondPool<T> {
	fn points_to_issue(&self, new_funds: BalanceOf<T>) -> PointsOf<T> {
		if self.balance.is_zero() || self.points.is_zero() {
			debug_assert!(self.balance.is_zero() && self.points.is_zero());

			new_funds.saturating_mul(POINTS_TO_BALANCE_INIT_RATIO.into())
		} else {
			let points_per_balance = {
				let balance = T::BalanceToU128::convert(self.balance);
				let points = T::BalanceToU128::convert(self.points);
				// REMINDER: `saturating_from_rational` panics if denominator is zero
				FixedU128::saturating_from_rational(points, balance)
			};
			let new_funds = T::BalanceToU128::convert(new_funds);

			T::U128ToBalance::convert(points_per_balance.saturating_mul_int(new_funds))
		}
	}

	fn balance_to_unbond(&self, delegator_points: PointsOf<T>) -> BalanceOf<T> {
		if self.balance.is_zero() || delegator_points.is_zero() {
			// There is nothing to unbond
			return Zero::zero()
		}

		let balance_per_share = {
			let balance = T::BalanceToU128::convert(self.balance);
			let points = T::BalanceToU128::convert(self.points);
			// REMINDER: `saturating_from_rational` panics if denominator is zero
			FixedU128::saturating_from_rational(balance, points)
		};
		let delegator_points = T::BalanceToU128::convert(delegator_points);

		T::U128ToBalance::convert(balance_per_share.saturating_mul_int(delegator_points))
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, DefaultNoBound)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
struct SubPoolsContainer<T: Config> {
	/// A general, era agnostic pool of funds that have fully unbonded. The pools
	/// of `self.with_era` will lazily be merged into into this pool if they are
	/// older then `current_era - T::MAX_UNBONDING`.
	no_era: UnbondPool<T>,
	/// Map of era => unbond pools.
	with_era: SubPoolsWithEra<T>,
}

impl<T: Config> SubPoolsContainer<T> {
	/// Merge the oldest unbonding pool with an era into the general unbond pool with no associated
	/// era.
	fn maybe_merge_pools(mut self, current_era: EraIndex) -> Self {
		if current_era < T::MaxUnbonding::get().into() {
			// For the first `T::MAX_UNBONDING` eras of the chain we don't need to do anything.
			// I.E. if `MAX_UNBONDING` is 5 and we are in era 4 we can add a pool for this era and
			// have exactly `MAX_UNBONDING` pools.
			return self
		}

		//  I.E. if `MAX_UNBONDING` is 5 and current era is 10, we only want to retain pools 6..=10.
		let oldest_era_to_keep = current_era - T::MaxUnbonding::get().saturating_add(1);

		let eras_to_remove: Vec<_> =
			self.with_era.keys().cloned().filter(|era| *era < oldest_era_to_keep).collect();
		for era in eras_to_remove {
			if let Some(p) = self.with_era.remove(&era) {
				self.no_era.points.saturating_add(p.points);
				self.no_era.balance.saturating_add(p.balance);
			} else {
				// the world is broken
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

		// Infallible method for converting `Currency::Balance` to `u128`.
		type BalanceToU128: Convert<BalanceOf<Self>, u128>;

		// Infallible method for converting `u128` to `Currency::Balance`.
		type U128ToBalance: Convert<u128, BalanceOf<Self>>;

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
	pub(crate) type Delegators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator<T>>;

	/// `PoolId` lookup from the pool's `AccountId`. Useful for pool lookup from the slashing
	/// system.
	#[pallet::storage]
	pub(crate) type PoolIds<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, PoolId>;

	/// Bonded pools.
	#[pallet::storage]
	pub(crate) type PrimaryPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, PrimaryPool<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool.
	#[pallet::storage]
	pub(crate) type RewardPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, RewardPool<T>>;

	/// Groups of unbonding pools. Each group of unbonding pools belongs to a primary pool,
	/// hence the name sub-pools.
	#[pallet::storage]
	pub(crate) type SubPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, SubPoolsContainer<T>>;

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
		/// The given (primary) pool id does not exist.
		PoolNotFound,
		/// The given account is not a delegator.
		DelegatorNotFound,
		// The given reward pool does not exist. In all cases this is a system logic error.
		RewardPoolNotFound,
		/// The account is already delegating in another pool. An account may only belong to one
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
		MinimiumBondNotMet,
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
			// if a delegator already exists that means they already belong to a pool
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			// Ensure that the `target` pool exists,
			let mut primary_pool =
				PrimaryPools::<T>::get(target).ok_or(Error::<T>::PoolNotFound)?;
			// And that `amount` will meet the minimum bond
			let old_free_balance = T::Currency::free_balance(&primary_pool.account_id);
			ensure!(
				old_free_balance.saturating_add(amount) >= T::StakingInterface::minimum_bond(),
				Error::<T>::InsufficientBond
			);
			// Note that we don't actually care about writing the reward pool, we just need its
			// total earnings at this point in time.
			let reward_pool = RewardPools::<T>::get(target)
				.ok_or(Error::<T>::RewardPoolNotFound)?
				// This is important because we want the most up-to-date total earnings.
				.update_total_earnings_and_balance();

			// Transfer the funds to be bonded from `who` to the pools account so the pool can then
			// go bond them.
			T::Currency::transfer(
				&who,
				&primary_pool.account_id,
				amount,
				ExistenceRequirement::KeepAlive,
			)?;
			// This should now include the transferred balance.
			let new_free_balance = T::Currency::free_balance(&primary_pool.account_id);
			// Get the exact amount we can bond extra.
			let exact_amount_to_bond = new_free_balance.saturating_sub(old_free_balance);

			// Issue the new points.
			let new_points = primary_pool.points_to_issue(exact_amount_to_bond);
			primary_pool.points = primary_pool.points.saturating_add(new_points);
			let delegator = Delegator::<T> {
				pool: target,
				points: new_points,
				// TODO double check that this is ok.
				// At best the reward pool has the rewards up through the previous era. If the
				// delegator joins prior to the snapshot they will benefit from the rewards of the
				// current era despite not contributing to the pool's vote weight. If they join
				// after the snapshot is taken they will benefit from the rewards of the next *2*
				// eras because their vote weight will not be counted until the snapshot in current
				// era + 1.
				reward_pool_total_earnings: reward_pool.total_earnings,
				unbonding_era: None,
			};

			T::StakingInterface::bond_extra(&primary_pool.account_id, exact_amount_to_bond)?;

			Delegators::insert(who.clone(), delegator);
			PrimaryPools::insert(target, primary_pool);

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
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let primary_pool = PrimaryPools::<T>::get(&delegator.pool).ok_or_else(|| {
				log!(error, "A primary pool could not be found, this is a system logic error.");
				debug_assert!(
					false,
					"A primary pool could not be found, this is a system logic error."
				);
				Error::<T>::PoolNotFound
			})?;

			Self::do_reward_payout(who, delegator, &primary_pool)?;

			Ok(())
		}

		/// A bonded delegator can use this to unbond _all_ funds from the pool.
		/// In order to withdraw the funds, the delegator must wait
		#[pallet::weight(666)]
		pub fn unbond(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			let mut primary_pool =
				PrimaryPools::<T>::get(delegator.pool).ok_or(Error::<T>::PoolNotFound)?;

			// Claim the the payout prior to unbonding. Once the user is unbonding their points
			// no longer exist in the primary pool and thus they can no longer claim their payouts.
			// It is not strictly necessary to claim the rewards, but we do it here for UX.
			Self::do_reward_payout(who.clone(), delegator, &primary_pool)?;

			// Re-fetch the delegator because they where updated by `do_reward_payout`.
			let mut delegator = Delegators::<T>::get(&who).ok_or(Error::<T>::DelegatorNotFound)?;
			// Note that we lazily create the unbonding pools here if they don't already exist
			let sub_pools = SubPools::<T>::get(delegator.pool).unwrap_or_default();
			let current_era = T::StakingInterface::current_era();

			let balance_to_unbond = primary_pool.balance_to_unbond(delegator.points);

			// Update the primary pool. Note that we must do this *after* calculating the balance
			// to unbond so we have the correct points for the balance:share ratio.
			primary_pool.points = primary_pool.points.saturating_sub(delegator.points);

			// Unbond in the actual underlying pool
			T::StakingInterface::unbond(&primary_pool.account_id, balance_to_unbond)?;

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
			PrimaryPools::insert(delegator.pool, primary_pool);
			SubPools::insert(delegator.pool, sub_pools);
			Delegators::insert(who, delegator);

			Ok(())
		}

		#[pallet::weight(666)]
		pub fn withdraw_unbonded(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegator = Delegators::<T>::take(&who).ok_or(Error::<T>::DelegatorNotFound)?;

			let unbonding_era = delegator.unbonding_era.ok_or(Error::<T>::NotUnbonding)?;
			let current_era = T::StakingInterface::current_era();
			if current_era.saturating_sub(unbonding_era) < T::StakingInterface::bonding_duration() {
				return Err(Error::<T>::NotUnbondedYet.into())
			};

			let mut sub_pools = SubPools::<T>::get(delegator.pool).unwrap_or_default();

			let balance_to_unbond = if let Some(pool) = sub_pools.with_era.get_mut(&current_era) {
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

			let primary_pool =
				PrimaryPools::<T>::get(delegator.pool).ok_or(Error::<T>::PoolNotFound)?;
			T::Currency::transfer(
				&primary_pool.account_id,
				&who,
				balance_to_unbond,
				ExistenceRequirement::AllowDeath,
			)?;

			SubPools::<T>::insert(delegator.pool, sub_pools);

			Self::deposit_event(Event::<T>::Withdrawn {
				delegator: who,
				pool: delegator.pool,
				amount: balance_to_unbond,
			});

			Ok(())
		}

		#[pallet::weight(666)]
		pub fn create(
			origin: OriginFor<T>,
			id: PoolId,
			targets: Vec<<T::Lookup as StaticLookup>::Source>,
			amount: BalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(!PrimaryPools::<T>::contains_key(id), Error::<T>::IdInUse);
			ensure!(amount >= T::StakingInterface::minimum_bond(), Error::<T>::MinimiumBondNotMet);

			let (stash, reward_dest) = Self::create_accounts(&who, id);

			T::Currency::transfer(&who, &stash, amount, ExistenceRequirement::AllowDeath)?;

			// T::StakingInterface::can_bond()
			// T::StakingInterface::can_nominate()

			T::StakingInterface::bond(
				stash.clone(),
				// We make the stash and controller the same for simplicity
				stash.clone(),
				amount,
				reward_dest.clone(),
			)?;

			T::StakingInterface::nominate(stash.clone(), targets)?;

			let mut primary_pool = PrimaryPool::<T> { points: Zero::zero(), account_id: stash };
			let points_to_issue = primary_pool.points_to_issue(amount);
			primary_pool.points = points_to_issue;

			Delegators::<T>::insert(
				who,
				Delegator::<T> {
					pool: id,
					points: points_to_issue,
					reward_pool_total_earnings: Zero::zero(),
					unbonding_era: None,
				},
			);
			PrimaryPools::<T>::insert(id, primary_pool);
			RewardPools::<T>::insert(
				id,
				RewardPool::<T> {
					balance: Zero::zero(),
					points: Zero::zero(),
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
	fn create_accounts(who: &T::AccountId, id: PoolId) -> (T::AccountId, T::AccountId) {
		let parent_hash = frame_system::Pallet::<T>::parent_hash();
		let ext_index = frame_system::Pallet::<T>::extrinsic_index().unwrap_or_default();

		let stash_entropy =
			(b"pools/stash", who, id, parent_hash, ext_index).using_encoded(sp_core::blake2_256);
		let reward_entropy =
			(b"pools/rewards", who, id, parent_hash, ext_index).using_encoded(sp_core::blake2_256);

		(
			Decode::decode(&mut TrailingZeroInput::new(stash_entropy.as_ref()))
				.expect("infinite length input; no invalid inputs for type; qed"),
			Decode::decode(&mut TrailingZeroInput::new(reward_entropy.as_ref()))
				.expect("infinite length input; no invalid inputs for type; qed"),
		)
	}

	/// Calculate the rewards for `delegator`.
	fn calculate_delegator_payout(
		primary_pool: &PrimaryPool<T>,
		reward_pool: RewardPool<T>,
		mut delegator: Delegator<T>,
	) -> Result<(RewardPool<T>, Delegator<T>, BalanceOf<T>), DispatchError> {
		// If the delegator is unbonding they cannot claim rewards. Note that when the delagator
		// goes to unbond, the unbond function should claim rewards for the final time.
		ensure!(delegator.unbonding_era.is_none(), Error::<T>::AlreadyUnbonding);

		let last_total_earnings = reward_pool.total_earnings;
		let mut reward_pool = reward_pool.update_total_earnings_and_balance();
		let new_earnings = reward_pool.total_earnings.saturating_sub(last_total_earnings);

		// The new points that will be added to the pool. For every unit of balance that has
		// been earned by the reward pool, we inflate the reward pool points by
		// `primary_pool.total_points`. In effect this allows each, single unit of balance (e.g.
		// plank) to be divvied up pro-rata among delegators based on points.
		//  TODO this needs to be some sort of BigUInt arithmetic
		let new_points = primary_pool.points.saturating_mul(new_earnings);

		// The points of the reward pool after taking into account the new earnings. Notice that
		// this always increases over time except for when we subtract delegator virtual shares
		let current_points = reward_pool.points.saturating_add(new_points);

		// The rewards pool's earnings since the last time this delegator claimed a payout
		let new_earnings_since_last_claim =
			reward_pool.total_earnings.saturating_sub(delegator.reward_pool_total_earnings);
		// The points of the reward pool that belong to the delegator.
		let delegator_virtual_points =
			delegator.points.saturating_mul(new_earnings_since_last_claim);

		let delegator_payout = if delegator_virtual_points.is_zero() || current_points.is_zero() {
			BalanceOf::<T>::zero()
		} else {
			// REMINDER: `saturating_from_rational` panics if denominator is zero
			let delegator_ratio_of_points = FixedU128::saturating_from_rational(
				T::BalanceToU128::convert(delegator_virtual_points),
				T::BalanceToU128::convert(current_points),
			);

			let payout = delegator_ratio_of_points
				.saturating_mul_int(T::BalanceToU128::convert(reward_pool.balance));
			T::U128ToBalance::convert(payout)
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
		primary_pool: &PrimaryPool<T>,
	) -> DispatchResult {
		let reward_pool = RewardPools::<T>::get(&delegator.pool).ok_or_else(|| {
			log!(error, "A reward pool could not be found, this is a system logic error.");
			debug_assert!(false, "A reward pool could not be found, this is a system logic error.");
			Error::<T>::RewardPoolNotFound
		})?;

		let (reward_pool, delegator, delegator_payout) =
			Self::calculate_delegator_payout(primary_pool, reward_pool, delegator)?;

		// Transfer payout to the delegator.
		Self::transfer_reward(
			&reward_pool.account_id,
			delegator_id.clone(),
			delegator.pool,
			delegator_payout,
		)?;

		// Write the updated delegator and reward pool to storage
		RewardPools::insert(delegator.pool, reward_pool);
		Delegators::insert(delegator_id, delegator);

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
	) -> Option<(BalanceOf<T>, BTreeMap<EraIndex, BalanceOf<T>>)> {
		let pool_id = PoolIds::<T>::get(pool_account)?;
		let mut sub_pools = SubPools::<T>::get(pool_id).unwrap_or_default();

		// TODO double check why we do slash_era + 1
		let affected_range = (slash_era + 1)..=apply_era;

		let bonded_balance = T::StakingInterface::bonded_balance(pool_account);

		// Note that this doesn't count the balance in the `no_era` pool
		let unbonding_affected_balance: BalanceOf<T> =
			affected_range.clone().fold(BalanceOf::<T>::zero(), |balance_sum, era| {
				if let Some(unbond_pool) = sub_pools.with_era.get(&era) {
					balance_sum.saturating_add(unbond_pool.balance)
				} else {
					balance_sum
				}
			});
		let total_affected_balance = bonded_balance.saturating_add(unbonding_affected_balance);

		if slash_amount < total_affected_balance {
			// TODO this shouldn't happen as long as MaxBonding pools is greater thant the slash
			// defer duration, which it should implicitly be because we expect it be longer then the
			// UnbondindDuration. TODO clearly document these assumptions
		};

		// Panics if denominator is zero
		let slash_ratio = if total_affected_balance <= Zero::zero() {
			return Some((Zero::zero(), Default::default()))
		} else {
			// REMINDER: `saturating_from_rational` panics if denominator is zero
			FixedU128::saturating_from_rational(
				T::BalanceToU128::convert(slash_amount),
				T::BalanceToU128::convert(total_affected_balance),
			)
		};

		let slash_multiplier = FixedU128::one().saturating_sub(slash_ratio);

		let unlock_chunk_balances: BTreeMap<_, _> = affected_range
			.filter_map(|era| {
				if let Some(mut unbond_pool) = sub_pools.with_era.get_mut(&era) {
					let pre_slash_balance = T::BalanceToU128::convert(unbond_pool.balance);
					let after_slash_balance = T::U128ToBalance::convert(
						slash_multiplier.saturating_mul_int(pre_slash_balance),
					);
					unbond_pool.balance = after_slash_balance;

					Some((era, after_slash_balance))
				} else {
					None
				}
			})
			.collect();

		SubPools::<T>::insert(pool_id, sub_pools);

		let slashed_bonded_pool_balance = {
			let pre_slash_balance = T::BalanceToU128::convert(bonded_balance);
			T::U128ToBalance::convert(slash_multiplier.saturating_mul_int(pre_slash_balance))
		};

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
	) -> Option<(Self::Balance, BTreeMap<EraIndex, Self::Balance>)> {
		Self::do_slash(pool_account, slash_amount, slash_era, apply_era)
	}
}

//
// - slashing
// - tests
// - force pool creation
// - rebond_rewards
// - force pool update
// - force pool delete?

// impl<T: Config> Pallet<T> {
// 	do_create_pool(
// 		creator: T::AccountId,
// 		targets: Vec<T::AccountId>,
// 		amount: BalanceOf<T>
// 	) -> DispatchResult {
// Create Stash/Controller account based on parent block hash, block number, and extrinsic index
// Create Reward Pool account based on Stash/Controller account
// Move `amount` to the stash / controller account
// Read in `bondable` - the free balance that we can bond after any neccesary reserv etc

// Bond with `amount`, ensuring that it is over the minimum bond (by min)
// (might has need to ensure number of targets etc is valid)

// Generate a pool id (look at how assets IDs are generated for inspiration)

//
// 	}
// }
