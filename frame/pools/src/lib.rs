//! Delegation pools for nominating in `pallet-staking`.

#![cfg_attr(not(feature = "std"), no_std)]

use scale_info::TypeInfo;
use sp_arithmetic::{FixedU128, FixedPointNumber};
use frame_support::{ensure, pallet_prelude::*, traits::{Currency, ExistenceRequirement}};
use sp_arithmetic::traits::Saturating;


pub use pallet::*;
pub(crate) const LOG_TARGET: &'static str = "runtime::pools";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] 👜", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
		)
	};
}

type PoolId = u32;
type Shares = u128;
type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

pub trait NominationProviderTrait {}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct Delegator {
	pool: PoolId,
	shares: Shares,
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Pool<T: Config> {
	shares: Shares,
	balance: BalanceOf<T>,
	account_id: T::AccountId,
}

impl<T: Config> Pool<T> {
// 	/// Number of shares per balance that can be exchanged for `Balance`.
// 	///
// 	/// Typically used upon entering.
	fn shares_per_balance(&self) -> FixedU128 {
		let balance_u128: u128 = self.balance.try_into().unwrap_or_default();
		let shares_u128: u128 = self.shares.try_into().unwrap_or_default();
		FixedU128::saturating_from_rational(shares_u128, balance_u128)
	}

	fn shares_to_issue(&self, new_funds: BalanceOf<T>) -> Shares {
		let new_funds_u128: u128 = new_funds.try_into().unwrap_or_default();
		self.shares_per_balance().saturating_mul_int(new_funds_u128
		)
	}
}

// #[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
// #[codec(mel_bound(T: Config))]
// struct SubPools<T: frame_system::Config> {
// 	shares: Shares,
// 	balance: Balance,
// 	account_id: T::AccountId,
// }

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
		// type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Weight information for extrinsics in this pallet.
		// type WeightInfo: weights::WeightInfo;

		/// The interface for nominating.
		type NominationProvider: NominationProviderTrait;

		/// The nominating balance.
		type Currency: Currency<Self::AccountId>;

		// TODO use this for conversion
		// type BalanceToU128: Convert<BalanceOf<T>, U128>;

		// MaxPools
	}

	/// Bonded pools.
	#[pallet::storage]
	pub(crate) type PrimaryPools<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, Pool<T>>;

	/// Active delegators.
	#[pallet::storage]
	pub(crate) type Delegators<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator>;

	// /// Groups of unbonding pools. Each group of unbonding pools belongs to a primary pool,
	// /// hence the name sub-pools.
	// #[pallet::storage]
	// type SubPools = CountedStorageMap<_, PoolId, SubPools, _>;

	// #[pallet::event]
	// #[pallet::generate_deposit(pub(crate) fn deposit_event)]
	// pub enum Event {}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// The given pool id does not exist.
		PoolNotFound,
		/// The account is already delegating in another pool. An account may only belong to one
		/// pool at a time.
		AccountBelongsToOtherPool,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(666)]
		pub fn join(origin: OriginFor<T>, amount: BalanceOf<T>, target: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			// Ensure that the `target` pool exists
			let mut primary_pool = PrimaryPools::<T>::get(target).ok_or(Error::<T>::PoolNotFound)?;

			// Ensure that the delegator does not back o

			let old_free_balance = T::Currency::free_balance(&primary_pool.account_id);

			// Ensure that `who` has `amount` transferable and do the actual transfer
			T::Currency::transfer(
				&who,
				&primary_pool.account_id,
				amount,
				ExistenceRequirement::KeepAlive,
			)?;

			// this should now include the transferred balance;
			primary_pool.balance = T::Currency::free_balance(&primary_pool.account_id);

			let actual_amount_to_bond = primary_pool.balance.saturating_sub(old_free_balance);

			let new_shares = primary_pool.shares_to_issue(amount);
			primary_pool.shares = primary_pool.shares.saturating_add(new_shares);
			// TODO: maybe some other checks to ensure that the pool is in an ok state

			// calculate the amount of shares to issue

			// Bond or BondExtra, depending on the pools balacn

			// write the pool to storage

			Ok(())
		}

		// pub fn force_create_pool(origin: ) -> DispatchResult {

		// }
	}
}
