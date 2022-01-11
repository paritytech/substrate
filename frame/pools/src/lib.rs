//! Delegation pools for nominating in `pallet-staking`.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	ensure,
	pallet_prelude::*,
	traits::{Currency, ExistenceRequirement},
};
use scale_info::TypeInfo;
use sp_arithmetic::{traits::Saturating, FixedPointNumber, FixedU128};
use sp_runtime::traits::{AtLeast32BitUnsigned, Convert, One, Zero};

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
type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type SharesOf<T> = BalanceOf<T>;

pub trait NominationProviderTrait<Balance, AccountId, EraIndex> {
	/// The minimum amount necessary to bond to be a nominator. This does not necessarily mean the
	/// nomination will be counted in an election, but instead just enough to be stored as a
	/// nominator (e.g. in the bags-list of polkadot)
	fn minimum_bond() -> Balance;

	/// The current era for the elections system
	fn current_era() -> EraIndex;

	/// Wether or not the elections system has an ongoing election. If there is an ongoing election
	/// it is assumed that any new pool joiner's funds will not start earning rewards until the
	/// following era.
	fn is_ongoing_election() -> bool;

	fn bond_extra(controller: &AccountId, extra: Balance) -> DispatchResult;
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Delegator<T: Config> {
	pool: PoolId,
	shares: SharesOf<T>,
	last_paid_out_era: T::EraIndex,

	/// The reward pools total payout ever the last time this delegator claimed a payout.
	total_payout_ever: BalanceOf<T>, // Probably needs to be some typ eof BigUInt
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct Pool<T: Config> {
	shares: SharesOf<T>,
	// The _Stash_ AND _Controller_ account for the pool.
	account_id: T::AccountId,
}

impl<T: Config> Pool<T> {
	fn shares_to_issue(&self, new_funds: BalanceOf<T>, pool_free: BalanceOf<T>) -> SharesOf<T> {
		let shares_per_balance = {
			let balance = T::BalanceToU128::convert(pool_free);
			let shares = T::BalanceToU128::convert(self.shares);
			FixedU128::saturating_from_rational(shares, balance)
		};
		let new_funds = T::BalanceToU128::convert(new_funds);

		T::U128ToBalance::convert(shares_per_balance.saturating_mul_int(new_funds))
	}
}

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct RewardPool<T: Config> {
	// TODO look into using the BigUInt
	/// The balance of this reward pool after the last claimed payout.
	balance: BalanceOf<T>,
	/// The shares of this reward pool after the last claimed payout
	shares: BalanceOf<T>,
	/// The total earnings ever of this reward pool after the last claimed payout. I.E. the sum of
	/// all incoming balance.
	total_earnings: BalanceOf<T>,
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
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Weight information for extrinsics in this pallet.
		// type WeightInfo: weights::WeightInfo;

		/// The nominating balance.
		type Currency: Currency<Self::AccountId>;

		// Infallible method for converting `Currency::Balance` to `u128`.
		type BalanceToU128: Convert<BalanceOf<Self>, u128>;

		// Infallible method for converting `u128` to `Currency::Balance`.
		type U128ToBalance: Convert<u128, BalanceOf<Self>>;

		/// The type for unique era indexes. Likely comes from what implements `NominationProvider`.
		type EraIndex: Member
			+ Parameter
			+ AtLeast32BitUnsigned
			+ Default
			+ Copy
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen
			+ TypeInfo;

		/// The interface for nominating.
		type NominationProvider: NominationProviderTrait<
			BalanceOf<Self>,
			Self::AccountId,
			Self::EraIndex,
		>;

		// MaxPools
	}

	/// Active delegators.
	#[pallet::storage]
	pub(crate) type Delegators<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, Delegator<T>>;

	/// Bonded pools.
	#[pallet::storage]
	pub(crate) type PrimaryPools<T: Config> = CountedStorageMap<_, Twox64Concat, PoolId, Pool<T>>;

	/// Reward pools. This is where there rewards for each pool accumulate. When a delegators payout
	/// is claimed, the balance comes out fo the reward pool.
	#[pallet::storage]
	pub(crate) type RewardPools<T: Config> =
		CountedStorageMap<_, Twox64Concat, PoolId, RewardPool<T>>;

	// /// Groups of unbonding pools. Each group of unbonding pools belongs to a primary pool,
	// /// hence the name sub-pools.
	// #[pallet::storage]
	// type SubPools = CountedStorageMap<_, PoolId, SubPools, _>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		Joined { delegator: T::AccountId, pool: PoolId, bonded: BalanceOf<T> },
	}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// The given pool id does not exist.
		PoolNotFound,
		/// The given account is not a delegator.
		DelegatorNotFound,
		/// The account is already delegating in another pool. An account may only belong to one
		/// pool at a time.
		AccountBelongsToOtherPool,
		/// The pool has insufficient balance to bond as a nominator.
		InsufficientBond,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Join a pre-existing pool. Note that an account can only be a member of a single pool.
		#[pallet::weight(666)]
		pub fn join(origin: OriginFor<T>, amount: BalanceOf<T>, target: PoolId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// if a delegator already exists that means they already belong to a pool
			ensure!(!Delegators::<T>::contains_key(&who), Error::<T>::AccountBelongsToOtherPool);

			// Ensure that the `target` pool exists
			let mut primary_pool =
				PrimaryPools::<T>::get(target).ok_or(Error::<T>::PoolNotFound)?;
			// And that `amount` will meet the minimum bond
			let old_free_balance = T::Currency::free_balance(&primary_pool.account_id);
			ensure!(
				old_free_balance.saturating_add(amount) >= T::NominationProvider::minimum_bond(),
				Error::<T>::InsufficientBond
			);

			// Transfer the funds to be bonded from `who` to the pools account so the pool can then
			// go bond them.
			// Note importantly that we can't error after this transfer goes through.
			// TODO I assume this does proper keep alive checks etc but need to double check
			T::Currency::transfer(
				&who,
				&primary_pool.account_id,
				amount,
				ExistenceRequirement::KeepAlive,
			)?;
			// this should now include the transferred balance
			let new_free_balance = T::Currency::free_balance(&primary_pool.account_id);
			// we get the exact amount we can bond extra
			let exact_amount_to_bond = new_free_balance.saturating_sub(old_free_balance);

			// issue the new shares
			let new_shares = primary_pool.shares_to_issue(exact_amount_to_bond, old_free_balance);
			primary_pool.shares = primary_pool.shares.saturating_add(new_shares);
			let delegator = {
				// Determine the last paid out era. Note that in the reward calculations we will
				// start attributing rewards to this delegator in `last_paid_out_era  + 1`.
				let last_paid_out_era = if T::NominationProvider::is_ongoing_election() {
					// If there is an ongoing election the new funds will start to help generating
					// rewards in current_era + 2.
					T::NominationProvider::current_era().saturating_add(One::one())
				} else {
					// If there is no ongoing election, the new funds will start help generating
					// generating rewards in current_era + 1.
					T::NominationProvider::current_era()
				};

				Delegator::<T> {
					pool: target,
					shares: new_shares,
					last_paid_out_era,
					total_payout_ever: Zero::zero(),
				}
			};

			// Do bond extra
			T::NominationProvider::bond_extra(&primary_pool.account_id, exact_amount_to_bond)?;

			// Write the pool and delegator to storage
			Delegators::insert(who.clone(), delegator);
			PrimaryPools::insert(target, primary_pool);

			// And finally emit an event to confirm the exact amount bonded
			Self::deposit_event(Event::<T>::Joined {
				delegator: who,
				pool: target,
				bonded: exact_amount_to_bond,
			});

			Ok(())
		}

		// fn unbond()

		// /// Claim a payout for a delegator can use this to claim their payout based on the
		// rewards /// that the pool has accumulated since their last claimed payout (OR since
		// joining if this /// is there for). The payout will go to the delegators account.
		// ///
		// /// This extrinsic is permisionless in the sense that any account can call it for any
		// /// delegator in the system.
		// #[pallet::weight(666)]
		// pub fn claim_payout_other(origin: OriginFor<T>, delegator: T::AccountId) ->
		// DispatchResult { 	ensure_signed(origin)?;

		// 	let delegator = Delegators::<T>::get(&delegator).ok_or(Error::<T>::DelegatorNotFound)?;

		// 	let reward_pool = RewardPools::<T>::get(&delegator.pool).unwrap_or_else(|| {
		// 		// The reward pool does not yet exist; this must be the first claimed payout for
		// 		// the pool, so we must make the reward pool
		// 		RewardPool { balance: Zero::zero(), shares: Zero::zero(), total_earnings: Zero::zero() }
		// 	});

		// 	Ok(())
		// }
	}
}

// impl<T: Config> Pallet<T> {
// 	do_create_pool(
// 		creator: T::AccountId,
// 		targets: Vec<T::AccountId>,
// 		amount: BalanceOf<T>
// 	) -> DispatchResult {
// Create Stash/Controller account based on parent block hash, block number, and extrinsic index
// Create Reward Pool account based on Stash/Controller account

// Bond with `amount`, ensuring that it is over the minimum bond (by min)

//
// 	}
// }
