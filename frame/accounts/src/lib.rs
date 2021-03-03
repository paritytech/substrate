#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::RuntimeDebug;
use codec::{Encode, Decode, FullCodec};

/// Type used to encode the number of references an account has.
pub type RefCount = u32;

/// Information of an account.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct AccountInfo<Index, AccountData> {
	/// The number of transactions this account has sent.
	pub nonce: Index,
	/// The number of other modules that currently depend on this account's existence. The account
	/// cannot be reaped until this is zero.
	pub consumers: RefCount,
	/// The number of other modules that allow this account to exist. The account may not be reaped
	/// until this is zero.
	pub providers: RefCount,
	/// The additional data that belongs to this account. Used to store the balance(s) in a lot of
	/// chains.
	pub data: AccountData,
}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;

	use frame_system::pallet_prelude::*;
	use frame_support::pallet_prelude::*;
	use frame_support::traits::AccountApi;
	use sp_runtime::traits::One;

	/// System configuration trait. Implemented by runtime.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Data to be associated with an account (other than nonce/transaction counter, which this
		/// pallet does regardless).
		type AccountData: Member + FullCodec + Clone + Default;
	}

	/// The full account information for a particular account ID.
	#[pallet::storage]
	#[pallet::getter(fn account)]
	pub type Account<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		AccountInfo<T::Index, <T as Config>::AccountData>,
		ValueQuery,
	>;

	#[pallet::pallet]
	#[pallet::generate_store(pub (super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	impl<T: Config> AccountApi for Pallet<T> {
		type AccountId = <T as frame_system::Config>::AccountId;
		type Index = <T as frame_system::Config>::Index;

		/// Return whether an account exists in storage.
		fn account_exists(who: &Self::AccountId) -> bool {
			Account::<T>::contains_key(who)
		}

		/// Retrieve the account transaction counter from storage.
		fn account_nonce(who: Self::AccountId) -> Self::Index {
			Account::<T>::get(who).nonce
		}

		/// Increment a particular account's nonce by 1.
		fn inc_account_nonce(who: Self::AccountId) {
			Account::<T>::mutate(who, |a| a.nonce += Self::Index::one());
		}
	}
}
