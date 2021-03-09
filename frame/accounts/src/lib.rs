#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{
	vec::Vec,
	marker::PhantomData,
};
use frame_support::{
	sp_runtime::{RuntimeDebug, traits::{StoredMapError, One}},
	traits::{HandleLifetime, StoredMap, OnNewAccount, OnKilledAccount, ReferencedAccount, BasicAccount},
};
use codec::{Encode, Decode, FullCodec};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

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
	/// until this and `sufficients` are both zero.
	pub providers: RefCount,
	/// The number of modules that allow this account to exist for their own purposes only. The
	/// account may not be reaped until this and `providers` are both zero.
	pub sufficients: RefCount,
	/// The additional data that belongs to this account. Used to store the balance(s) in a lot of
	/// chains.
	pub data: AccountData,
}

/// Reference status; can be either referenced or unreferenced.
#[derive(RuntimeDebug)]
pub enum RefStatus {
	Referenced,
	Unreferenced,
}

/// Some resultant status relevant to incrementing a provider/self-sufficient reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum IncRefStatus {
	/// Account was created.
	Created,
	/// Account already existed.
	Existed,
}

/// Some resultant status relevant to decrementing a provider/self-sufficient reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum DecRefStatus {
	/// Account was destroyed.
	Reaped,
	/// Account still exists.
	Exists,
}

/// Some resultant status relevant to decrementing a provider reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum DecRefError {
	/// Account cannot have the last provider reference removed while there is a consumer.
	ConsumerRemaining,
}

/// Some resultant status relevant to incrementing a consumer reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum IncRefError {
	/// Account cannot introduce a consumer while there are no providers.
	NoProviders,
}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;

	use frame_system::pallet_prelude::*;
	use frame_support::pallet_prelude::*;

	/// System configuration trait. Implemented by runtime.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Data to be associated with an account (other than nonce/transaction counter, which this
		/// pallet does regardless).
		type AccountData: Member + FullCodec + Clone + Default;

		/// Handler for when a new account has just been created.
		type OnNewAccount: OnNewAccount<Self::AccountId>;

		/// A function that is invoked when an account has been determined to be dead.
		///
		/// All resources should be cleaned up associated with the given account.
		type OnKilledAccount: OnKilledAccount<Self::AccountId>;
	}

	/// Event for the Accounts pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	#[pallet::metadata(T::AccountId = "AccountId")]
	pub enum Event<T: Config> {
		/// A new \[account\] was created.
		NewAccount(T::AccountId),
		/// An \[account\] was reaped.
		KilledAccount(T::AccountId),
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

	impl<T: Config> Pallet<T> {
		/// An account is being created.
		pub(crate) fn on_created_account(who: T::AccountId, _a: &mut AccountInfo<T::Index, T::AccountData>) {
			T::OnNewAccount::on_new_account(&who);
			Self::deposit_event(Event::NewAccount(who));
		}

		/// Do anything that needs to be done after an account has been killed.
		pub(crate) fn on_killed_account(who: T::AccountId) {
			T::OnKilledAccount::on_killed_account(&who);
			Self::deposit_event(Event::KilledAccount(who));
		}
	}
}

/// Event handler which registers a provider when created.
pub struct Provider<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for Provider<T> {
	fn created(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::inc_providers(t);
		Ok(())
	}
	fn killed(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::dec_providers(t)
			.map(|_| ())
			.or_else(|e| match e {
				DecRefError::ConsumerRemaining => Err(StoredMapError::ConsumerRemaining),
			})
	}
}

/// Event handler which registers a self-sufficient when created.
pub struct SelfSufficient<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for SelfSufficient<T> {
	fn created(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::inc_sufficients(t);
		Ok(())
	}
	fn killed(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::dec_sufficients(t);
		Ok(())
	}
}

/// Event handler which registers a consumer when created.
pub struct Consumer<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for Consumer<T> {
	fn created(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::inc_consumers(t)
			.map_err(|e| match e {
				IncRefError::NoProviders => StoredMapError::NoProviders
			})
	}
	fn killed(t: &T::AccountId) -> Result<(), StoredMapError> {
		Module::<T>::dec_consumers(t);
		Ok(())
	}
}

/// Implement StoredMap for a simple single-item, provide-when-not-default system. This works fine
/// for storing a single item which allows the account to continue existing as long as it's not
/// empty/default.
///
/// Anything more complex will need more sophisticated logic.
impl<T: Config> StoredMap<T::AccountId, <T as Config>::AccountData> for Pallet<T> {
	fn get(k: &T::AccountId) -> <T as Config>::AccountData {
		Account::<T>::get(k).data
	}

	fn try_mutate_exists<R, E: From<StoredMapError>>(
		k: &T::AccountId,
		f: impl FnOnce(&mut Option<<T as Config>::AccountData>) -> Result<R, E>,
	) -> Result<R, E> {
		let account = Account::<T>::get(k);
		let was_providing = is_providing(&account.data);
		let mut some_data = if was_providing { Some(account.data) } else { None };
		let result = f(&mut some_data)?;
		let is_providing = some_data.is_some();
		if !was_providing && is_providing {
			Self::inc_providers(k);
		} else if was_providing && !is_providing {
			match Self::dec_providers(k) {
				Err(DecRefError::ConsumerRemaining) => Err(StoredMapError::ConsumerRemaining)?,
				Ok(DecRefStatus::Reaped) => return Ok(result),
				Ok(DecRefStatus::Exists) => {
					// Update value as normal...
				}
			}
		} else if !was_providing && !is_providing {
			return Ok(result)
		}
		Account::<T>::mutate(k, |a| a.data = some_data.unwrap_or_default());
		Ok(result)
	}
}

fn is_providing<T: Default + Eq>(d: &T) -> bool {
	d != &T::default()
}

impl<T: Config> BasicAccount<T::AccountId, T::Index> for Pallet<T> {
	type AccountInfo = AccountInfo<T::Index, <T as Config>::AccountData>;

	/// Return whether an account exists in storage.
	fn account_exists(who: &T::AccountId) -> bool {
		Account::<T>::contains_key(who)
	}

	/// Return the data for an account
	fn get(who: &T::AccountId) -> Self::AccountInfo {
		Account::<T>::get(who)
	}

	/// Retrieve the account transaction counter from storage.
	fn account_nonce(who: &T::AccountId) -> T::Index {
		Account::<T>::get(who).nonce
	}

	/// Increment a particular account's nonce by 1.
	fn inc_account_nonce(who: &T::AccountId) {
		Account::<T>::mutate(who, |a| a.nonce += T::Index::one());
	}

	/// Return the storage key for an account.
	fn hashed_key_for(who: &T::AccountId) -> Vec<u8> {
		Account::<T>::hashed_key_for(who)
	}
}

impl<T: Config> ReferencedAccount<T::AccountId, T::Index> for Pallet<T> {
	type RefCount = RefCount;
	type IncRefStatus = IncRefStatus;
	type DecRefStatus = DecRefStatus;
	type IncRefError = IncRefError;
	type DecRefError = DecRefError;

	/// Increment the provider reference counter on an account.
	fn inc_providers(who: &T::AccountId) -> IncRefStatus {
		Account::<T>::mutate(who, |a| if a.providers == 0 && a.sufficients == 0 {
			// Account is being created.
			a.providers = 1;
			Self::on_created_account(who.clone(), a);
			IncRefStatus::Created
		} else {
			a.providers = a.providers.saturating_add(1);
			IncRefStatus::Existed
		})
	}

	/// Decrement the provider reference counter on an account.
	///
	/// This *MUST* only be done once for every time you called `inc_providers` on `who`.
	fn dec_providers(who: &T::AccountId) -> Result<DecRefStatus, DecRefError> {
		Account::<T>::try_mutate_exists(who, |maybe_account| {
			if let Some(mut account) = maybe_account.take() {
				if account.providers == 0 {
					// Logic error - cannot decrement beyond zero.
					log::error!(
						target: "runtime::system",
						"Logic error: Unexpected underflow in reducing provider",
					);
					account.providers = 1;
				}
				match (account.providers, account.consumers, account.sufficients) {
					(1, 0, 0) => {
						// No providers left (and no consumers) and no sufficients. Account dead.

						Module::<T>::on_killed_account(who.clone());
						Ok(DecRefStatus::Reaped)
					}
					(1, c, _) if c > 0 => {
						// Cannot remove last provider if there are consumers.
						Err(DecRefError::ConsumerRemaining)
					}
					(x, _, _) => {
						// Account will continue to exist as there is either > 1 provider or
						// > 0 sufficients.
						account.providers = x - 1;
						*maybe_account = Some(account);
						Ok(DecRefStatus::Exists)
					}
				}
			} else {
				log::error!(
					target: "runtime::system",
					"Logic error: Account already dead when reducing provider",
				);
				Ok(DecRefStatus::Reaped)
			}
		})
	}

	/// Increment the self-sufficient reference counter on an account.
	fn inc_sufficients(who: &T::AccountId) -> IncRefStatus {
		Account::<T>::mutate(who, |a| if a.providers + a.sufficients == 0 {
			// Account is being created.
			a.sufficients = 1;
			Self::on_created_account(who.clone(), a);
			IncRefStatus::Created
		} else {
			a.sufficients = a.sufficients.saturating_add(1);
			IncRefStatus::Existed
		})
	}

	/// Decrement the self-sufficient reference counter on an account.
	///
	/// This *MUST* only be done once for every time you called `inc_sufficients` on `who`.
	fn dec_sufficients(who: &T::AccountId) -> DecRefStatus {
		Account::<T>::mutate_exists(who, |maybe_account| {
			if let Some(mut account) = maybe_account.take() {
				if account.sufficients == 0 {
					// Logic error - cannot decrement beyond zero.
					log::error!(
						target: "runtime::system",
						"Logic error: Unexpected underflow in reducing sufficients",
					);
				}
				match (account.sufficients, account.providers) {
					(0, 0) | (1, 0) => {
						Module::<T>::on_killed_account(who.clone());
						DecRefStatus::Reaped
					}
					(x, _) => {
						account.sufficients = x - 1;
						*maybe_account = Some(account);
						DecRefStatus::Exists
					}
				}
			} else {
				log::error!(
					target: "runtime::system",
					"Logic error: Account already dead when reducing provider",
				);
				DecRefStatus::Reaped
			}
		})
	}

	/// The number of outstanding provider references for the account `who`.
	fn providers(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).providers
	}

	/// The number of outstanding sufficient references for the account `who`.
	fn sufficients(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).sufficients
	}

	/// The number of outstanding provider and sufficient references for the account `who`.
	fn reference_count(who: &T::AccountId) -> RefCount {
		let a = Account::<T>::get(who);
		a.providers + a.sufficients
	}

	/// Increment the reference counter on an account.
	///
	/// The account `who`'s `providers` must be non-zero or this will return an error.
	fn inc_consumers(who: &T::AccountId) -> Result<(), IncRefError> {
		Account::<T>::try_mutate(who, |a| if a.providers > 0 {
			a.consumers = a.consumers.saturating_add(1);
			Ok(())
		} else {
			Err(IncRefError::NoProviders)
		})
	}

	/// Decrement the reference counter on an account. This *MUST* only be done once for every time
	/// you called `inc_consumers` on `who`.
	fn dec_consumers(who: &T::AccountId) {
		Account::<T>::mutate(who, |a| if a.consumers > 0 {
			a.consumers -= 1;
		} else {
			log::error!(
				target: "runtime::system",
				"Logic error: Unexpected underflow in reducing consumer",
			);
		})
	}

	/// The number of outstanding references for the account `who`.
	fn consumers(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).consumers
	}

	/// True if the account has some outstanding references.
	fn is_provider_required(who: &T::AccountId) -> bool {
		Account::<T>::get(who).consumers != 0
	}
}
