// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_runtime::{
	traits::{StaticLookup, Dispatchable, SaturatedConversion, Zero, CheckedAdd, CheckedMul},
	DispatchError, DispatchResult
};
use codec::{Encode, Decode};

use frame_support::{
	decl_module, decl_event, decl_storage, decl_error, ensure,
	Parameter, RuntimeDebug,
	weights::{
		SimpleDispatchInfo, GetDispatchInfo, PaysFee, WeighData, Weight,
		ClassifyDispatch, DispatchClass
	},
	traits::{Currency, ReservableCurrency, Get},
};
use frame_system::{self as system, ensure_signed, ensure_root};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The base amount of currency needed to reserve for creating a recovery configuration.
	///
	/// This is held for an additional storage item whose value size is
	/// TODO bytes.
	type ConfigDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per additional user when creating a recovery configuration.
	///
	/// This is held for adding TODO bytes more into a pre-existing storage value.
	type FriendDepositFactor: Get<BalanceOf<Self>>;

	/// The maximum amount of friends allowed in a recovery configuration.
	type MaxFriends: Get<u16>;

	/// The base amount of currency needed to reserve for starting a recovery.
	///
	/// This is held for an additional storage item whose value size is
	/// TODO bytes.
	type RecoveryDeposit: Get<BalanceOf<Self>>;
}

/// An active recovery process.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct ActiveRecovery<BlockNumber, Balance, AccountId> {
	/// The block number when the recovery process started.
	created: BlockNumber,
	/// The amount held in reserve of the `depositor`,
	/// To be returned once this recovery process is closed.
	deposit: Balance,
	/// The friends which have vouched so far. Always sorted.
	friends: Vec<AccountId>,
}

/// Configuration for recovering an account.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct RecoveryConfig<BlockNumber, Balance, AccountId> {
	/// The minimum number of blocks since the start of the recovery process before the account
	/// can be recovered.
	delay_period: BlockNumber,
	/// The amount held in reserve of the `depositor`,
	/// to be returned once this configuration is removed.
	deposit: Balance,
	/// The list of friends which can help recover an account. Always sorted.
	friends: Vec<AccountId>,
	/// The number of approving friends needed to recover an account.
	threshold: u16,
}

decl_storage! {
	trait Store for Module<T: Trait> as Recovery {
		/// The set of recoverable accounts and their recovery configuration.
		pub Recoverable get(fn recovery_config):
			map T::AccountId => Option<RecoveryConfig<T::BlockNumber, BalanceOf<T>, T::AccountId>>;
		/// Active recovery attempts.
		///
		/// First account is the account to be recovered, and the second account
		/// is the user trying to recover the account.
		pub ActiveRecoveries get(fn active_recovery):
			double_map hasher(twox_64_concat) T::AccountId, twox_64_concat(T::AccountId) =>
			Option<ActiveRecovery<T::BlockNumber, BalanceOf<T>, T::AccountId>>;
		/// The final list of recovered accounts.
		///
		/// Map from the recovered account to the user who can access it.
		pub Recovered get(fn recovered_account): map T::AccountId => Option<T::AccountId>;
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
	{
		/// A recovery process has been set up for an account
		RecoveryCreated(AccountId),
		/// A recovery process has been initiated by account_1 for account_2
		RecoveryInitiated(AccountId, AccountId),
		/// A recovery process by account_1 for account_2 has been vouched for by account_3
		RecoveryVouched(AccountId, AccountId, AccountId),
		/// Account_1 has recovered account_2
		AccountRecovered(AccountId, AccountId),
		/// A recovery process has been removed for an account
		RecoveryRemoved(AccountId),
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// User is not allowed to make a call on behalf of this account
		NotAllowed,
		/// Threshold must be greater than zero
		ZeroThreshold,
		/// Friends list must be greater than zero and threshold
		NotEnoughFriends,
		/// Friends list must be less than max friends
		MaxFriends,
		/// Friends list must be sorted and free of duplicates
		NotSorted,
		/// This account is not set up for recovery
		NotRecoverable,
		/// This account is already set up for recovery
		AlreadyRecoverable,
		/// A recovery process has already started for this account
		AlreadyStarted,
		/// A recovery process has not started for this rescuer
		NotStarted,
		/// This account is not a friend who can vouch
		NotFriend,
		/// The friend must wait until the delay period to vouch for this recovery
		DelayPeriod,
		/// This user has already vouched for this recovery
		AlreadyVouched,
		/// The threshold for recovering this account has not been met
		Threshold,
		/// There are still active recovery attempts that need to be closed
		StillActive,
		/// There was an overflow in a calculation
		Overflow,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;
		
		/// Send a call through a recovered account.
		fn as_recovered(origin, account: T::AccountId, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// Check `who` is allowed to make a call on behalf of `account`
			ensure!(Self::recovered_account(&account) == Some(who), Error::<T>::NotAllowed);
			call.dispatch(frame_system::RawOrigin::Signed(account).into())
		}
		
		/// Allow Sudo to bypass the recovery process and set an alias account.
		fn set_recovered_account(origin, lost: T::AccountId, rescuer: T::AccountId) {
			ensure_root(origin)?;

			// Create the recovery storage item.
			<Recovered<T>>::insert(&lost, &rescuer);

			Self::deposit_event(RawEvent::AccountRecovered(rescuer, lost));
		}
		
		/// Create a recovery process for your account.
		fn create_recovery(origin,
			friends: Vec<T::AccountId>,
			threshold: u16,
			delay_period: T::BlockNumber
		) {
			let who = ensure_signed(origin)?;
			// Check account is not already set up for recovery
			ensure!(!<Recoverable<T>>::exists(&who), Error::<T>::AlreadyRecoverable);
			// Check user input is valid
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			ensure!(!friends.is_empty(), Error::<T>::NotEnoughFriends);
			ensure!(threshold as usize <= friends.len(), Error::<T>::NotEnoughFriends);
			let max_friends = T::MaxFriends::get() as usize;
			ensure!(friends.len() <= max_friends, Error::<T>::MaxFriends);
			ensure!(Self::is_sorted(&friends), Error::<T>::NotSorted);

			// Total deposit is base fee + number of friends * factor fee
			let friend_deposit = T::FriendDepositFactor::get()
				.checked_mul(&friends.len().saturated_into())
				.ok_or(Error::<T>::Overflow)?;
			let total_deposit = T::ConfigDepositBase::get()
				.checked_add(&friend_deposit)
				.ok_or(Error::<T>::Overflow)?;
			// Reserve the deposit
			T::Currency::reserve(&who, total_deposit)?;

			// Create the recovery configuration
			let recovery_config = RecoveryConfig {
				delay_period,
				deposit: total_deposit,
				friends,
				threshold,
			};

			<Recoverable<T>>::insert(&who, recovery_config);

			Self::deposit_event(RawEvent::RecoveryCreated(who));
		}
		
		fn initiate_recovery(origin, account: T::AccountId) {
			let who = ensure_signed(origin)?;
			// Check that the account is recoverable
			ensure!(<Recoverable<T>>::exists(&account), Error::<T>::NotRecoverable);
			// Check that the recovery process has not already been started
			ensure!(!<ActiveRecoveries<T>>::exists(&account, &who), Error::<T>::AlreadyStarted);
			// Take recovery deposit
			let recovery_deposit = T::RecoveryDeposit::get();
			T::Currency::reserve(&who, recovery_deposit)?;
			// Create an active recovery status
			let recovery_status = ActiveRecovery {
				created: <system::Module<T>>::block_number(),
				deposit: recovery_deposit,
				friends: vec![],
			};

			<ActiveRecoveries<T>>::insert(&account, &who, recovery_status);

			Self::deposit_event(RawEvent::RecoveryInitiated(who, account));
		}
		
		fn vouch_recovery(origin, lost: T::AccountId, rescuer: T::AccountId) {
			let who = ensure_signed(origin)?;

			// Check that the lost account is recoverable
			if let Some(recovery_config) = Self::recovery_config(&lost) {
				// Check that the recovery process has been initiated for this rescuer
				if let Some(mut active_recovery) = Self::active_recovery(&lost, &rescuer) {
					// Make sure the voter is a friend
					ensure!(Self::is_friend(&recovery_config.friends, &who), Error::<T>::NotFriend);
					// Either insert the vouch, or return an error that the user already vouched.
					match active_recovery.friends.binary_search(&who) {
						Ok(_pos) => Err(Error::<T>::AlreadyVouched)?,
						Err(pos) => active_recovery.friends.insert(pos, who.clone()),
					}

					// Update storage with the latest details
					<ActiveRecoveries<T>>::insert(&lost, &rescuer, active_recovery);

					Self::deposit_event(RawEvent::RecoveryVouched(rescuer, lost, who));
				} else {
					Err(Error::<T>::NotStarted)?
				}
			} else {
				Err(Error::<T>::NotRecoverable)?
			}
		}
		
		/// Allow a rescuer to claim their recovered account.
		fn claim_recovery(origin, account: T::AccountId) {
			let who = ensure_signed(origin)?;
			// Check that the lost account is recoverable
			if let Some(recovery_config) = Self::recovery_config(&account) {
				// Check that the recovery process has been initiated for this rescuer
				if let Some(active_recovery) = Self::active_recovery(&account, &who) {
					// Make sure the delay period has passed
					let current_block_number = <system::Module<T>>::block_number();
					let recoverable_block_number = active_recovery.created
						.checked_add(&recovery_config.delay_period)
						.ok_or(Error::<T>::Overflow)?;
					ensure!(recoverable_block_number <= current_block_number, Error::<T>::DelayPeriod);
					// Make sure the threshold is met
					ensure!(
						recovery_config.threshold as usize <= active_recovery.friends.len(),
						Error::<T>::Threshold
					);

					// Create the recovery storage item
					<Recovered<T>>::insert(&account, &who);

					Self::deposit_event(RawEvent::AccountRecovered(who, account));
				} else {
					Err(Error::<T>::NotStarted)?
				}
			} else {
				Err(Error::<T>::NotRecoverable)?
			}
		}
		
		/// Close an active recovery process.
		///
		/// Can only be called by the account trying to be recovered.
		fn close_recovery(origin, rescuer: T::AccountId) {
			let who = ensure_signed(origin)?;
			if let Some(active_recovery) = <ActiveRecoveries<T>>::take(&who, &rescuer) {
				// Move the reserved funds from the rescuer to the rescued account.
				// Acts like a slashing mechanism for those who try to maliciously recover accounts.
				let _ = T::Currency::repatriate_reserved(&rescuer, &who, active_recovery.deposit);
			} else {
				Err(Error::<T>::NotStarted)?
			}
		}
		
		/// Remove the recovery process for your account.
		///
		/// The user must make sure to call `close_recovery` on all active recovery attempts
		/// before calling this function.
		fn remove_recovery(origin) {
			let who = ensure_signed(origin)?;
			// Check there are no active recoveries
			let mut active_recoveries = <ActiveRecoveries<T>>::iter_prefix(&who);
			ensure!(active_recoveries.next().is_none(), Error::<T>::StillActive);
			// Check account is recoverable
			if let Some(recovery_config) = <Recoverable<T>>::take(&who) {
				T::Currency::unreserve(&who, recovery_config.deposit);

				Self::deposit_event(RawEvent::RecoveryRemoved(who));
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Check that friends list is sorted.
	fn is_sorted(friends: &Vec<T::AccountId>) -> bool {
		friends.windows(2).all(|w| w[0] < w[1])
	}

	/// Check that a user is a friend in the friends list.
	fn is_friend(friends: &Vec<T::AccountId>, friend: &T::AccountId) -> bool {
		friends.binary_search(&friend).is_ok()
	}
}
