// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! A simple name service that can be used to give accounts friendly names.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::{Bounded, Convert, Saturating, Zero};
	use sp_std::{convert::TryInto, vec::Vec};

	use frame_support::traits::{
		Currency, ExistenceRequirement, OnUnbalanced, ReservableCurrency, WithdrawReasons,
	};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	type NameHash = [u8; 32];

	type CommitmentHash = [u8; 32];

	// Allows easy access our Pallet's `Balance` and `NegativeImbalance` type. Comes from `Currency`
	// interface.
	type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::NegativeImbalance;

	// Your Pallet's configuration trait, representing custom external types and interfaces.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The Currency handler for the kitties pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Convert the block number into a balance.
		type BlockNumberToBalance: Convert<Self::BlockNumber, BalanceOf<Self>>;

		/// The account where registration fees are paid to.
		type RegistrationFeeHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The deposit a user needs to make in order to commit to a name registration.
		#[pallet::constant]
		type CommitmentDeposit: Get<BalanceOf<Self>>;

		/// The amount of blocks a user needs to wait after a Commitment before revealing.
		#[pallet::constant]
		type MinimumCommitmentPeriod: Get<Self::BlockNumber>;

		/// The amount of blocks after a commitment is created for before it expires.
		#[pallet::constant]
		type CommitmentAlivePeriod: Get<Self::BlockNumber>;

		/// The deposit a user needs to place in order to keep their name registration in storage.
		#[pallet::constant]
		type NameDeposit: Get<BalanceOf<Self>>;

		/// Registration fee for registering a 3-letter name.
		#[pallet::constant]
		type TierThreeLetters: Get<BalanceOf<Self>>;

		/// Registration fee for registering a 4-letter name.
		#[pallet::constant]
		type TierFourLetters: Get<BalanceOf<Self>>;

		/// Default registration fee for 5+ letter names.
		#[pallet::constant]
		type TierDefault: Get<BalanceOf<Self>>;

		/// How long a registration period is in blocks.
		#[pallet::constant]
		type BlocksPerRegistrationPeriod: Get<Self::BlockNumber>;

		/// Notification duration before expiry, in blocks.
		#[pallet::constant]
		type NotificationPeriod: Get<Self::BlockNumber>;

		/// Registration fee per registration period, defined as a number of blocks.
		#[pallet::constant]
		type FeePerRegistrationPeriod: Get<BalanceOf<Self>>;

		/// The origin that has super-user access to manage all name registrations.
		type RegistrationManager: EnsureOrigin<Self::Origin>;
	}

	#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo)]
	pub struct Commitment<AccountId, Balance, BlockNumber> {
		pub who: AccountId,
		pub when: BlockNumber,
		pub deposit: Balance,
	}

	#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo)]
	pub struct Registration<AccountId, Balance, BlockNumber> {
		pub owner: AccountId,
		pub registrant: AccountId,
		pub expiry: BlockNumber,
		pub deposit: Balance,
	}

	/* Placeholder for defining custom storage items. */

	/// Name Commitments
	#[pallet::storage]
	#[pallet::getter(fn commitment)]
	pub(super) type Commitments<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		CommitmentHash,
		Commitment<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// Name Registrations
	#[pallet::storage]
	#[pallet::getter(fn registration)]
	pub(super) type Registrations<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		Registration<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// This resolver maps name hashes to an account
	#[pallet::storage]
	#[pallet::getter(fn resolve)]
	pub(super) type Resolvers<T: Config> = StorageMap<_, Blake2_128Concat, NameHash, T::AccountId>;

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		// TODO: Potentially make events more lightweight
		/// A new `Commitment` has taken place.
		Committed { sender: T::AccountId, who: T::AccountId, hash: CommitmentHash },
		/// A new `Registration` has taken added.
		NameRegistered { name_hash: NameHash, owner: T::AccountId, expiry: T::BlockNumber },
		/// A `Registration` has been transferred to a new owner.
		Transfer { from: T::AccountId, to: T::AccountId },
		/// A `Registration` has been renewed.
		NameRenewed { name_hash: NameHash, expires: T::BlockNumber },
		/// An address has been set for a name hash to resolve to.
		AddressSet { name_hash: NameHash, address: T::AccountId },
		/// An address was deregistered.
		AddressDeregistered { name_hash: NameHash },
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// This commitment hash already exists in storage.
		AlreadyCommitted,
		/// It has not passed the minimum waiting period to reveal a commitement.
		TooEarlyToReveal,
		/// The commitment cannot yet be removed. Has not expired.
		CommitmentNotExpired,
		/// This commitment does not exist.
		CommitmentNotFound,
		/// This registration does not exist.
		RegistrationNotFound,
		/// The sender is not the registration owner.
		NotRegistrationOwner,
		/// This registration has expired.
		RegistrationExpired,
		/// This registration has not yet expired.
		RegistrationNotExpired,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		// TODO: Should we allow registration on behalf of?
		#[pallet::weight(0)]
		pub fn commit(
			origin: OriginFor<T>,
			who: T::AccountId,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(!Commitments::<T>::contains_key(commitment_hash), Error::<T>::AlreadyCommitted);

			let block_number = frame_system::Pallet::<T>::block_number();
			let deposit = T::CommitmentDeposit::get();

			T::Currency::reserve(&sender, deposit)?;

			let commitment = Commitment { who: who.clone(), when: block_number, deposit };

			Commitments::<T>::insert(commitment_hash, commitment);
			Self::deposit_event(Event::<T>::Committed { sender, who, hash: commitment_hash });

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn reveal(
			origin: OriginFor<T>,
			name: Vec<u8>,
			secret: u64,
			periods: u32,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let commitment_hash = sp_io::hashing::blake2_256(&(&name, secret).encode());

			let commitment =
				Commitments::<T>::get(commitment_hash).ok_or(Error::<T>::CommitmentNotFound)?;

			let name_hash = sp_io::hashing::blake2_256(&name);
			let block_number = frame_system::Pallet::<T>::block_number();

			ensure!(
				block_number > commitment.when.saturating_add(T::MinimumCommitmentPeriod::get()),
				Error::<T>::TooEarlyToReveal
			);

			if Self::is_available(name_hash, block_number) {
				let fee = Self::registration_fee(name.clone(), periods);

				let imbalance = T::Currency::withdraw(
					&sender,
					fee,
					WithdrawReasons::FEE,
					ExistenceRequirement::KeepAlive,
				)?;

				T::RegistrationFeeHandler::on_unbalanced(imbalance);

				let deposit = T::NameDeposit::get();
				Self::do_register(name_hash, commitment.who.clone(), deposit, periods)?;
			}

			T::Currency::unreserve(&commitment.who, commitment.deposit);
			Commitments::<T>::remove(commitment_hash);

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn transfer(
			origin: OriginFor<T>,
			to: T::AccountId,
			name_hash: NameHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let block_number = frame_system::Pallet::<T>::block_number();

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;
				ensure!(r.owner == sender, Error::<T>::NotRegistrationOwner);
				ensure!(r.expiry > block_number, Error::<T>::RegistrationExpired);

				r.owner = to.clone();

				// TODO: transfer deposit over?

				Self::deposit_event(Event::<T>::Transfer { from: sender, to });
				Ok(())
			})
		}

		#[pallet::weight(0)]
		pub fn renew(origin: OriginFor<T>, name_hash: NameHash, periods: u32) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;

				let fee = Self::length_fee(periods);

				// withdraw fees from account
				let imbalance = T::Currency::withdraw(
					&sender,
					fee,
					WithdrawReasons::FEE,
					ExistenceRequirement::KeepAlive,
				)?;

				let block_number = frame_system::Pallet::<T>::block_number();

				let expiry_new = match r.expiry > block_number {
					true => r.expiry.saturating_add(Self::length(periods)),
					false => block_number.saturating_add(Self::length(periods)),
				};

				r.expiry = expiry_new;

				T::RegistrationFeeHandler::on_unbalanced(imbalance);

				Self::deposit_event(Event::<T>::NameRenewed { name_hash, expires: expiry_new });
				Ok(())
			})
		}

		#[pallet::weight(0)]
		pub fn set_address(
			origin: OriginFor<T>,
			name_hash: NameHash,
			address: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			ensure!(registration.owner == sender, Error::<T>::NotRegistrationOwner);

			ensure!(
				registration.expiry > frame_system::Pallet::<T>::block_number(),
				Error::<T>::RegistrationExpired
			);

			Resolvers::<T>::insert(name_hash, address.clone());

			Self::deposit_event(Event::<T>::AddressSet { name_hash, address });

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_deregister(name_hash, Some(sender))?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn force_register(
			origin: OriginFor<T>,
			name_hash: NameHash,
			who: T::AccountId,
			periods: u32,
		) -> DispatchResult {
			T::RegistrationManager::ensure_origin(origin)?;
			let deposit: BalanceOf<T> = Zero::zero();
			Self::do_register(name_hash, who, deposit, periods)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn force_deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			T::RegistrationManager::ensure_origin(origin)?;
			Self::do_deregister(name_hash, None)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn remove_commitment(
			origin: OriginFor<T>,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			let commitment =
				Commitments::<T>::get(commitment_hash).ok_or(Error::<T>::CommitmentNotFound)?;

			ensure!(
				commitment.when.saturating_add(T::CommitmentAlivePeriod::get()) >
					frame_system::Pallet::<T>::block_number(),
				Error::<T>::CommitmentNotExpired
			);

			let _ = T::Currency::unreserve(&commitment.who, commitment.deposit);
			Commitments::<T>::remove(commitment_hash);
			Ok(())
		}
	}

	// Pallet internal functions
	impl<T: Config> Pallet<T> {
		pub fn registration_fee(name: Vec<u8>, periods: u32) -> BalanceOf<T> {
			let name_length = name.len();
			let fee_reg = if name_length < 3 {
				// names with under 3 characters should not be registered, so we
				// put an exorbitant fee.
				BalanceOf::<T>::max_value()
			} else if name_length == 3 {
				T::TierThreeLetters::get()
			} else if name_length == 4 {
				T::TierFourLetters::get()
			} else {
				T::TierDefault::get()
			};

			let fee_length = Self::length_fee(periods);
			fee_reg.saturating_add(fee_length)
		}

		pub fn length_fee(periods: u32) -> BalanceOf<T> {
			let periods_as_balance: BalanceOf<T> = periods.try_into().ok().unwrap();
			T::FeePerRegistrationPeriod::get().saturating_mul(periods_as_balance)
		}

		pub fn length(periods: u32) -> T::BlockNumber {
			let periods_as_block_number: T::BlockNumber = periods.try_into().ok().unwrap();
			periods_as_block_number.saturating_mul(T::BlocksPerRegistrationPeriod::get())
		}

		pub fn is_available(name_hash: NameHash, current_block_number: T::BlockNumber) -> bool {
			match Registrations::<T>::get(name_hash) {
				Some(r) => r.expiry <= current_block_number,
				None => true,
			}
		}

		pub fn do_register(
			name_hash: NameHash,
			owner: T::AccountId,
			deposit: BalanceOf<T>,
			periods: u32,
		) -> DispatchResult {
			let block_number = frame_system::Pallet::<T>::block_number();
			let expiry = block_number.saturating_add(Self::length(periods));

			// if registration already exists, unreserve deposit
			let maybe_existing_registration = Registrations::<T>::get(name_hash);
			if let Some(r) = maybe_existing_registration {
				let _ = T::Currency::unreserve(&r.registrant, r.deposit);
			}
			
			// reserve deposit
			T::Currency::reserve(&owner, deposit)?;

			let registration =
				Registration { owner: owner.clone(), registrant: owner.clone(), expiry, deposit };

			Registrations::<T>::insert(name_hash, registration);

			Self::deposit_event(Event::<T>::NameRegistered { name_hash, owner, expiry });

			Ok(())
		}

		pub fn do_deregister(
			name_hash: NameHash,
			maybe_sender: Option<T::AccountId>,
		) -> DispatchResult {
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;

			let is_owner =
				if let Some(sender) = maybe_sender { registration.owner == sender } else { false };

			// If the sender is not the owner, we need to verify that the registration has expired.
			// Otherwise, we can skip this check since owner can do whatever they want.
			if !is_owner {
				ensure!(
					registration.expiry <= frame_system::Pallet::<T>::block_number(),
					Error::<T>::RegistrationNotExpired
				);
			}

			let _ = T::Currency::unreserve(&registration.registrant, registration.deposit);

			Registrations::<T>::remove(name_hash);
			Self::deposit_event(Event::<T>::AddressDeregistered { name_hash });

			Ok(())
		}
	}
}
