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
	use sp_runtime::traits::{Hash, Saturating};

	use frame_support::traits::{
		Currency, ExistenceRequirement, OnUnbalanced, ReservableCurrency, WithdrawReasons,
	};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	type NameHash = [u8; 32];

	type CommitmentHash = [u8; 32];

	// Allows easy access our Pallet's `Balance` type. Comes from `Currency` interface.
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

		/// The account where registration fees are paid to.
		type RegistrationFeeHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The deposit a user needs to make in order to commit to a name registration.
		#[pallet::constant]
		type CommitmentDeposit: Get<BalanceOf<Self>>;

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

		// Registration fee per block. Included in registration and extension fees.
		#[pallet::constant]
		type FeePerBlock: Get<BalanceOf<Self>>;

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

	#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
	pub enum Resolver<AccountId> {
		Default(AccountId),
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
	pub(super) type Resolvers<T: Config> =
		StorageMap<_, Blake2_128Concat, NameHash, Resolver<T::AccountId>>;

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		// TODO: Potentially make events more lightweight
		/// A new `Commitment` has taken place.
		Committed { sender: T::AccountId, who: T::AccountId, hash: CommitmentHash },
		/// A new `Registration` has taken added.
		Registered {
			owner: T::AccountId,
			registrant: T::AccountId,
			expiry: T::BlockNumber,
			deposit: BalanceOf<T>,
		},
		/// A `Registration` has been transferred to a new owner.
		Transfer { from: T::AccountId, to: T::AccountId },
		/// A `Registration` has been extended.
		Extended { name_hash: NameHash, expires: T::BlockNumber },
		/// An address has been set for a name hash to resolve to.
		AddressSet { name_hash: NameHash, address: T::AccountId },
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// This commitment hash already exists in storage.
		AlreadyCommitted,
		/// This commitment does not exist.
		CommitmentNotFound,
		/// This name is already registered.
		AlreadyRegistered,
		/// This registration does not exist.
		RegistrationNotFound,
		/// The sender is not the registration owner.
		NotRegistrationOwner,
		/// This resolver does not exist.
		ResolverNotFound,
		/// This registration has expired.
		RegistrationExpired,
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
			length: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let commitment_hash = sp_io::hashing::blake2_256(&(name.clone(), secret).encode());

			let commitment =
				Commitments::<T>::get(commitment_hash.clone()).ok_or(Error::<T>::CommitmentNotFound)?;
			let name_hash = sp_io::hashing::blake2_256(&name);

			// TODO: if statement, available then register, otherwise remove commitment
			ensure!(Self::is_available(name_hash, frame_system::Pallet::<T>::block_number()), Error::<T>::AlreadyRegistered);

			let fee = Self::registration_fee(name.clone(), length);

			// withdraw fees from account
			let imbalance =
				T::Currency::withdraw(&sender, fee, WithdrawReasons::FEE, ExistenceRequirement::KeepAlive)?;

			T::RegistrationFeeHandler::on_unbalanced(imbalance);

			// TODO: handle deposits maybe in the future
			let deposit: BalanceOf<T> = Default::default();

			Self::do_register(name_hash, commitment.who, deposit, length);

			// TODO: handle this if name expires
			Commitments::<T>::remove(commitment_hash);

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn transfer(origin: OriginFor<T>, to: T::AccountId, name_hash: NameHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let block_number = frame_system::Pallet::<T>::block_number();

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;
				ensure!(r.owner == sender, Error::<T>::NotRegistrationOwner);
				ensure!(r.expiry > block_number, Error::<T>::RegistrationExpired);

				r.owner = to.clone();

				Self::deposit_event(Event::<T>::Transfer { from: sender, to });
				Ok(())
			})
		}

		#[pallet::weight(0)]
		pub fn renew(
			origin: OriginFor<T>,
			name_hash: NameHash,
			length: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;

				// TODO: check if within expiry or in grace period
				// if we are in grace period, new expiry is current block + length
				// if we are before expiry, new expiry is currency expiry + length
				// if we are beyond grace period, need to re-register (fail renew).

				let fee = Self::length_fee(length);

				// withdraw fees from account
				let imbalance = T::Currency::withdraw(
					&sender,
					fee,
					WithdrawReasons::FEE,
					ExistenceRequirement::KeepAlive,
				)?;

				let expiry_new = r.expiry.saturating_add(length);
				r.expiry = expiry_new.clone();

				T::RegistrationFeeHandler::on_unbalanced(imbalance);

				Self::deposit_event(Event::<T>::Extended { name_hash, expires: expiry_new });
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

			Resolvers::<T>::insert(name_hash, Resolver::Default(address.clone()));

			Self::deposit_event(Event::<T>::AddressSet { name_hash, address });

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn force_register(
			origin: OriginFor<T>,
			name_hash: NameHash,
			who: T::AccountId,
			length: T::BlockNumber,
		) -> DispatchResult {
			T::RegistrationManager::ensure_origin(origin)?;
			// TODO: Deposit maybe should just be ZERO
			let deposit = Default::default();
			Self::do_register(name_hash, who, deposit, length)?;
			Ok(())
		}
	}

	// Your Pallet's internal functions.
	// TODO: make block_number function parameter?
	impl<T: Config> Pallet<T> {
		fn is_available(name_hash: NameHash, block_number: T::BlockNumber) -> bool {
			match Registrations::<T>::get(name_hash) {
				// TODO: add grace period to expiry
				Some(r) => r.expiry < block_number,
				None => true,
			}
		}

		fn registration_fee(name: Vec<u8>, length: T::BlockNumber) -> BalanceOf<T> {
			let fee_reg: BalanceOf<T> = match name.len() {
				3 => T::TierThreeLetters::get(),
				4 => T::TierFourLetters::get(),
				_ => T::TierDefault::get(),
			};
			let fee_length = Self::length_fee(length);
			fee_reg.saturating_add(fee_length)
		}

		fn length_fee(length: T::BlockNumber) -> BalanceOf<T> {
			// T::FeePerBlock::get().saturating_mul(length.into())
			Default::default()
		}

		fn do_register(
			name_hash: NameHash,
			who: T::AccountId,
			deposit: BalanceOf<T>,
			length: T::BlockNumber,
		) -> DispatchResult {
			let block_number = frame_system::Pallet::<T>::block_number();
			let expiry = block_number.saturating_add(length);

			let registration =
				Registration { owner: who.clone(), registrant: who.clone(), expiry, deposit };

			Registrations::<T>::insert(name_hash, registration);

			Self::deposit_event(Event::<T>::Registered {
				owner: who.clone(),
				registrant: who,
				expiry,
				deposit,
			});

			Ok(())
		}
	}
}
