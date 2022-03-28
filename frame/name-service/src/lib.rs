// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

mod commit_reveal;
mod registrar;
mod subnodes;
mod types;

#[frame_support::pallet]
pub mod pallet {
	use crate::types::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::{Bounded, Convert, Saturating};
	use sp_std::vec::Vec;

	use frame_support::traits::{BalanceStatus, OnUnbalanced, ReservableCurrency};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	// Your Pallet's configuration trait, representing custom external types and interfaces.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The Currency handler for this pallet.
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

		/// The deposit a user needs to place to keep their subnodes in storage.
		#[pallet::constant]
		type SubNodeDeposit: Get<BalanceOf<Self>>;

		/// The deposit a user needs to place to keep their reverse-lookups in storage.
		#[pallet::constant]
		type ReverseLookupDeposit: Get<BalanceOf<Self>>;

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
		Committed { depositor: T::AccountId, owner: T::AccountId, hash: CommitmentHash },
		/// A new `Registration` has taken added.
		NameRegistered { name_hash: NameHash, owner: T::AccountId },
		/// A `Registration` has been transferred to a new owner.
		NewOwner { from: T::AccountId, to: T::AccountId },
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
		/// A `Registration` of this name already exists.
		RegistrationExists,
		/// This registration does not exist.
		RegistrationNotFound,
		/// Registration registratn does not exist.
		RegistrationRegistrantNotFound,
		/// The account is not the registration registrant.
		NotRegistrationRegistrant,
		/// The account is not the registration owner.
		NotRegistrationOwner,
		/// The account is not the registration registrant or the owner.
		NotRegistrationRegistrantOrOwner,
		/// This registration has expired.
		RegistrationExpired,
		/// This registration has not yet expired.
		RegistrationNotExpired,
		/// Cannot renew this registration.
		RegistrationHasNoExpiry,
		/// Subnode label is too short.
		LabelTooShort,
		/// Address has already been set to this.
		AlreadySet,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Force the registration of a name hash. It will overwrite any existing name registration,
		/// returning the deposit to the original owner.
		///
		/// Can only be called by the `RegistrationManager` origin.
		#[pallet::weight(0)]
		pub fn force_register(
			origin: OriginFor<T>,
			name_hash: NameHash,
			who: T::AccountId,
			maybe_expiry: Option<T::BlockNumber>,
		) -> DispatchResult {
			T::RegistrationManager::ensure_origin(origin)?;
			Self::do_register(name_hash, Some(who.clone()), who, maybe_expiry, None)?;
			Ok(())
		}

		/// Force the de-registration of a name hash. It will delete any existing name registration,
		/// returning the deposit to the original owner.
		///
		/// Can only be called by the `RegistrationManager` origin.
		#[pallet::weight(0)]
		pub fn force_deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			T::RegistrationManager::ensure_origin(origin)?;
			Self::do_deregister(name_hash);
			Ok(())
		}

		/// Allow a sender to commit to a new name registration on behalf of the `owner`. By making
		/// a commitment, the sender will reserve a deposit until the name is revealed or the
		/// commitment is removed.
		///
		/// The commitment hash should be the `bake2_256(name: Vec<u8>, secret: u64)`, which
		/// allows the sender to keep name being registered secret until it is revealed.
		///
		/// The `name` must be at least 3 characters long.
		///
		/// When `MinimumCommitmentPeriod` blocks have passed, any user can submit `reveal` with the
		/// `name` and `secret` parameters, and the registration will be completed.
		///
		/// See `fn reveal`.
		#[pallet::weight(0)]
		pub fn commit(
			origin: OriginFor<T>,
			owner: T::AccountId,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_commit(sender, owner, commitment_hash)?;
			Ok(())
		}

		/// Allow a sender to reveal a previously committed name registration on behalf of the
		/// committed `owner`. By revealing the name, the sender will pay a non-refundable
		/// registration fee.
		///
		/// The registration fee is calculated using the length of the name and the length of the
		/// registration.
		#[pallet::weight(0)]
		pub fn reveal(
			origin: OriginFor<T>,
			name: Vec<u8>,
			secret: u64,
			periods: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_reveal(sender, name, secret, periods)?;
			Ok(())
		}

		/// Allows anyone to remove a commitment that has expired the reveal period.
		///
		/// By doing so, the commitment deposit is returned to the original depositor.
		#[pallet::weight(0)]
		pub fn remove_commitment(
			origin: OriginFor<T>,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			let commitment = Self::get_commitment(commitment_hash)?;
			let block_number = frame_system::Pallet::<T>::block_number();
			ensure!(
				Self::is_commitment_expired(&commitment, &block_number),
				Error::<T>::CommitmentNotExpired
			);
			Self::do_remove_commitment(&commitment_hash, &commitment);
			Ok(())
		}

		/// Transfers the ownership and deposits of a name registration to a new owner.
		///
		/// Can only be called by the existing owner of the name registration.
		#[pallet::weight(0)]
		pub fn transfer(
			origin: OriginFor<T>,
			new_owner: T::AccountId,
			name_hash: NameHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration = Self::get_registration(name_hash)?;
			ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotRegistrationOwner);
			Self::do_transfer_ownership(name_hash, new_owner)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_owner(
			origin: OriginFor<T>,
			name_hash: NameHash,
			to: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;

				// registrant has to exist. Subnodes use `set_subnode_owner` instead.
				let registrant =
					r.registrant.clone().ok_or(Error::<T>::RegistrationRegistrantNotFound)?;

				ensure!(
					!(!(registrant == sender) && !(r.owner == sender)),
					Error::<T>::NotRegistrationRegistrantOrOwner
				);

				r.owner = to.clone();
				Self::deposit_event(Event::<T>::NewOwner { from: sender, to });
				Ok(())
			})
		}

		/// Allows any sender to extend the registration of an existing name.
		///
		/// By doing so, the sender will pay the non-refundable registration extension fee.
		#[pallet::weight(0)]
		pub fn renew(
			origin: OriginFor<T>,
			name_hash: NameHash,
			periods: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_renew(sender, name_hash, periods)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_address(
			origin: OriginFor<T>,
			name_hash: NameHash,
			address: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_address(name_hash, sender, address)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			if !Self::is_expired(&registration) {
				ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotRegistrationOwner);
			}
			Self::do_deregister(name_hash);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_subnode_record(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_subnode_record(sender, parent_hash, &label)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_subnode_owner(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label_hash: NameHash,
			owner: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				Registrations::<T>::contains_key(parent_hash),
				Error::<T>::RegistrationNotFound
			);

			let name_hash = Self::subnode_hash(parent_hash, label_hash);

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;
				ensure!(r.owner == sender, Error::<T>::NotRegistrationOwner);

				if let Some(deposit) = r.deposit {
					T::Currency::repatriate_reserved(
						&sender,
						&owner,
						deposit,
						BalanceStatus::Reserved,
					)?;
				}

				r.owner = owner.clone();
				Self::deposit_event(Event::<T>::NewOwner { from: sender, to: owner });
				Ok(())
			})
		}

		#[pallet::weight(0)]
		pub fn deregister_subnode(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label_hash: NameHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let subnode_hash = Self::subnode_hash(parent_hash, label_hash);
			let subnode_registration = Self::get_registration(subnode_hash)?;
			// The owner isn't calling, we check that the parent registration doesn't exist, which
			// mean this subnode is still valid.
			if !Self::is_owner(&subnode_registration, &sender) {
				ensure!(
					Self::get_registration(parent_hash).is_err(),
					Error::<T>::RegistrationNotExpired
				);
			}
			Self::do_deregister(subnode_hash);
			Ok(())
		}
	}

	// Pallet internal functions
	impl<T: Config> Pallet<T> {
		pub fn registration_fee(name: Vec<u8>, periods: T::BlockNumber) -> BalanceOf<T> {
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

		pub fn length_fee(periods: T::BlockNumber) -> BalanceOf<T> {
			let periods_as_balance: BalanceOf<T> = T::BlockNumberToBalance::convert(periods);
			T::FeePerRegistrationPeriod::get().saturating_mul(periods_as_balance)
		}

		pub fn length(periods: T::BlockNumber) -> T::BlockNumber {
			periods.saturating_mul(T::BlocksPerRegistrationPeriod::get())
		}

		pub fn do_set_address(
			name_hash: NameHash,
			owner: T::AccountId,
			address: T::AccountId,
		) -> DispatchResult {
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			ensure!(registration.owner == owner, Error::<T>::NotRegistrationOwner);

			if let Some(e) = registration.expiry {
				ensure!(
					frame_system::Pallet::<T>::block_number() <= e,
					Error::<T>::RegistrationExpired
				);
			}

			let maybe_current_address = Resolvers::<T>::get(name_hash);
			if let Some(a) = maybe_current_address {
				ensure!(a != address, Error::<T>::AlreadySet);
			}

			Resolvers::<T>::insert(name_hash, address.clone());
			Self::deposit_event(Event::<T>::AddressSet { name_hash, address });
			Ok(())
		}
	}
}
