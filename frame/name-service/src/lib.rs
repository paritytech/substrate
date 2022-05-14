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

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
mod commit_reveal;
mod misc;
mod registrar;
mod resolver;
mod subnodes;
mod types;
mod weights;

pub use resolver::NameServiceResolver;

#[frame_support::pallet]
pub mod pallet {
	use crate::{resolver::NameServiceResolver, types::*};
	use frame_support::{
		pallet_prelude::*,
		traits::{OnUnbalanced, ReservableCurrency},
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::{Convert, Zero};
	use sp_std::vec::Vec;

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
		type MinCommitmentAge: Get<Self::BlockNumber>;

		/// The amount of blocks after a commitment is created for before it expires.
		#[pallet::constant]
		type MaxCommitmentAge: Get<Self::BlockNumber>;

		/// Maximum length of a name.
		#[pallet::constant]
		type MaxNameLength: Get<u32>;

		/// Maximum length for metadata text.
		#[pallet::constant]
		type MaxTextLength: Get<u32>;

		/// The deposit a user needs to place to keep their subnodes in storage.
		#[pallet::constant]
		type SubNodeDeposit: Get<BalanceOf<Self>>;

		/// Registration fee for registering a 3-letter name.
		#[pallet::constant]
		type TierThreeLetters: Get<BalanceOf<Self>>;

		/// Registration fee for registering a 4-letter name.
		#[pallet::constant]
		type TierFourLetters: Get<BalanceOf<Self>>;

		/// Default registration fee for 5+ letter names.
		#[pallet::constant]
		type TierDefault: Get<BalanceOf<Self>>;

		/// Registration fee per block.
		#[pallet::constant]
		type RegistrationFeePerBlock: Get<BalanceOf<Self>>;

		/// The origin that has super-user access to manage all name registrations.
		type RegistrationManager: EnsureOrigin<Self::Origin>;

		/// An interface to access the name service resolver.
		type NameServiceResolver: NameServiceResolver<Self>;

		/// The deposit taken per byte of storage used.
		type PerByteFee: Get<BalanceOf<Self>>;
	}

	/* Placeholder for defining custom storage items. */

	/// Name Commitments
	#[pallet::storage]
	pub(super) type Commitments<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		CommitmentHash,
		Commitment<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// Name Registrations
	#[pallet::storage]
	pub(super) type Registrations<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		Registration<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// This resolver maps name hashes to an account
	#[pallet::storage]
	pub(super) type AddressResolver<T: Config> =
		StorageMap<_, Blake2_128Concat, NameHash, T::AccountId>;

	/// This resolver maps name hashes to an account
	#[pallet::storage]
	pub(super) type NameResolver<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		BytesStorage<T::AccountId, BalanceOf<T>, BoundedNameOf<T>>,
	>;

	/// This resolver maps name hashes to an account
	#[pallet::storage]
	pub(super) type TextResolver<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		BytesStorage<T::AccountId, BalanceOf<T>, BoundedTextOf<T>>,
	>;

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
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
		/// An name has been set as a reverse lookup for a name hash. You can query storage to see
		/// what the name is.
		NameSet { name_hash: NameHash },
		/// An address has been set for a name hash to resolve to. You can query storage to see
		/// what text was set.
		TextSet { name_hash: NameHash },
		/// An address was deregistered.
		AddressDeregistered { name_hash: NameHash },
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// It has not passed the minimum waiting period to reveal a commitment.
		TooEarlyToReveal,
		/// This commitment hash already exists in storage.
		CommitmentExists,
		/// The commitment cannot yet be removed. Has not expired.
		CommitmentNotExpired,
		/// This commitment does not exist.
		CommitmentNotFound,
		/// A `Registration` of this name already exists.
		RegistrationExists,
		/// This registration has not yet expired.
		RegistrationNotExpired,
		/// This registration does not exist.
		RegistrationNotFound,
		/// Name is too short to be registered.
		NameTooShort,
		/// The name was longer than the configured limit.
		NameTooLong,
		/// The account is not the name controller.
		NotController,
		/// The account is not the name owner.
		NotOwner,
		/// Cannot renew this registration.
		RegistrationHasNoExpiry,
		/// Renew expiry time is not in the future
		ExpiryInvalid,
		/// The name provided does not match the expected hash.
		BadName,
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
			Self::do_register(name_hash, who.clone(), who, maybe_expiry, None)?;
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
		/// When `MinCommitmentAge` blocks have passed, any user can submit `reveal` with the
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
			length: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_reveal(sender, name, secret, length)?;
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
			ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);
			Self::do_transfer_ownership(name_hash, new_owner)?;
			Ok(())
		}

		/// Set the controller for a name registration.
		///
		/// Can only be called by the existing controller or owner.
		#[pallet::weight(0)]
		pub fn set_controller(
			origin: OriginFor<T>,
			name_hash: NameHash,
			to: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
				let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;
				ensure!(Self::is_controller(&r, &sender), Error::<T>::NotController);
				r.controller = to.clone();
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
			expiry: T::BlockNumber,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_renew(sender, name_hash, expiry)?;
			Ok(())
		}

		/// Deregister a registered name.
		///
		/// If the registration is still valid, only the owner of the name can make this call.
		///
		/// If the registration is expired, then anyone can call this function to make the name
		/// available.
		#[pallet::weight(0)]
		pub fn deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			// If the registration is expired, anyone can trigger deregister.
			if !Self::is_expired(&registration) {
				ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);
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

		#[pallet::weight(0)]
		pub fn set_subnode_owner(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label_hash: NameHash,
			new_owner: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_subnode_owner(sender, parent_hash, label_hash, new_owner)?;
			Ok(())
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
			ensure!(Self::is_controller(&registration, &sender), Error::<T>::NotController);
			T::NameServiceResolver::set_address(name_hash, address, sender)?;
			Ok(())
		}

		/// Register the raw name for a given name hash. This can be used as a reverse lookup for
		/// front-ends.
		///
		/// This is a permissionless function that anyone can call who is willing to place a deposit
		/// to store this data on chain.
		#[pallet::weight(0)]
		pub fn set_name(
			origin: OriginFor<T>,
			name_hash: NameHash,
			name: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(Registrations::<T>::contains_key(name_hash), Error::<T>::RegistrationNotFound);
			let bounded_name = name.try_into().map_err(|()| Error::<T>::NameTooLong)?;
			T::NameServiceResolver::set_name(name_hash, bounded_name, sender)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_text(
			origin: OriginFor<T>,
			name_hash: NameHash,
			text: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			ensure!(Self::is_controller(&registration, &sender), Error::<T>::NotController);
			let bounded_text = text.try_into().map_err(|()| Error::<T>::NameTooLong)?;
			T::NameServiceResolver::set_text(name_hash, bounded_text, sender)?;
			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			// registration fee per block cannot be zero
			assert!(T::RegistrationFeePerBlock::get() > BalanceOf::<T>::zero());
			// max name length cannot be zero
			assert!(T::MaxNameLength::get() > 0);
			// max text length cannot be zero
			assert!(!T::MaxTextLength::get() > 0);
			// three letter tier fee must be larger than four letter tier fee
			assert!(T::TierThreeLetters::get() > BalanceOf::<T>::zero());
			// four letter tier fee must be larger than default tier fee
			assert!(T::TierFourLetters::get() > BalanceOf::<T>::zero());
		}
	}
}
