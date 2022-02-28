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

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::traits::{Currency, ReservableCurrency};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	type NameHash = [u8; 32];

	type CommitmentHash = [u8; 32];

	// Allows easy access our Pallet's `Balance` type. Comes from `Currency` interface.
	type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	// Your Pallet's configuration trait, representing custom external types and interfaces.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The Currency handler for the kitties pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The deposit a user needs to make in order to commit to a name registration.
		#[pallet::constant]
		type CommitmentDeposit = Get<BalanceOf<T>>;

		/// The deposit a user needs to place in order to keep their name registration in storage.
		#[pallet::constant]
		type NameDeposit = Get<BalanceOf<T>>;
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

	/// Name Registrations
	#[pallet::storage]
	pub(super) type Names<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, NameHash>;

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Committed { who: T::AccountId, hash: CommitmentHash },

	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// This commitment hash already exists in storage.
		AlreadyCommitted,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn commit(origin: OriginFor<T>, commitment_hash: CommitmentHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(!Commitments::<T>::contains_key(commitment_hash), Error::<T>::AlreadyCommitted);
			let block_number = frame_system::Pallet::<T>::block_number();
			let deposit = T::CommitmentDeposit::get();

			T::Currenty::reserve(sender, deposit)?;

			let commitment = Commitment {
				who: sender,
				when: block_number,
				deposit,
			}

			Commitments::<T>::insert(commitment_hash, commitment);
			Self::deposit_event()

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn reveal(origin: OriginFor<T>, commitment_hash: CommitmentHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(!Commitments::<T>::contains_key(commitment_hash), Error::<T>::AlreadyCommitted);
			let block_number = frame_system::Pallet::<T>::block_number();
			let deposit = T::CommitmentDeposit::get();

			T::Currenty::reserve(sender, deposit)?;

			let commitment = Commitment {
				who: sender,
				when: block_number,
				deposit,
			}

			Commitments::<T>::insert(commitment_hash, commitment);
			Self::deposit_event()

			Ok(())
		}


	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {
		fn do_register(name_hash: NameHash, who: T::AccountId, deposit: BalanceOf<T>) -> DispatchResult {
			Ok(())
		}
	}
}
