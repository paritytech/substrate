// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Preimage Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Preimage pallet allows for the users and the runtime to store the preimage
//! of a hash on chain. This can be used by other pallets where storing and managing
//! large byte-blobs.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::{
	traits::{BadOrigin, Hash, Saturating},
	DispatchResult,
};
use sp_std::{convert::TryFrom, prelude::*};

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	ensure,
	pallet_prelude::Get,
	traits::{Currency, ReservableCurrency},
	BoundedVec,
};
use scale_info::TypeInfo;

pub use pallet::*;

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct Preimage<BoundedVec, Balance, AccountId> {
	preimage: BoundedVec,
	deposit: Option<(Balance, AccountId)>,
}

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use super::{DispatchResult, *};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// An origin that can bypass deposits to place a preimage on-chain.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// Max size allowed for a preimage.
		type MaxSize: Get<u32>;

		/// The base deposit for placing a preimage on chain.
		type BaseDeposit: Get<BalanceOf<Self>>;

		/// The per-byte deposit for placing a preimage on chain.
		type ByteDeposit: Get<BalanceOf<Self>>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A preimage has been noted.
		Noted { hash: T::Hash },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Preimage is too large to store on-chain.
		TooLarge,
		/// Preimage has already been noted on-chain.
		AlreadyNoted,
	}

	/// The preimages stored by this pallet.
	#[pallet::storage]
	#[pallet::getter(fn key)]
	pub(super) type Preimages<T: Config> = StorageMap<
		_,
		Identity, // TODO: Double Check
		T::Hash,
		Preimage<BoundedVec<u8, T::MaxSize>, BalanceOf<T>, T::AccountId>,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register a preimage by paying a deposit proportional to the length of the preimage.
		#[pallet::weight(0)] //T::WeightInfo::note_preimage(encoded_proposal.len() as u32))]
		pub fn note_preimage(origin: OriginFor<T>, bytes: Vec<u8>) -> DispatchResult {
			// We accept a signed origin which will pay a deposit, or a root origin where a deposit
			// is not taken.
			let maybe_sender = Self::ensure_signed_or_root(origin)?;
			Self::note_bytes(bytes, maybe_sender)?;
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Ensure that the origin is either root, or `PalletOwner`.
	fn ensure_signed_or_root(origin: T::Origin) -> Result<Option<T::AccountId>, BadOrigin> {
		use frame_system::RawOrigin;
		match origin.into() {
			Ok(RawOrigin::Root) => Ok(None),
			Ok(RawOrigin::Signed(signer)) => Ok(Some(signer)),
			_ => Err(BadOrigin),
		}
	}

	pub fn note_bytes(bytes: Vec<u8>, maybe_depositor: Option<T::AccountId>) -> DispatchResult {
		let bounded_vec =
			BoundedVec::<u8, T::MaxSize>::try_from(bytes).map_err(|()| Error::<T>::TooLarge)?;

		let hash = T::Hashing::hash(&bounded_vec);
		ensure!(!Preimages::<T>::contains_key(hash), Error::<T>::AlreadyNoted);

		let deposit = if let Some(depositor) = maybe_depositor {
			let length = bounded_vec.len() as u32;
			let deposit = T::BaseDeposit::get()
				.saturating_add(T::ByteDeposit::get().saturating_mul(length.into()));
			T::Currency::reserve(&depositor, deposit)?;
			Some((depositor, deposit))
		} else {
			None
		};

		let preimage = Preimage { preimage: bounded_vec, deposit };

		//Preimages::<T>::insert(hash, preimage);
		Self::deposit_event(Event::Noted { hash });
		Ok(())
	}
}
