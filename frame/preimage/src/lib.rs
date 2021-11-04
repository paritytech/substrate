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

use sp_runtime::traits::{BadOrigin, Hash, One, Saturating};
use sp_std::{convert::TryFrom, prelude::*};

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	ensure,
	pallet_prelude::Get,
	traits::{Currency, ReservableCurrency},
	weights::Pays,
	BoundedVec,
};
use scale_info::TypeInfo;

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

pub use pallet::*;

/// A type to note whether a preimage is owned by a user or the system.
#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum RefCount<AccountId, Balance> {
	/// This preimage is owned by a user who has the following deposit on hold.
	User(AccountId, Balance),
	/// This preimage is managed by the system with a number of reference counters.
	System(u32),
}

/// The preimage metadata.
#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct Preimage<BoundedVec, AccountId, Balance> {
	// The preimage we are storing.
	pub preimage: BoundedVec,
	// A reference counter for who depends on this resource.
	pub ref_count: RefCount<AccountId, Balance>,
}

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// An origin that can request a preimage be placed on-chain without a deposit or fee, or
		/// manage existing preimages.
		type ManagerOrigin: EnsureOrigin<Self::Origin>;

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
		/// A preimage has been requested.
		Requested { hash: T::Hash },
		/// A preimage has ben cleared.
		Cleared { hash: T::Hash },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Preimage is too large to store on-chain.
		TooLarge,
		/// Preimage has already been noted on-chain.
		AlreadyNoted,
		/// The user is not authorized to perform this action.
		NotAuthorized,
	}

	/// The preimages stored by this pallet.
	// TODO: Maybe store preimage metadata in its own storage.
	#[pallet::storage]
	pub(super) type Preimages<T: Config> = StorageMap<
		_,
		Identity, // TODO: Double Check
		T::Hash,
		Preimage<BoundedVec<u8, T::MaxSize>, T::AccountId, BalanceOf<T>>,
	>;

	/// Any outstanding preimage requests.
	#[pallet::storage]
	pub(super) type Requests<T: Config> = StorageMap<
		_,
		Identity, // TODO: Double Check
		T::Hash,
		u32,
		ValueQuery,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register a preimage on-chain.
		///
		/// If the preimage was previously requested, no fees or deposits are taken for providing
		/// the preimage. Otherwise, a deposit is taken proportional to the size of the preimage.
		#[pallet::weight(0)]
		pub fn note_preimage(origin: OriginFor<T>, bytes: Vec<u8>) -> DispatchResultWithPostInfo {
			// We accept a signed origin which will pay a deposit, or a root origin where a deposit
			// is not taken.
			let maybe_sender = Self::ensure_signed_or_manager(origin)?;
			let bounded_vec =
				BoundedVec::<u8, T::MaxSize>::try_from(bytes).map_err(|()| Error::<T>::TooLarge)?;
			if let Some(sender) = maybe_sender {
				let system_requested = Self::note_user_bytes(bounded_vec, sender)?;
				if system_requested {
					Ok(Pays::No.into())
				} else {
					Ok(().into())
				}
			} else {
				Self::note_system_bytes(bounded_vec);
				Ok(Pays::No.into())
			}
		}

		/// Clear a preimage from the runtime storage.
		///
		/// If a signed origin is requesting to clear a preimage, they must be managing that
		/// preimage by holding a deposit against it. After the preimage is cleared, any held
		/// deposit will be returned to the user.
		///
		/// Otherwise, the `ManagerOrigin` can clear any preimage, and will correctly handle
		/// deposits.
		#[pallet::weight(0)]
		pub fn clear_preimage(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			let maybe_sender = Self::ensure_signed_or_manager(origin)?;
			Self::do_clear_preimage(hash, maybe_sender)?;
			Ok(())
		}

		/// Request a preimage be uploaded to the chain without paying any fees or deposits.
		///
		/// If the preimage requests has already been provided on-chain, we unreserve any deposit
		/// a user may have paid, and take the control of the preimage out of their hands.
		#[pallet::weight(0)]
		pub fn request_preimage(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			T::ManagerOrigin::ensure_origin(origin)?;
			Self::do_request_preimage(hash);
			Ok(())
		}

		/// Clear the request for a preimage.
		#[pallet::weight(0)]
		pub fn clear_request(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			T::ManagerOrigin::ensure_origin(origin)?;
			Self::do_clear_request(hash);
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Ensure that the origin is either the `ManagerOrigin` or a signed origin.
	fn ensure_signed_or_manager(origin: T::Origin) -> Result<Option<T::AccountId>, BadOrigin> {
		if T::ManagerOrigin::ensure_origin(origin.clone()).is_ok() {
			return Ok(None)
		}
		let who = ensure_signed(origin)?;
		Ok(Some(who))
	}

	/// Store some preimage on chain from a trusted source.
	///
	/// If the preimage is already uploaded, we increase the reference counter, ensuring it is
	/// not cleared before all uses of this preimage is complete.
	fn note_system_bytes(bounded_vec: BoundedVec<u8, T::MaxSize>) {
		let hash = T::Hashing::hash(&bounded_vec);
		Preimages::<T>::mutate_exists(hash, |maybe_preimage| {
			if let Some(preimage) = maybe_preimage {
				// If the preimage already exists, it could be owned by a user.
				// We have the system take over control of the preimage.
				match &preimage.ref_count {
					RefCount::User(who, deposit) => {
						T::Currency::unreserve(who, *deposit);
						preimage.ref_count = RefCount::System(One::one());
					},
					RefCount::System(mut count) => {
						count.saturating_inc();
					},
				}
			} else {
				*maybe_preimage = Some(Preimage {
					preimage: bounded_vec,
					ref_count: RefCount::System(One::one()),
				})
			}
		});

		Self::deposit_event(Event::Noted { hash });
	}

	/// Store some preimage on chain.
	///
	/// We verify that the preimage is within the bounds of what the pallet supports.
	///
	/// If the preimage was requested to be uploaded, then the user pays no deposits or tx fees.
	fn note_user_bytes(
		bounded_vec: BoundedVec<u8, T::MaxSize>,
		depositor: T::AccountId,
	) -> Result<bool, DispatchError> {
		let hash = T::Hashing::hash(&bounded_vec);
		ensure!(!Preimages::<T>::contains_key(hash), Error::<T>::AlreadyNoted);

		// We take a deposit only if there is a provided depositor, and the preimage was not
		// previously requested. This also allows the tx to pay no fee.
		let requests = Requests::<T>::take(hash);
		let ref_count = if requests > 0 {
			RefCount::System(requests)
		} else {
			let length = bounded_vec.len() as u32;
			let deposit = T::BaseDeposit::get()
				.saturating_add(T::ByteDeposit::get().saturating_mul(length.into()));
			T::Currency::reserve(&depositor, deposit)?;
			RefCount::User(depositor, deposit)
		};

		// Return whether this was requested by the system.
		let system_request = match ref_count {
			RefCount::System(_) => true,
			RefCount::User(_, _) => false,
		};

		let preimage = Preimage { preimage: bounded_vec, ref_count };

		Preimages::<T>::insert(hash, preimage);
		Self::deposit_event(Event::Noted { hash });

		Ok(system_request)
	}

	// This function will add a hash to the list of requested preimages.
	//
	// If the preimage already exists before the request is made, the deposit for the preimage is
	// returned to the user, and removed from their management.
	fn do_request_preimage(hash: T::Hash) {
		if let Some(mut preimage_metadata) = Preimages::<T>::get(hash) {
			match preimage_metadata.ref_count {
				RefCount::User(who, deposit) => {
					// Preimage already exists and owned by a user.
					// We return the deposit and change ownership to the system.
					T::Currency::unreserve(&who, deposit);
					preimage_metadata.ref_count = RefCount::System(One::one());
				},
				RefCount::System(mut count) => {
					// Preimage already exists and is owned by the system.
					// We simply increase the number of reference counters.
					count.saturating_inc();
				},
			}
			Preimages::<T>::insert(hash, preimage_metadata);
		} else {
			// Preimage does not exist yet, so increase the number of requests.
			Requests::<T>::mutate(hash, |requests| requests.saturating_inc());
			Self::deposit_event(Event::Requested { hash });
		}
	}

	// Clear a preimage from the storage of the chain, returning any deposit that may be reserved.
	//
	// If `maybe_owner` is provided, we verify that it is the correct owner before clearing the
	// data.
	//
	// If `maybe_owner` is not provided, this function cannot return an error.
	fn do_clear_preimage(hash: T::Hash, maybe_owner: Option<T::AccountId>) -> DispatchResult {
		Preimages::<T>::mutate_exists(hash, |maybe_value| -> DispatchResult {
			if let Some(preimage_metadata) = maybe_value {
				match &preimage_metadata.ref_count {
					RefCount::User(who, deposit) => {
						// If there is a deposit on hold, we return it if there is no `maybe_owner`
						// or if the owner matches.
						if let Some(owner) = maybe_owner {
							if &owner != who {
								// Ownership check did not pass. Return early without mutating
								// anything.
								return Err(Error::<T>::NotAuthorized.into())
							}
						}
						// At this point, we have done all the authorization needed, and we can
						// simply unreserve the deposit.
						T::Currency::unreserve(who, *deposit);
					},
					RefCount::System(mut count) => {
						// A regular user cannot clear a system preimage.
						if maybe_owner.is_some() {
							return Err(Error::<T>::NotAuthorized.into())
						}
						// If this preimage still has reference counters, decrement, and exit early.
						if count > 1 {
							count.saturating_dec();
							return Ok(())
						}
					},
				};

				// If we got this far, we are removing the value.
				*maybe_value = None;
				Self::deposit_event(Event::Cleared { hash });
			}
			Ok(())
		})
	}

	/// Clear a preimage request.
	fn do_clear_request(hash: T::Hash) {
		let count = Requests::<T>::get(hash);
		if count > 1 {
			Requests::<T>::insert(hash, count - 1);
		} else {
			Requests::<T>::remove(hash);
		}
	}
}

impl<T: Config> frame_support::traits::PreimageHandler<T::Hash> for Pallet<T> {
	type MaxSize = T::MaxSize;

	fn preimage_exists(hash: T::Hash) -> bool {
		Preimages::<T>::contains_key(hash)
	}

	fn preimage_requested(hash: T::Hash) -> bool {
		Requests::<T>::contains_key(hash)
	}

	fn get_preimage(hash: T::Hash) -> Option<Vec<u8>> {
		Preimages::<T>::get(hash).map(|preimage| preimage.preimage.to_vec())
	}

	fn note_preimage(bytes: BoundedVec<u8, Self::MaxSize>) {
		Self::note_system_bytes(bytes)
	}

	fn request_preimage(hash: T::Hash) {
		Self::do_request_preimage(hash)
	}

	fn clear_preimage(hash: T::Hash) {
		// Should never fail if authorization check is skipped.
		let res = Self::do_clear_preimage(hash, None);
		debug_assert!(res.is_ok(), "do_clear_preimage failed when authorization check was skipped");
	}

	fn clear_request(hash: T::Hash) {
		Self::do_clear_request(hash);
	}
}
