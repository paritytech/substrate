// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
//! of a hash on chain. This can be used by other pallets for storing and managing
//! large byte-blobs.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use sp_runtime::traits::{BadOrigin, DispatchInfoOf, Hash, Saturating, SignedExtension};
use sp_std::{prelude::*, cell::RefCell, borrow::Cow, collections::btree_map::BTreeMap};

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	ensure,
	pallet_prelude::Get,
	traits::{Currency, IsSubType, PreimageProvider, PreimageRecipient, ReservableCurrency, TempPreimageRecipient},
	weights::Pays,
	BoundedVec,
};
use scale_info::TypeInfo;
pub use weights::WeightInfo;

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

pub use pallet::*;

/// A type to note whether a preimage is owned by a user or the system.
#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub enum RequestStatus<AccountId, Balance> {
	/// The associated preimage has not yet been requested by the system. The given deposit (if
	/// some) is being held until either it becomes requested or the user retracts the primage.
	Unrequested(Option<(AccountId, Balance)>),
	/// There are a non-zero number of outstanding requests for this hash by this chain. If there
	/// is a preimage registered, then it may be removed iff this counter becomes zero.
	Requested(u32),
}

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo, RuntimeDebug)]
pub struct UnboundedBlob(Vec<u8>);
impl MaxEncodedLen for UnboundedBlob {
	fn max_encoded_len() -> usize {
		0
	}
}

impl AsRef<Vec<u8>> for UnboundedBlob {
	fn as_ref(&self) -> &Vec<u8> {
		&self.0
	}
}

impl From<Vec<u8>> for UnboundedBlob {
	fn from(t: Vec<u8>) -> Self {
		Self(t)
	}
}
impl From<UnboundedBlob> for Vec<u8> {
	fn from(t: UnboundedBlob) -> Self {
		t.0
	}
}
impl<'a> codec::EncodeLike<UnboundedBlob> for Vec<u8> {}
impl<'a> codec::EncodeLike<UnboundedBlob> for &'a Vec<u8> {}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The Weight information for this pallet.
		type WeightInfo: weights::WeightInfo;

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
		/// The preimage cannot be removed since it has not yet been noted.
		NotNoted,
		/// A preimage may not be removed when there are outstanding requests.
		Requested,
		/// The preimage request cannot be removed since no outstanding requests exist.
		NotRequested,
	}

	/// The request status of a given hash.
	#[pallet::storage]
	pub(super) type StatusFor<T: Config> =
		StorageMap<_, Identity, T::Hash, RequestStatus<T::AccountId, BalanceOf<T>>>;

	/// The preimages stored by this pallet.
	#[pallet::storage]
	pub(super) type PreimageFor<T: Config> =
		StorageMap<_, Identity, T::Hash, BoundedVec<u8, T::MaxSize>>;

	/// The preimages stored by this pallet.
	#[pallet::storage]
	//#[pallet::storage(write-only)]
	// This is not persisted
	pub(super) type TempPreimageFor<T: Config> = StorageMap<_, Identity, T::Hash, UnboundedBlob>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register a preimage on-chain.
		///
		/// If the preimage was previously requested, no fees or deposits are taken for providing
		/// the preimage. Otherwise, a deposit is taken proportional to the size of the preimage.
		#[pallet::weight(T::WeightInfo::note_preimage(bytes.len() as u32))]
		pub fn note_preimage(origin: OriginFor<T>, bytes: Vec<u8>) -> DispatchResultWithPostInfo {
			// We accept a signed origin which will pay a deposit, or a root origin where a deposit
			// is not taken.
			let maybe_sender = Self::ensure_signed_or_manager(origin)?;
			let bounded_vec =
				BoundedVec::<u8, T::MaxSize>::try_from(bytes).map_err(|()| Error::<T>::TooLarge)?;
			let system_requested = Self::note_bytes(bounded_vec, maybe_sender.as_ref())?;
			if system_requested || maybe_sender.is_none() {
				Ok(Pays::No.into())
			} else {
				Ok(().into())
			}
		}

		/// Clear an unrequested preimage from the runtime storage.
		#[pallet::weight(T::WeightInfo::unnote_preimage())]
		pub fn unnote_preimage(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			let maybe_sender = Self::ensure_signed_or_manager(origin)?;
			Self::do_unnote_preimage(&hash, maybe_sender)
		}

		/// Request a preimage be uploaded to the chain without paying any fees or deposits.
		///
		/// If the preimage requests has already been provided on-chain, we unreserve any deposit
		/// a user may have paid, and take the control of the preimage out of their hands.
		#[pallet::weight(T::WeightInfo::request_preimage())]
		pub fn request_preimage(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			T::ManagerOrigin::ensure_origin(origin)?;
			Self::do_request_preimage(&hash);
			Ok(())
		}

		/// Clear a previously made request for a preimage.
		///
		/// NOTE: THIS MUST NOT BE CALLED ON `hash` MORE TIMES THAN `request_preimage`.
		#[pallet::weight(T::WeightInfo::unrequest_preimage())]
		pub fn unrequest_preimage(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			T::ManagerOrigin::ensure_origin(origin)?;
			Self::do_unrequest_preimage(&hash)
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

	/// Store some preimage on chain.
	///
	/// We verify that the preimage is within the bounds of what the pallet supports.
	///
	/// If the preimage was requested to be uploaded, then the user pays no deposits or tx fees.
	fn note_bytes(
		preimage: BoundedVec<u8, T::MaxSize>,
		maybe_depositor: Option<&T::AccountId>,
	) -> Result<bool, DispatchError> {
		let hash = T::Hashing::hash(&preimage);
		ensure!(!PreimageFor::<T>::contains_key(hash), Error::<T>::AlreadyNoted);

		// We take a deposit only if there is a provided depositor, and the preimage was not
		// previously requested. This also allows the tx to pay no fee.
		let was_requested = match (StatusFor::<T>::get(hash), maybe_depositor) {
			(Some(RequestStatus::Requested(..)), _) => true,
			(Some(RequestStatus::Unrequested(..)), _) =>
				return Err(Error::<T>::AlreadyNoted.into()),
			(None, None) => {
				StatusFor::<T>::insert(hash, RequestStatus::Unrequested(None));
				false
			},
			(None, Some(depositor)) => {
				let length = preimage.len() as u32;
				let deposit = T::BaseDeposit::get()
					.saturating_add(T::ByteDeposit::get().saturating_mul(length.into()));
				T::Currency::reserve(depositor, deposit)?;
				let status = RequestStatus::Unrequested(Some((depositor.clone(), deposit)));
				StatusFor::<T>::insert(hash, status);
				false
			},
		};

		PreimageFor::<T>::insert(hash, preimage);
		Self::deposit_event(Event::Noted { hash });

		Ok(was_requested)
	}

	// This function will add a hash to the list of requested preimages.
	//
	// If the preimage already exists before the request is made, the deposit for the preimage is
	// returned to the user, and removed from their management.
	fn do_request_preimage(hash: &T::Hash) {
		let count = StatusFor::<T>::get(hash).map_or(1, |x| match x {
			RequestStatus::Requested(mut count) => {
				count.saturating_inc();
				count
			},
			RequestStatus::Unrequested(None) => 1,
			RequestStatus::Unrequested(Some((owner, deposit))) => {
				// Return the deposit - the preimage now has outstanding requests.
				T::Currency::unreserve(&owner, deposit);
				1
			},
		});
		StatusFor::<T>::insert(hash, RequestStatus::Requested(count));
		if count == 1 {
			Self::deposit_event(Event::Requested { hash: *hash });
		}
	}

	// Clear a preimage from the storage of the chain, returning any deposit that may be reserved.
	//
	// If `maybe_owner` is provided, we verify that it is the correct owner before clearing the
	// data.
	fn do_unnote_preimage(
		hash: &T::Hash,
		maybe_check_owner: Option<T::AccountId>,
	) -> DispatchResult {
		match StatusFor::<T>::get(hash).ok_or(Error::<T>::NotNoted)? {
			RequestStatus::Unrequested(Some((owner, deposit))) => {
				ensure!(maybe_check_owner.map_or(true, |c| c == owner), Error::<T>::NotAuthorized);
				T::Currency::unreserve(&owner, deposit);
			},
			RequestStatus::Unrequested(None) => {
				ensure!(maybe_check_owner.is_none(), Error::<T>::NotAuthorized);
			},
			RequestStatus::Requested(_) => return Err(Error::<T>::Requested.into()),
		}
		StatusFor::<T>::remove(hash);
		PreimageFor::<T>::remove(hash);
		Self::deposit_event(Event::Cleared { hash: *hash });
		Ok(())
	}

	/// Clear a preimage request.
	fn do_unrequest_preimage(hash: &T::Hash) -> DispatchResult {
		match StatusFor::<T>::get(hash).ok_or(Error::<T>::NotRequested)? {
			RequestStatus::Requested(mut count) if count > 1 => {
				count.saturating_dec();
				StatusFor::<T>::insert(hash, RequestStatus::Requested(count));
			},
			RequestStatus::Requested(count) => {
				debug_assert!(count == 1, "preimage request counter at zero?");
				PreimageFor::<T>::remove(hash);
				StatusFor::<T>::remove(hash);
				Self::deposit_event(Event::Cleared { hash: *hash });
			},
			RequestStatus::Unrequested(_) => return Err(Error::<T>::NotRequested.into()),
		}
		Ok(())
	}
}

thread_local! {
	static TEMP_PREIMAGES: RefCell<BTreeMap<Vec<u8>, Cow<[u8]>>> = RefCell::new(Default::default());
}

impl<T: Config> PreimageProvider<T::Hash> for Pallet<T> {
	fn have_preimage(hash: &T::Hash) -> bool {
		PreimageFor::<T>::contains_key(hash)
	}

	fn preimage_requested(hash: &T::Hash) -> bool {
		matches!(StatusFor::<T>::get(hash), Some(RequestStatus::Requested(..)))
	}

	fn get_preimage(hash: &T::Hash) -> Option<Cow<[u8]>> {
		TEMP_PREIMAGES.with(|t| hash.using_encoded(|e| t.borrow().get(e).map(|x| x.into()))
			.or_else(|| PreimageFor::<T>::get(hash).map(|preimage| preimage.to_vec().into()))
	}

	fn request_preimage(hash: &T::Hash) {
		Self::do_request_preimage(hash)
	}

	fn unrequest_preimage(hash: &T::Hash) {
		let res = Self::do_unrequest_preimage(hash);
		debug_assert!(res.is_ok(), "do_unrequest_preimage failed - counter underflow?");
	}
}

impl<T: Config> PreimageRecipient<T::Hash> for Pallet<T> {
	type MaxSize = T::MaxSize;

	fn note_preimage(bytes: BoundedVec<u8, Self::MaxSize>) {
		// We don't really care if this fails, since that's only the case if someone else has
		// already noted it.
		let _ = Self::note_bytes(bytes, None);
	}

	fn unnote_preimage(hash: &T::Hash) {
		// Should never fail if authorization check is skipped.
		let res = Self::do_unnote_preimage(hash, None);
		debug_assert!(res.is_ok(), "unnote_preimage failed - request outstanding?");
	}
}

/// A special preimage recipient which doesn't store it on-chain but in-memory for the duration of
/// the current runtime API function.
pub struct Temporary<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> TempPreimageRecipient<T::Hash> for Temporary<T> {
	fn note_preimage(bytes: Cow<&'static, [u8]>) {
		// We don't really care if this fails, since that's only the case if someone else has
		// already noted it.
		TEMP_PREIMAGES.with(|t| t.borrow_mut().insert(T::Hashing::hash(&bytes[..]).encode(), bytes));
	}

	fn unnote_preimage(hash: &T::Hash) {
		TEMP_PREIMAGES.with(|t| t.borrow_mut().remove(hash));
	}

	fn clear() {
		TEMP_PREIMAGES.with(|t| t.borrow_mut().clear());
	}
}
