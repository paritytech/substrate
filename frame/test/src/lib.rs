// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Test Pallet

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

//mod benchmarking;
//mod tests;
pub mod weights;

use codec::{Decode, Encode};
use frame_support::{
	dispatch::PostDispatchInfo,
	traits::{IsSubType, UnfilteredDispatchable},
	weights::{GetDispatchInfo},
};
use sp_core::TypeId;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::Dispatchable;
use sp_std::prelude::*;
pub use weights::WeightInfo;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// Configuration trait.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching call type.
		type Call: Parameter
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ From<frame_system::Call<Self>>
			+ UnfilteredDispatchable<Origin = Self::Origin>
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::Call>;

		/// The caller origin, overarching type of all pallets origins.
		type PalletsOrigin: Parameter +
			Into<<Self as frame_system::Config>::Origin> +
			IsType<<<Self as frame_system::Config>::Origin as frame_support::traits::OriginTrait>::PalletsOrigin>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::event]
	//#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event {
		Dummy,
	}

	// #[pallet::extra_constants]
	// impl<T: Config> Pallet<T> {
	// 	/// The limit on the number of batched calls.
	// 	fn batched_calls_limit() -> u32 {
	// 		let allocator_limit = sp_core::MAX_POSSIBLE_ALLOCATION;
	// 		let call_size = ((sp_std::mem::size_of::<<T as Config>::Call>() as u32 + CALL_ALIGN -
	// 			1) / CALL_ALIGN) * CALL_ALIGN;
	// 		// The margin to take into account vec doubling capacity.
	// 		let margin_factor = 3;

	// 		allocator_limit / margin_factor / call_size
	// 	}
	// }

	// #[pallet::hooks]
	// impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
	// 	fn integrity_test() {
	// 		// If you hit this error, you need to try to `Box` big dispatchable parameters.
	// 		assert!(
	// 			sp_std::mem::size_of::<<T as Config>::Call>() as u32 <= CALL_ALIGN,
	// 			"Call enum size should be smaller than {} bytes.",
	// 			CALL_ALIGN,
	// 		);
	// 	}
	// }

	#[pallet::error]
	pub enum Error<T> {
		/// Too many calls batched.
		TooManyCalls,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Send a batch of dispatch calls.
		///
		/// May be called from any origin.
		///
		/// - `calls`: The calls to be dispatched from the same origin. The number of call must not
		///   exceed the constant: `batched_calls_limit` (available in constant metadata).
		///
		/// If origin is root then call are dispatch without checking origin filter. (This includes
		/// bypassing `frame_system::Config::BaseCallFilter`).
		///
		/// # <weight>
		/// - Complexity: O(C) where C is the number of calls to be batched.
		/// # </weight>
		///
		/// This will return `Ok` in all circumstances. To determine the success of the batch, an
		/// event is deposited. If a call failed and the batch was interrupted, then the
		/// `BatchInterrupted` event is deposited, along with the number of successful calls made
		/// and the error of the failed call. If all were successful, then the `BatchCompleted`
		/// event is deposited.
		#[pallet::weight({
			(2, DispatchClass::Normal)
		})]
		pub fn batch(
			origin: OriginFor<T>,
			_calls: Vec<<T as Config>::Call>,
		) -> DispatchResultWithPostInfo {
			let _is_root = ensure_root(origin.clone()).is_ok();
			
			Ok(Some(2).into())
		}
	}
}

/// A pallet identifier. These are per pallet and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedTestPalletId(u16);

impl TypeId for IndexedTestPalletId {
	const TYPE_ID: [u8; 4] = *b"test";
}

impl<T: Config> Pallet<T> {
	/// Derive a derivative account ID from the owner account and the sub-account index.
	pub fn derivative_account_id(who: T::AccountId, index: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, index).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}
}
