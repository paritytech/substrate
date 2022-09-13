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

//! # Utility Pallet
//! A stateless pallet with helpers for dispatch management which does no re-authentication.
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! This pallet contains two basic pieces of functionality:
//! - Batch dispatch: A stateless operation, allowing any origin to execute multiple calls in a
//!   single dispatch. This can be useful to amalgamate proposals, combining `set_code` with
//!   corresponding `set_storage`s, for efficient multiple payouts with just a single signature
//!   verify, or in combination with one of the other two dispatch functionality.
//! - Pseudonymal dispatch: A stateless operation, allowing a signed origin to execute a call from
//!   an alternative signed origin. Each account has 2 * 2**16 possible "pseudonyms" (alternative
//!   account IDs) and these can be stacked. This can be useful as a key management tool, where you
//!   need multiple distinct accounts (e.g. as controllers for many staking accounts), but where
//!   it's perfectly fine to have each of them controlled by the same underlying keypair. Derivative
//!   accounts are, for the purposes of proxy filtering considered exactly the same as the origin
//!   and are thus hampered with the origin's filters.
//!
//! Since proxy filters are respected in all dispatches of this pallet, it should never need to be
//! filtered by any proxy.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For batch dispatch
//! * `batch` - Dispatch multiple calls from the sender's origin.
//!
//! #### For pseudonymal dispatch
//! * `as_derivative` - Dispatch a call from a derivative signed origin.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod tests;
pub mod weights;

use codec::{Decode, Encode};
use frame_support::{
	dispatch::PostDispatchInfo,
	traits::{IsSubType, OriginTrait, UnfilteredDispatchable},
	weights::{extract_actual_weight, GetDispatchInfo},
};
use sp_core::TypeId;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Dispatchable, TrailingZeroInput};
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
		type RuntimeEvent: From<Event> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: Parameter
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ From<frame_system::Call<Self>>
			+ UnfilteredDispatchable<Origin = Self::Origin>
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// The caller origin, overarching type of all pallets origins.
		type PalletsOrigin: Parameter +
			Into<<Self as frame_system::Config>::Origin> +
			IsType<<<Self as frame_system::Config>::Origin as frame_support::traits::OriginTrait>::PalletsOrigin>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event {
		/// Batch of dispatches did not complete fully. Index of first failing dispatch given, as
		/// well as the error.
		BatchInterrupted { index: u32, error: DispatchError },
		/// Batch of dispatches completed fully with no error.
		BatchCompleted,
		/// Batch of dispatches completed but has errors.
		BatchCompletedWithErrors,
		/// A single item within a Batch of dispatches has completed with no error.
		ItemCompleted,
		/// A single item within a Batch of dispatches has completed with error.
		ItemFailed { error: DispatchError },
		/// A call was dispatched.
		DispatchedAs { result: DispatchResult },
	}

	// Align the call size to 1KB. As we are currently compiling the runtime for native/wasm
	// the `size_of` of the `Call` can be different. To ensure that this don't leads to
	// mismatches between native/wasm or to different metadata for the same runtime, we
	// algin the call size. The value is choosen big enough to hopefully never reach it.
	const CALL_ALIGN: u32 = 1024;

	#[pallet::extra_constants]
	impl<T: Config> Pallet<T> {
		/// The limit on the number of batched calls.
		fn batched_calls_limit() -> u32 {
			let allocator_limit = sp_core::MAX_POSSIBLE_ALLOCATION;
			let call_size = ((sp_std::mem::size_of::<<T as Config>::RuntimeCall>() as u32 +
				CALL_ALIGN - 1) / CALL_ALIGN) *
				CALL_ALIGN;
			// The margin to take into account vec doubling capacity.
			let margin_factor = 3;

			allocator_limit / margin_factor / call_size
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			// If you hit this error, you need to try to `Box` big dispatchable parameters.
			assert!(
				sp_std::mem::size_of::<<T as Config>::RuntimeCall>() as u32 <= CALL_ALIGN,
				"Call enum size should be smaller than {} bytes.",
				CALL_ALIGN,
			);
		}
	}

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
			let dispatch_infos = calls.iter().map(|call| call.get_dispatch_info()).collect::<Vec<_>>();
			let dispatch_weight = dispatch_infos.iter()
				.map(|di| di.weight)
				.fold(Weight::zero(), |total: Weight, weight: Weight| total.saturating_add(weight))
				.saturating_add(T::WeightInfo::batch(calls.len() as u32));
			let dispatch_class = {
				let all_operational = dispatch_infos.iter()
					.map(|di| di.class)
					.all(|class| class == DispatchClass::Operational);
				if all_operational {
					DispatchClass::Operational
				} else {
					DispatchClass::Normal
				}
			};
			(dispatch_weight, dispatch_class)
		})]
		pub fn batch(
			origin: OriginFor<T>,
			calls: Vec<<T as Config>::RuntimeCall>,
		) -> DispatchResultWithPostInfo {
			let is_root = ensure_root(origin.clone()).is_ok();
			let calls_len = calls.len();
			ensure!(calls_len <= Self::batched_calls_limit() as usize, Error::<T>::TooManyCalls);

			// Track the actual weight of each of the batch calls.
			let mut weight = Weight::zero();
			for (index, call) in calls.into_iter().enumerate() {
				let info = call.get_dispatch_info();
				// If origin is root, don't apply any dispatch filters; root can call anything.
				let result = if is_root {
					call.dispatch_bypass_filter(origin.clone())
				} else {
					call.dispatch(origin.clone())
				};
				// Add the weight of this call.
				weight = weight.saturating_add(extract_actual_weight(&result, &info));
				if let Err(e) = result {
					Self::deposit_event(Event::BatchInterrupted {
						index: index as u32,
						error: e.error,
					});
					// Take the weight of this function itself into account.
					let base_weight = T::WeightInfo::batch(index.saturating_add(1) as u32);
					// Return the actual used weight + base_weight of this call.
					return Ok(Some(base_weight + weight).into())
				}
				Self::deposit_event(Event::ItemCompleted);
			}
			Self::deposit_event(Event::BatchCompleted);
			let base_weight = T::WeightInfo::batch(calls_len as u32);
			Ok(Some(base_weight + weight).into())
		}

		/// Send a call through an indexed pseudonym of the sender.
		///
		/// Filter from origin are passed along. The call will be dispatched with an origin which
		/// use the same filter as the origin of this call.
		///
		/// NOTE: If you need to ensure that any account-based filtering is not honored (i.e.
		/// because you expect `proxy` to have been used prior in the call stack and you do not want
		/// the call restrictions to apply to any sub-accounts), then use `as_multi_threshold_1`
		/// in the Multisig pallet instead.
		///
		/// NOTE: Prior to version *12, this was called `as_limited_sub`.
		///
		/// The dispatch origin for this call must be _Signed_.
		#[pallet::weight({
			let dispatch_info = call.get_dispatch_info();
			(
				T::WeightInfo::as_derivative()
					// AccountData for inner call origin accountdata.
					.saturating_add(T::DbWeight::get().reads_writes(1, 1))
					.saturating_add(dispatch_info.weight),
				dispatch_info.class,
			)
		})]
		pub fn as_derivative(
			origin: OriginFor<T>,
			index: u16,
			call: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResultWithPostInfo {
			let mut origin = origin;
			let who = ensure_signed(origin.clone())?;
			let pseudonym = Self::derivative_account_id(who, index);
			origin.set_caller_from(frame_system::RawOrigin::Signed(pseudonym));
			let info = call.get_dispatch_info();
			let result = call.dispatch(origin);
			// Always take into account the base weight of this call.
			let mut weight = T::WeightInfo::as_derivative()
				.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			// Add the real weight of the dispatch.
			weight = weight.saturating_add(extract_actual_weight(&result, &info));
			result
				.map_err(|mut err| {
					err.post_info = Some(weight).into();
					err
				})
				.map(|_| Some(weight).into())
		}

		/// Send a batch of dispatch calls and atomically execute them.
		/// The whole transaction will rollback and fail if any of the calls failed.
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
		#[pallet::weight({
			let dispatch_infos = calls.iter().map(|call| call.get_dispatch_info()).collect::<Vec<_>>();
			let dispatch_weight = dispatch_infos.iter()
				.map(|di| di.weight)
				.fold(Weight::zero(), |total: Weight, weight: Weight| total.saturating_add(weight))
				.saturating_add(T::WeightInfo::batch_all(calls.len() as u32));
			let dispatch_class = {
				let all_operational = dispatch_infos.iter()
					.map(|di| di.class)
					.all(|class| class == DispatchClass::Operational);
				if all_operational {
					DispatchClass::Operational
				} else {
					DispatchClass::Normal
				}
			};
			(dispatch_weight, dispatch_class)
		})]
		pub fn batch_all(
			origin: OriginFor<T>,
			calls: Vec<<T as Config>::RuntimeCall>,
		) -> DispatchResultWithPostInfo {
			let is_root = ensure_root(origin.clone()).is_ok();
			let calls_len = calls.len();
			ensure!(calls_len <= Self::batched_calls_limit() as usize, Error::<T>::TooManyCalls);

			// Track the actual weight of each of the batch calls.
			let mut weight = Weight::zero();
			for (index, call) in calls.into_iter().enumerate() {
				let info = call.get_dispatch_info();
				// If origin is root, bypass any dispatch filter; root can call anything.
				let result = if is_root {
					call.dispatch_bypass_filter(origin.clone())
				} else {
					let mut filtered_origin = origin.clone();
					// Don't allow users to nest `batch_all` calls.
					filtered_origin.add_filter(
						move |c: &<T as frame_system::Config>::RuntimeCall| {
							let c = <T as Config>::RuntimeCall::from_ref(c);
							!matches!(c.is_sub_type(), Some(Call::batch_all { .. }))
						},
					);
					call.dispatch(filtered_origin)
				};
				// Add the weight of this call.
				weight = weight.saturating_add(extract_actual_weight(&result, &info));
				result.map_err(|mut err| {
					// Take the weight of this function itself into account.
					let base_weight = T::WeightInfo::batch_all(index.saturating_add(1) as u32);
					// Return the actual used weight + base_weight of this call.
					err.post_info = Some(base_weight + weight).into();
					err
				})?;
				Self::deposit_event(Event::ItemCompleted);
			}
			Self::deposit_event(Event::BatchCompleted);
			let base_weight = T::WeightInfo::batch_all(calls_len as u32);
			Ok(Some(base_weight.saturating_add(weight)).into())
		}

		/// Dispatches a function call with a provided origin.
		///
		/// The dispatch origin for this call must be _Root_.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB write (event).
		/// - Weight of derivative `call` execution + T::WeightInfo::dispatch_as().
		/// # </weight>
		#[pallet::weight({
			let dispatch_info = call.get_dispatch_info();
			(
				T::WeightInfo::dispatch_as()
					.saturating_add(dispatch_info.weight),
				dispatch_info.class,
			)
		})]
		pub fn dispatch_as(
			origin: OriginFor<T>,
			as_origin: Box<T::PalletsOrigin>,
			call: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let res = call.dispatch_bypass_filter((*as_origin).into());

			Self::deposit_event(Event::DispatchedAs {
				result: res.map(|_| ()).map_err(|e| e.error),
			});
			Ok(())
		}

		/// Send a batch of dispatch calls.
		/// Unlike `batch`, it allows errors and won't interrupt.
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
		#[pallet::weight({
			let dispatch_infos = calls.iter().map(|call| call.get_dispatch_info()).collect::<Vec<_>>();
			let dispatch_weight = dispatch_infos.iter()
				.map(|di| di.weight)
				.fold(Weight::zero(), |total: Weight, weight: Weight| total.saturating_add(weight))
				.saturating_add(T::WeightInfo::force_batch(calls.len() as u32));
			let dispatch_class = {
				let all_operational = dispatch_infos.iter()
					.map(|di| di.class)
					.all(|class| class == DispatchClass::Operational);
				if all_operational {
					DispatchClass::Operational
				} else {
					DispatchClass::Normal
				}
			};
			(dispatch_weight, dispatch_class)
		})]
		pub fn force_batch(
			origin: OriginFor<T>,
			calls: Vec<<T as Config>::RuntimeCall>,
		) -> DispatchResultWithPostInfo {
			let is_root = ensure_root(origin.clone()).is_ok();
			let calls_len = calls.len();
			ensure!(calls_len <= Self::batched_calls_limit() as usize, Error::<T>::TooManyCalls);

			// Track the actual weight of each of the batch calls.
			let mut weight = Weight::zero();
			// Track failed dispatch occur.
			let mut has_error: bool = false;
			for call in calls.into_iter() {
				let info = call.get_dispatch_info();
				// If origin is root, don't apply any dispatch filters; root can call anything.
				let result = if is_root {
					call.dispatch_bypass_filter(origin.clone())
				} else {
					call.dispatch(origin.clone())
				};
				// Add the weight of this call.
				weight = weight.saturating_add(extract_actual_weight(&result, &info));
				if let Err(e) = result {
					has_error = true;
					Self::deposit_event(Event::ItemFailed { error: e.error });
				} else {
					Self::deposit_event(Event::ItemCompleted);
				}
			}
			if has_error {
				Self::deposit_event(Event::BatchCompletedWithErrors);
			} else {
				Self::deposit_event(Event::BatchCompleted);
			}
			let base_weight = T::WeightInfo::batch(calls_len as u32);
			Ok(Some(base_weight.saturating_add(weight)).into())
		}
	}
}

/// A pallet identifier. These are per pallet and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedUtilityPalletId(u16);

impl TypeId for IndexedUtilityPalletId {
	const TYPE_ID: [u8; 4] = *b"suba";
}

impl<T: Config> Pallet<T> {
	/// Derive a derivative account ID from the owner account and the sub-account index.
	pub fn derivative_account_id(who: T::AccountId, index: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, index).using_encoded(blake2_256);
		Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
			.expect("infinite length input; no invalid inputs for type; qed")
	}
}
