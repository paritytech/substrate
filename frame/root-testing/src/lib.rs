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

//! # Root Testing Pallet
//! Pallet that contains extrinsics that can be usefull in testing.
//!
//! NOTE: This pallet should only be used for testing purposes.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::dispatch::DispatchErrorWithPostInfo;
use frame_system::WeightInfo;
use sp_runtime::Perbill;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	pub enum Event<T: Config> {}

	#[pallet::error]
	pub enum Error<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// A dispatch that will fill the block weight up to the given ratio.
		#[pallet::weight(*_ratio * T::BlockWeights::get().max_block)]
		pub fn fill_block(origin: OriginFor<T>, _ratio: Perbill) -> DispatchResultWithPostInfo {
			match ensure_root(origin) {
				Ok(_) => Ok(().into()),
				Err(_) => {
					// roughly same as a 4 byte remark since perbill is u32.
					Err(DispatchErrorWithPostInfo {
						post_info: Some(<T as frame_system::Config>::SystemWeightInfo::remark(
							4u32,
						))
						.into(),
						error: DispatchError::BadOrigin,
					})
				},
			}
		}
	}
}
