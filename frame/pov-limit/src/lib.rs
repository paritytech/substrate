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

//! # Pov Limit Pallet
//!
//! Pallet that controls compute usage and PoV size usage. The parameters for
//! the usage are configured by root and are stored as `StorageValue`s.
//!
//! NOTE: This is only meant to be used for testing.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

use frame_support::{pallet_prelude::*, traits::GenesisBuild};
use sp_core::{Blake2Hasher, Hasher};
use sp_runtime::Perbill;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The number of times the hash function should be called to fill up
		/// all the block's weight.
		#[pallet::constant]
		type HashesForFull: Get<u32>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	pub(crate) type Compute<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	#[pallet::storage]
	pub(crate) type Storage<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub compute: Perbill,
		pub storage: u32,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self { compute: Default::default(), storage: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			Compute::<T>::set(self.compute);
			Storage::<T>::set(self.storage);
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_idle(_: BlockNumberFor<T>, remaining_weight: Weight) -> Weight {
			let mut weight = T::DbWeight::get().reads(1);

			for i in 0..(Compute::<T>::get().mul_ceil(T::HashesForFull::get())) {
				Blake2Hasher::hash(&i.to_le_bytes());
			}

			for i in 0..Storage::<T>::get() {
				weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
				if remaining_weight.any_lt(weight) {
					weight = remaining_weight;
					break
				}

				storage::unhashed::put(&i.to_le_bytes(), &i.to_le_bytes());
				let _: Option<Vec<u8>> = storage::unhashed::get(&i.to_le_bytes());
			}

			weight
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set the `Compute` storage value that determines how much of the
		/// block's weight to use during `on_initialize`.
		///
		/// Only callable by Root.
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_compute(origin: OriginFor<T>, compute: Perbill) -> DispatchResult {
			let _ = ensure_root(origin)?;
			Compute::<T>::set(compute);

			Ok(())
		}

		/// Set the `Storage` storage value that determines the PoV size usage
		/// for each block.
		///
		/// Only callable by Root.
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_storage(origin: OriginFor<T>, storage: u32) -> DispatchResult {
			let _ = ensure_root(origin)?;
			Storage::<T>::set(storage);

			Ok(())
		}
	}
}
