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
pub mod weights;

use frame_support::pallet_prelude::*;
use sp_runtime::Perbill;

pub use pallet::*;
pub use weights::WeightInfo;

pub trait Hasher {
	/// The output type of the hashing algorithm.
	type Out;

	/// Hashes a slice of bytes and returns the result.
	fn hash(_: &[u8]) -> Self::Out;
}

pub trait Reader {
	/// Reads some storage value and returns the weight consumed from reading.
	fn read<T: crate::Config>(_: &[u8]) -> Weight;
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Weight information for this pallet.
		type WeightInfo: WeightInfo;

		/// Type that implements the `Hasher` trait.
		type Hasher: Hasher;

		/// Type that implements the `Reader` trait.
		type Reader: Reader;
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

			let computation_weight_limit =
				Compute::<T>::get().mul_ceil(remaining_weight.ref_time());

			let mut value: u64 = 0;
			loop {
				if computation_weight_limit <
					weight.ref_time().saturating_add(T::WeightInfo::hash_value().ref_time())
				{
					break
				}
				weight = weight.saturating_add(T::WeightInfo::hash_value());
				Self::hash_value(value);
				value += 1;
			}

			for i in 0..Storage::<T>::get() {
				if remaining_weight.any_lt(weight) {
					weight = remaining_weight;
					break
				}

				let consumed_weight = T::Reader::read::<T>(&i.to_le_bytes());
				weight = weight.saturating_add(consumed_weight);
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
		#[pallet::call_index(0)]
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
		#[pallet::call_index(1)]
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_storage(origin: OriginFor<T>, storage: u32) -> DispatchResult {
			let _ = ensure_root(origin)?;
			Storage::<T>::set(storage);

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		pub fn hash_value(value: u64) {
			T::Hasher::hash(&value.to_le_bytes());
		}
	}
}
