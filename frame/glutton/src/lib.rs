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

//! # Glutton Pallet
//!
//! Pallet that consumes `ref_time` and `proof_size` of a block. Based on the
//! `Compute` and `Storage` parameters the pallet consumes the adequate amount
//! of weight.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use blake2::{Blake2b512, Digest};
use frame_support::{defensive, pallet_prelude::*, weights::WeightMeter};
use frame_system::pallet_prelude::*;
use sp_runtime::{traits::Zero, Perbill, Saturating};
use sp_std::{vec, vec::Vec};

pub use pallet::*;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event {
		/// The pallet has been initialized by root.
		PalletInitialized,
		/// The computation limit has been updated by root.
		ComputationLimitSet { compute: Perbill },
		/// The storage limit has been updated by root.
		StorageLimitSet { storage: Perbill },
	}

	#[pallet::storage]
	pub(crate) type Compute<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	#[pallet::storage]
	pub(crate) type Storage<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	#[pallet::storage]
	pub(super) type TrashData<T: Config> = StorageMap<_, Blake2_128Concat, u32, u32, OptionQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		/// The initial percentage of the `ref_time` to waste.
		pub compute: Perbill,
		/// The initial percentage of the `proof_size` to consume.
		pub storage: Perbill,
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
		fn integrity_test() {
			assert!(
				!T::WeightInfo::waste_ref_time_iter(1).ref_time().is_zero(),
				"Weight zero; would get stuck in an infinite loop"
			);
			assert!(
				!T::WeightInfo::waste_proof_size_none(1).proof_size().is_zero(),
				"Weight zero; would get stuck in an infinite loop"
			);
		}

		fn on_idle(_: BlockNumberFor<T>, remaining_weight: Weight) -> Weight {
			let mut meter = WeightMeter::from_limit(remaining_weight);
			if !meter.check_accrue(Self::read_limits_weight()) {
				return T::WeightInfo::empty_on_idle()
			}

			let proof_size_limit = Storage::<T>::get().mul_floor(meter.remaining().proof_size());
			let computation_weight_limit =
				Compute::<T>::get().mul_floor(meter.remaining().ref_time());
			let mut meter = WeightMeter::from_limit(Weight::from_parts(
				computation_weight_limit,
				proof_size_limit,
			));

			// First we start by wasting proof size.
			let mut num_proof_size = 0;
			while meter.can_accrue(
				T::WeightInfo::waste_proof_size_some(1)
					.max(T::WeightInfo::waste_proof_size_none(1)),
			) {
				let wasted = Self::waste_proof_size(num_proof_size);
				num_proof_size.saturating_inc();
				if wasted.is_zero() {
					// Do not get stuck in an infinite loop if no PoV can be consumed.
					break
				}
				if !meter.check_accrue(wasted) {
					defensive!("Could not consume waste_proof_size");
					break
				}
			}

			Self::waste_at_most_ref_time(&mut meter);
			meter.consumed
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Initializes the pallet by writing into `TrashData`.
		///
		/// Only callable by Root.
		#[pallet::call_index(0)]
		#[pallet::weight(T::DbWeight::get().writes((*trash_count).into()))]
		pub fn initialize_pallet(origin: OriginFor<T>, trash_count: u32) -> DispatchResult {
			ensure_root(origin)?;

			// Fill up the `TrashData` storage item.
			(0..trash_count).for_each(|i| TrashData::<T>::insert(i, i));

			Self::deposit_event(Event::PalletInitialized);
			Ok(())
		}

		/// Set the `Compute` storage value that determines how much of the
		/// block's weight `ref_time` to use during `on_idle`.
		///
		/// Only callable by Root.
		#[pallet::call_index(1)]
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_compute(origin: OriginFor<T>, compute: Perbill) -> DispatchResult {
			ensure_root(origin)?;
			Compute::<T>::set(compute);

			Self::deposit_event(Event::ComputationLimitSet { compute });
			Ok(())
		}

		/// Set the `Storage` storage value that determines the PoV size usage
		/// for each block.
		///
		/// Only callable by Root.
		#[pallet::call_index(2)]
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_storage(origin: OriginFor<T>, storage: Perbill) -> DispatchResult {
			ensure_root(origin)?;
			Storage::<T>::set(storage);

			Self::deposit_event(Event::StorageLimitSet { storage });
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		fn read_limits_weight() -> Weight {
			T::WeightInfo::read_limits().max(T::DbWeight::get().reads(2))
		}

		/// Wastes some `proof_size`. Receives a counter as an argument.
		fn waste_proof_size(counter: u32) -> Weight {
			if TrashData::<T>::get(counter).is_some() {
				T::WeightInfo::waste_proof_size_some(1)
			} else {
				T::WeightInfo::waste_proof_size_none(1)
			}
		}

		/// Waste at most the remaining ref time weight of `meter`.
		///
		/// Tries to come as close to the limit as possible.
		pub(crate) fn waste_at_most_ref_time(meter: &mut WeightMeter) {
			// Now we waste ref time.
			let mut clobber = vec![0u8; 64]; // There isn't a previous result.
			while meter.can_accrue(T::WeightInfo::waste_ref_time_iter(1)) {
				clobber = Self::waste_ref_time_iter(clobber);
				meter.defensive_saturating_accrue(T::WeightInfo::waste_ref_time_iter(1));
			}

			// By casting it into a vec we can hopefully prevent the compiler from optimizing it
			// out. Note that `Blake2b512` produces 64 bytes, this is therefore impossible - but the
			// compiler does not know that (hopefully).
			debug_assert!(clobber.len() == 64);
			if clobber == vec![0u8; 65] {
				TrashData::<T>::insert(0, clobber[0] as u32);
			}
		}

		/// Wastes some `ref_time`. Receives the previous result as an argument.
		pub(crate) fn waste_ref_time_iter(clobber: Vec<u8>) -> Vec<u8> {
			let mut hasher = Blake2b512::new();

			// Blake2 has a very high speed of hashing so we make multiple hashes with it to
			// waste more `ref_time` at once.
			(0..50).for_each(|_| {
				hasher.update(clobber.as_slice());
			});

			hasher.finalize().to_vec()
		}
	}
}
