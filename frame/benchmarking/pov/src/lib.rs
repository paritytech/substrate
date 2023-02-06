// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! End-to-end testing pallet for PoV benchmarking. Should only be deployed in a  testing runtime.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod tests;
mod weights;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_std::prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::storage]
	pub(crate) type Value<T: Config> = StorageValue<Value = u32, QueryKind = OptionQuery>;

	#[pallet::storage]
	pub(crate) type Value2<T: Config> = StorageValue<Value = u32, QueryKind = OptionQuery>;

	/// A value without a MEL bound.
	#[pallet::storage]
	#[pallet::unbounded]
	pub(crate) type UnboundedValue<T: Config> =
		StorageValue<Value = Vec<u8>, QueryKind = OptionQuery>;

	/// A value with a MEL bound of 32 byte.
	#[pallet::storage]
	pub(crate) type BoundedValue<T: Config> =
		StorageValue<Value = BoundedVec<u8, ConstU32<32>>, QueryKind = OptionQuery>;

	/// 4MiB value.
	#[pallet::storage]
	pub(crate) type LargeValue<T: Config> =
		StorageValue<Value = BoundedVec<u8, ConstU32<{ 1 << 22 }>>, QueryKind = OptionQuery>;

	#[pallet::storage]
	pub(crate) type LargeValue2<T: Config> =
		StorageValue<Value = BoundedVec<u8, ConstU32<{ 1 << 22 }>>, QueryKind = OptionQuery>;

	/// A map with a maximum of 1M entries.
	#[pallet::storage]
	pub(crate) type Map1M<T: Config> = StorageMap<
		Hasher = Blake2_256,
		Key = u32,
		Value = u32,
		QueryKind = OptionQuery,
		MaxValues = ConstU32<1_000_000>,
	>;

	/// A map with a maximum of 16M entries.
	#[pallet::storage]
	pub(crate) type Map16M<T: Config> = StorageMap<
		Hasher = Blake2_256,
		Key = u32,
		Value = u32,
		QueryKind = OptionQuery,
		MaxValues = ConstU32<16_000_000>,
	>;

	#[pallet::storage]
	pub(crate) type DoubleMap1M<T: Config> = StorageDoubleMap<
		Hasher1 = Blake2_256,
		Hasher2 = Blake2_256,
		Key1 = u32,
		Key2 = u32,
		Value = u32,
		QueryKind = OptionQuery,
		MaxValues = ConstU32<1_000_000>,
	>;

	#[pallet::storage]
	#[pallet::unbounded]
	pub(crate) type UnboundedMap<T: Config> =
		StorageMap<Hasher = Blake2_256, Key = u32, Value = Vec<u32>, QueryKind = OptionQuery>;

	#[pallet::storage]
	#[pallet::unbounded]
	pub(crate) type UnboundedMap2<T: Config> =
		StorageMap<Hasher = Blake2_256, Key = u32, Value = Vec<u32>, QueryKind = OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		TestEvent,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn emit_event(_origin: OriginFor<T>) -> DispatchResult {
			Self::deposit_event(Event::TestEvent);
			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn noop(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}
