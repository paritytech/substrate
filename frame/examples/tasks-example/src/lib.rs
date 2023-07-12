// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! <!-- markdown-link-check-disable -->
//! # Dev Mode Example Pallet
//!
//! A simple example of a FRAME pallet demonstrating
//! the ease of requirements for a pallet in dev mode.
//!
//! Run `cargo doc --package pallet-dev-mode --open` to view this pallet's documentation.
//!
//! **Dev mode is not meant to be used in production.**

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{dispatch::DispatchResult, traits::Task};
// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;
use sp_runtime::DispatchError;

#[derive(Clone, PartialEq, Eq, Encode, Decode)]
pub enum ExampleTask {
	Increment,
	Decrement,
}

pub trait PalletTask<T: Config>: Task {
	type Config: frame_system::Config;
	fn is_valid(&self, config: &Self::Config) -> bool;
	fn run(&self, config: &Self::Config) -> Result<(), DispatchError>;
}

impl Task for ExampleTask {
	type Enumeration = std::vec::IntoIter<ExampleTask>;

	const TASK_INDEX: usize = 0;

	fn enumerate() -> Self::Enumeration {
		vec![ExampleTask::Increment, ExampleTask::Decrement].into_iter()
	}

	fn is_valid(&self) -> bool {
		todo!()
	}

	fn run(&self) -> Result<(), DispatchError> {
		todo!()
	}
}

impl<T: Config> PalletTask<T> for ExampleTask {
	type Config = T;

	fn is_valid(&self, _config: &Self::Config) -> bool {
		// You can implement some validation logic here
		// For demonstration purposes, we'll just return true
		true
	}

	fn run(&self, _config: &Self::Config) -> Result<(), DispatchError> {
		match self {
			ExampleTask::Increment => {
				// You can call some functions on your pallet here
				// For demonstration purposes, we'll just print a message
				println!("Increment task running");
			},
			ExampleTask::Decrement => {
				// You can call some functions on your pallet here
				// For demonstration purposes, we'll just print a message
				println!("Decrement task running");
			},
		}
		Ok(())
	}
}

/// Enable `dev_mode` for this pallet.
#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	// Simple declaration of the `Pallet` type. It is placeholder we use to implement traits and
	// method.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	#[pallet::getter(fn value)]
	pub type Value<T: Config> = StorageValue<_, u8>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		// No need to define a `call_index` attribute here because of `dev_mode`.
		// No need to define a `weight` attribute here because of `dev_mode`.
		pub fn add_dummy(origin: OriginFor<T>, id: T::AccountId) -> DispatchResult {
			ensure_root(origin)?;

			if let Some(mut dummies) = Dummy::<T>::get() {
				dummies.push(id.clone());
				Dummy::<T>::set(Some(dummies));
			} else {
				Dummy::<T>::set(Some(vec![id.clone()]));
			}

			// Let's deposit an event to let the outside world know this happened.
			Self::deposit_event(Event::AddDummy { account: id });

			Ok(())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		AddDummy { account: T::AccountId },
	}

	/// The MEL requirement for bounded pallets is skipped by `dev_mode`.
	/// This means that all storages are marked as unbounded.
	/// This is equivalent to specifying `#[pallet::unbounded]` on this type definitions.
	/// When the dev_mode is removed, we would need to implement implement `MaxEncodedLen`.
	#[pallet::storage]
	pub type Dummy<T: Config> = StorageValue<_, Vec<T::AccountId>>;

	/// The Hasher requirement is skipped by `dev_mode`. So, second parameter can be `_`
	/// and `Blake2_128Concat` is used as a default.
	/// When the dev_mode is removed, we would need to specify the hasher like so:
	/// `pub type Bar<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, T::Balance>;`.
	#[pallet::storage]
	pub type Bar<T: Config> = StorageMap<_, _, T::AccountId, u32>;
}
