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

//! A minimal wrapper around the [`frame_support::storage::StoragePagedList`].

#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]

pub use pallet::*;

mod mock;
mod tests;

use codec::FullCodec;
use frame_support::traits::StorageInstance;
use frame_support::traits::PalletInfoAccess;
use frame_support::pallet_prelude::StorageList;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, storage::types::StoragePagedList};

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// This type alias is what FRAME normally get us.
	pub type List<T> = StoragePagedList<
		ListPrefix<T>,
		Blake2_128Concat,
		<T as Config>::Value,
		<T as Config>::ValuesPerPage,
		<T as Config>::MaxPages,
	>;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Value: FullCodec + Clone + MaxEncodedLen;

		#[pallet::constant]
		type ValuesPerPage: Get<u32>;

		#[pallet::constant]
		type MaxPages: Get<Option<u32>>;
	}

	#[pallet::event]
	pub enum Event<T: Config> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

/// The storage prefix for the list.
pub struct ListPrefix<T>(core::marker::PhantomData<T>);

impl<T: Config> StorageInstance for ListPrefix<T> {
	fn pallet_prefix() -> &'static str {
		crate::Pallet::<T>::module_name() // TODO double check
	}
	const STORAGE_PREFIX: &'static str = "list";
}

// Pass everything through to the underlying list.
impl<T: Config> StorageList<T::Value> for Pallet<T> {
	type Iterator = <List<T> as StorageList<T::Value>>::Iterator;
	type Appendix = <List<T> as StorageList<T::Value>>::Appendix;

	fn iter() -> Self::Iterator {
		List::<T>::iter()
	}

	fn drain() -> Self::Iterator {
		List::<T>::drain()
	}

	fn appendix() -> Self::Appendix {
		List::<T>::appendix()
	}
}
