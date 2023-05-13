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

//! A minimal wrapper around the [`paged_list::StoragePagedList`].

#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]

pub use pallet::*;

pub mod mock;
mod paged_list;
mod tests;

use codec::FullCodec;
use frame_support::{
	pallet_prelude::StorageList,
	traits::{PalletInfoAccess, StorageInstance},
};
pub use paged_list::StoragePagedList;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(_);

	/// This type alias is what FRAME normally get us.
	pub type List<T, I> = StoragePagedList<
		ListPrefix<T, I>,
		Blake2_128Concat,
		<T as Config<I>>::Value,
		<T as Config<I>>::ValuesPerPage,
		<T as Config<I>>::MaxPages,
	>;

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Value: FullCodec + Clone + MaxEncodedLen;

		#[pallet::constant]
		type ValuesPerPage: Get<u32>;

		#[pallet::constant]
		type MaxPages: Get<Option<u32>>;
	}

	#[pallet::event]
	pub enum Event<T: Config<I>, I: 'static = ()> {}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {}
}

// This exposes the list functionality to other pallets.
impl<T: Config<I>, I: 'static> StorageList<T::Value> for Pallet<T, I> {
	type Iterator = <List<T, I> as StorageList<T::Value>>::Iterator;
	type Appendix = <List<T, I> as StorageList<T::Value>>::Appendix;

	fn iter() -> Self::Iterator {
		List::<T, I>::iter()
	}

	fn drain() -> Self::Iterator {
		List::<T, I>::drain()
	}

	fn appendix() -> Self::Appendix {
		List::<T, I>::appendix()
	}
}

// Helper stuff for tests.
#[cfg(feature = "std")]
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Return the elements of the list.
	pub fn as_vec() -> Vec<T::Value> {
		<Self as frame_support::storage::StorageList<_>>::iter().collect()
	}

	/// Remove and return all elements of the list.
	pub fn as_drained_vec() -> Vec<T::Value> {
		<Self as frame_support::storage::StorageList<_>>::drain().collect()
	}
}

/// The storage prefix for the list.
///
/// Unique for each instance.
pub struct ListPrefix<T, I>(core::marker::PhantomData<(T, I)>);

impl<T: Config<I>, I: 'static> StorageInstance for ListPrefix<T, I> {
	fn pallet_prefix() -> &'static str {
		crate::Pallet::<T, I>::name()
	}

	const STORAGE_PREFIX: &'static str = "paged_list";
}
