// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Migrations for the AURA pallet.

use frame_support::{pallet_prelude::*, traits::Get, weights::Weight};

struct __LastTimestamp<T>(sp_std::marker::PhantomData<T>);
impl<T: RemoveLastTimestamp> frame_support::traits::StorageInstance for __LastTimestamp<T> {
	fn pallet_prefix() -> &'static str {
		T::PalletPrefix::get()
	}
	const STORAGE_PREFIX: &'static str = "LastTimestamp";
}

type LastTimestamp<T> = StorageValue<__LastTimestamp<T>, (), ValueQuery>;

pub trait RemoveLastTimestamp: super::Config {
	type PalletPrefix: Get<&'static str>;
}

/// Remove the `LastTimestamp` storage value.
///
/// This storage value was removed and replaced by `CurrentSlot`. As we only remove this storage
/// value, it is safe to call this method multiple times.
///
/// This migration requires a type `T` that implements [`RemoveLastTimestamp`].
pub fn remove_last_timestamp<T: RemoveLastTimestamp>() -> Weight {
	LastTimestamp::<T>::kill();
	T::DbWeight::get().writes(1)
}
