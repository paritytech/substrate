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

use crate::{Config, Pallet, Weight, LOG_TARGET};
use frame_support::{pallet_prelude::*, storage::migration, traits::OnRuntimeUpgrade};
use log;

/// The current storage version.
pub const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

/// Wrapper for all migrations of this pallet.
pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
	let onchain_version = Pallet::<T, I>::on_chain_storage_version();
	let mut weight: Weight = 0;

	if onchain_version < 1 {
		weight = weight.saturating_add(v0_to_v1::migrate::<T, I>());
	}

	STORAGE_VERSION.put::<Pallet<T, I>>();
	weight = weight.saturating_add(T::DbWeight::get().writes(1));

	weight
}

/// Implements `OnRuntimeUpgrade` trait.
pub struct Migration<T, I = ()>(PhantomData<(T, I)>);

impl<T: Config<I>, I: 'static> OnRuntimeUpgrade for Migration<T, I> {
	fn on_runtime_upgrade() -> Weight {
		migrate::<T, I>()
	}
}

/// v0_to_v1: `UpForKicking` is replaced by a retirement period.
mod v0_to_v1 {
	use super::*;

	pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
		if migration::clear_storage_prefix(
			<Pallet<T, I>>::name().as_bytes(),
			b"UpForKicking",
			b"",
			None,
			None,
		)
		.maybe_cursor
		.is_some()
		{
			log::error!(
				target: LOG_TARGET,
				"Storage prefix 'UpForKicking' is not completely cleared."
			);
		}

		T::DbWeight::get().writes(1)
	}
}
