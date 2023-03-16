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

use frame_support::{
	traits::{Get, OnRuntimeUpgrade},
	weights::Weight,
};

use crate::{Config, CurrentSetId, SetIdSession, LOG_TARGET};

/// Version 4.
pub mod v4;

/// This migration will clean up all stale set id -> session entries from the
/// `SetIdSession` storage map, only the latest `max_set_id_session_entries`
/// will be kept.
///
/// This migration should be added with a runtime upgrade that introduces the
/// `MaxSetIdSessionEntries` constant to the pallet (although it could also be
/// done later on).
pub struct CleanupSetIdSessionMap<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> OnRuntimeUpgrade for CleanupSetIdSessionMap<T> {
	fn on_runtime_upgrade() -> Weight {
		// NOTE: since this migration will loop over all stale entries in the
		// map we need to set some cutoff value, otherwise the migration might
		// take too long to run. for scenarios where there are that many entries
		// to cleanup a multiblock migration will be needed instead.
		if CurrentSetId::<T>::get() > 25_000 {
			log::warn!(
				target: LOG_TARGET,
				"CleanupSetIdSessionMap migration was aborted since there are too many entries to cleanup."
			);

			return T::DbWeight::get().reads(1)
		}

		cleanup_set_id_sesion_map::<T>()
	}
}

fn cleanup_set_id_sesion_map<T: Config>() -> Weight {
	let until_set_id = CurrentSetId::<T>::get().saturating_sub(T::MaxSetIdSessionEntries::get());

	for set_id in 0..=until_set_id {
		SetIdSession::<T>::remove(set_id);
	}

	T::DbWeight::get()
		.reads(1)
		.saturating_add(T::DbWeight::get().writes(until_set_id + 1))
}
