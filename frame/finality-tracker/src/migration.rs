// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// Migration code to update storage.

use super::*;
use frame_support::storage::migration::{put_storage_value, take_storage_value};

pub fn on_runtime_upgrade<T: Trait>() {
	change_name_timestamp_to_finality_tracker::<T>()
}

// Change the storage name used by this pallet from `Timestamp` to `FinalityTracker`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.

fn change_name_timestamp_to_finality_tracker<T:Trait>() {
	sp_runtime::print("Migrating Finality Tracker.");

	if let Some(recent_hints) = take_storage_value::<Vec<T::BlockNumber>>(b"Timestamp", b"RecentHints", &[]) {
		put_storage_value(b"FinalityTracker", b"RecentHints", &[], recent_hints);
	}

	if let Some(ordered_hints) = take_storage_value::<Vec<T::BlockNumber>>(b"Timestamp", b"OrderedHints", &[]) {
		put_storage_value(b"FinalityTracker", b"OrderedHints", &[], ordered_hints);
	}

	if let Some(median) = take_storage_value::<T::BlockNumber>(b"Timestamp", b"Median", &[]) {
		put_storage_value(b"FinalityTracker", b"Median", &[], median);
	}

	if let Some(update) = take_storage_value::<T::BlockNumber>(b"Timestamp", b"Update", &[]) {
		put_storage_value(b"FinalityTracker", b"Update", &[], update);
	}

	if let Some(initialized) = take_storage_value::<bool>(b"Timestamp", b"Initialized", &[]) {
		put_storage_value(b"FinalityTracker", b"Initialized", &[], initialized);
	}
}
