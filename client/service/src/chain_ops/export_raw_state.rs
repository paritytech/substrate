// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::error::Error;
use sc_client_api::{StorageProvider, UsageProvider};
use sp_core::storage::{well_known_keys, ChildInfo, Storage, StorageChild, StorageKey, StorageMap};
use sp_runtime::traits::Block as BlockT;

use std::{
	collections::{BTreeMap, HashMap},
	sync::Arc,
};

/// Export the raw state at the given `block`. If `block` is `None`, the
/// best block will be used.
pub fn export_raw_state<B, BA, C>(client: Arc<C>, hash: B::Hash) -> Result<Storage, Error>
where
	C: UsageProvider<B> + StorageProvider<B, BA>,
	B: BlockT,
	BA: sc_client_api::backend::Backend<B>,
{
	let mut top = BTreeMap::new();
	let mut children_default = HashMap::new();

	for (key, value) in client.storage_pairs(hash, None, None)? {
		// Remove all default child storage roots from the top storage and collect the child storage
		// pairs.
		if key.0.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX) {
			let child_root_key = StorageKey(
				key.0[well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.len()..].to_vec(),
			);
			let child_info = ChildInfo::new_default(&child_root_key.0);
			let mut pairs = StorageMap::new();
			for child_key in client.child_storage_keys(hash, child_info.clone(), None, None)? {
				if let Some(child_value) = client.child_storage(hash, &child_info, &child_key)? {
					pairs.insert(child_key.0, child_value.0);
				}
			}

			children_default.insert(child_root_key.0, StorageChild { child_info, data: pairs });
			continue
		}

		top.insert(key.0, value.0);
	}

	Ok(Storage { top, children_default })
}
