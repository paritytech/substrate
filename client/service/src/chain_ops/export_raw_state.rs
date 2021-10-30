// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

use std::{collections::HashMap, sync::Arc};

/// Export the raw state at the given `block`. If `block` is `None`, the
/// best block will be used.
pub fn export_raw_state<B, BA, C>(
	client: Arc<C>,
	block: Option<BlockId<B>>,
) -> Result<Storage, Error>
where
	C: UsageProvider<B> + StorageProvider<B, BA>,
	B: BlockT,
	BA: sc_client_api::backend::Backend<B>,
{
	let block = block.unwrap_or_else(|| BlockId::Hash(client.usage_info().chain.best_hash));

	let empty_key = StorageKey(Vec::new());
	let mut top_storage = client.storage_pairs(&block, &empty_key)?;
	let mut children_default = HashMap::new();

	// Remove all default child storage roots from the top storage and collect the child storage
	// pairs.
	while let Some(pos) = top_storage
		.iter()
		.position(|(k, _)| k.0.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX))
	{
		let (key, _) = top_storage.swap_remove(pos);

		let key =
			StorageKey(key.0[well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.len()..].to_vec());
		let child_info = ChildInfo::new_default(&key.0);

		let keys = client.child_storage_keys(&block, &child_info, &empty_key)?;
		let mut pairs = StorageMap::new();
		keys.into_iter().try_for_each(|k| {
			if let Some(value) = client.child_storage(&block, &child_info, &k)? {
				pairs.insert(k.0, value.0);
			}

			Ok::<_, Error>(())
		})?;

		children_default.insert(key.0, StorageChild { child_info, data: pairs });
	}

	let top = top_storage.into_iter().map(|(k, v)| (k.0, v.0)).collect();
	Ok(Storage { top, children_default })
}
