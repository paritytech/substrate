// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate state API.

use jsonrpc_derive::rpc;
use sp_core::storage::{StorageKey, PrefixedStorageKey, StorageData};
use crate::state::error::FutureResult;

pub use self::gen_client::Client as ChildStateClient;

/// Substrate child state API
///
/// Note that all `PrefixedStorageKey` are desierialized
/// from json and not guaranted valid.
#[rpc]
pub trait ChildStateApi<Hash> {
	/// RPC Metadata
	type Metadata;

	/// Returns the keys with prefix from a child storage, leave empty to get all the keys
	#[rpc(name = "childstate_getKeys")]
	fn storage_keys(
		&self,
		child_storage_key: PrefixedStorageKey,
		prefix: StorageKey,
		hash: Option<Hash>
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	#[rpc(name = "childstate_getStorage")]
	fn storage(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> FutureResult<Option<StorageData>>;

	/// Returns the hash of a child storage entry at a block's state.
	#[rpc(name = "childstate_getStorageHash")]
	fn storage_hash(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> FutureResult<Option<Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	#[rpc(name = "childstate_getStorageSize")]
	fn storage_size(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> FutureResult<Option<u64>>;
}
