// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::state::error::FutureResult;
use jsonrpc_derive::rpc;
use sp_core::storage::{PrefixedStorageKey, StorageData, StorageKey};

pub use self::gen_client::Client as ChildStateClient;
use crate::state::ReadProof;

/// Substrate child state API
///
/// Note that all `PrefixedStorageKey` are deserialized
/// from json and not guaranteed valid.
#[rpc]
pub trait ChildStateApi<Hash> {
	/// RPC Metadata
	type Metadata;

	/// DEPRECATED: Please use `childstate_getKeysPaged` with proper paging support.
	/// Returns the keys with prefix from a child storage, leave empty to get all the keys
	#[rpc(name = "childstate_getKeys")]
	fn storage_keys(
		&self,
		child_storage_key: PrefixedStorageKey,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns the keys with prefix from a child storage with pagination support.
	/// Up to `count` keys will be returned.
	/// If `start_key` is passed, return next keys in storage in lexicographic order.
	#[rpc(name = "childstate_getKeysPaged", alias("childstate_getKeysPagedAt"))]
	fn storage_keys_paged(
		&self,
		child_storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		hash: Option<Hash>,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	#[rpc(name = "childstate_getStorage")]
	fn storage(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> FutureResult<Option<StorageData>>;

	/// Returns child storage entries for multiple keys at a specific block's state.
	#[rpc(name = "childstate_getStorageEntries")]
	fn storage_entries(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		hash: Option<Hash>,
	) -> FutureResult<Vec<Option<StorageData>>>;

	/// Returns the hash of a child storage entry at a block's state.
	#[rpc(name = "childstate_getStorageHash")]
	fn storage_hash(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> FutureResult<Option<Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	#[rpc(name = "childstate_getStorageSize")]
	fn storage_size(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> FutureResult<Option<u64>>;

	/// Returns proof of storage for child key entries at a specific block's state.
	#[rpc(name = "state_getChildReadProof")]
	fn read_child_proof(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		hash: Option<Hash>,
	) -> FutureResult<ReadProof<Hash>>;
}
