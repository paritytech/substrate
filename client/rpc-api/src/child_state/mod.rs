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

use crate::state::ReadProof;
use jsonrpsee::{proc_macros::rpc, types::RpcResult};
use sp_core::storage::{PrefixedStorageKey, StorageData, StorageKey};

/// Substrate child state API
///
/// Note that all `PrefixedStorageKey` are deserialized
/// from json and not guaranteed valid.
#[rpc(client, server, namespace = "childstate")]
pub trait ChildStateApi<Hash> {
	/// DEPRECATED: Please use `getKeysPaged` with proper paging support.
	/// Returns the keys with prefix from a child storage, leave empty to get all the keys
	#[method(name = "getKeys")]
	async fn storage_keys(
		&self,
		child_storage_key: PrefixedStorageKey,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> RpcResult<Vec<StorageKey>>;

	/// Returns the keys with prefix from a child storage with pagination support.
	/// Up to `count` keys will be returned.
	/// If `start_key` is passed, return next keys in storage in lexicographic order.
	#[method(name = "getKeysPaged", aliases = ["getKeysPagedAt"])]
	async fn storage_keys_paged(
		&self,
		child_storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		hash: Option<Hash>,
	) -> RpcResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	#[method(name = "getStorage")]
	async fn storage(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> RpcResult<Option<StorageData>>;

	/// Returns child storage entries for multiple keys at a specific block's state.
	#[method(name = "getStorageEntries")]
	async fn storage_entries(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		hash: Option<Hash>,
	) -> RpcResult<Vec<Option<StorageData>>>;

	/// Returns the hash of a child storage entry at a block's state.
	#[method(name = "getStorageHash")]
	async fn storage_hash(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> RpcResult<Option<Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	#[method(name = "getStorageSize")]
	async fn storage_size(
		&self,
		child_storage_key: PrefixedStorageKey,
		key: StorageKey,
		hash: Option<Hash>,
	) -> RpcResult<Option<u64>>;

	/// Returns proof of storage for child key entries at a specific block's state.
	#[method(name = "getChildReadProof", aliases = ["state_getChildReadProof"])]
	async fn read_child_proof(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		hash: Option<Hash>,
	) -> RpcResult<ReadProof<Hash>>;
}
