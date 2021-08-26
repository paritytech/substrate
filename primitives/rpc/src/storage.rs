// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Types for working with block storage change data

use serde::{Deserialize, Serialize};
use rustc_hash::FxHashMap;

use sp_core::storage::{StorageData, StorageKey};

/// Container for all related storage changes for the block being re-executed.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct BlockStorageChanges<Hash> {
	/// Hash of the block being re-executed
	pub block_hash: Hash,
	/// Parent hash
	pub parent_hash: Hash,
	/// Storage prefixes targets used to filter out changes that do not have one of the storage
	/// prefixes. Empty vector means do not filter out any storage prefixes.
	pub storage_prefixes: Vec<String>,
	/// Vec of storage key-value pair.
	pub storage_changes: FxHashMap<StorageKey, Option<StorageData>>,
}

/// Error response for the `state_traceBlockStorageAt` RPC.
#[derive(Serialize, Deserialize, Default, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct StorageChangesError {
	/// Error message
	pub error: String,
}

/// Response for the `state_traceBlockStorageAt` RPC.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub enum BlockStorageChangesResponse<Hash> {
	/// Error block tracing response
	StorageChangesError(StorageChangesError),
	/// Successful block storage tracing response
	BlockStorageChanges(BlockStorageChanges<Hash>),
}
