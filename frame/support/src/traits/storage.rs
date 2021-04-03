// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Traits for encoding data related to pallet's storage items.

/// An instance of a pallet in the storage.
///
/// It is required that these instances are unique, to support multiple instances per pallet in the same runtime!
///
/// E.g. for module MyModule default instance will have prefix "MyModule" and other instances
/// "InstanceNMyModule".
pub trait Instance: 'static {
	/// Unique module prefix. E.g. "InstanceNMyModule" or "MyModule"
	const PREFIX: &'static str;
}

/// An instance of a storage in a pallet.
///
/// Define an instance for an individual storage inside a pallet.
/// The pallet prefix is used to isolate the storage between pallets, and the storage prefix is
/// used to isolate storages inside a pallet.
///
/// NOTE: These information can be used to define storages in pallet such as a `StorageMap` which
/// can use keys after `twox_128(pallet_prefix())++twox_128(STORAGE_PREFIX)`
pub trait StorageInstance {
	/// Prefix of a pallet to isolate it from other pallets.
	fn pallet_prefix() -> &'static str;

	/// Prefix given to a storage to isolate from other storages in the pallet.
	const STORAGE_PREFIX: &'static str;
}
