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

#![cfg_attr(not(feature = "std"), no_std)]

//! Substrate genesis config builder
//!
//! This Runtime API allows to construct `GenesisConfig`, in particular:
//! - serialize the runtime default `GenesisConfig` struct into json format,
//! - put the GenesisConfig struct into the storage. Internally this operation calls
//!   `GenesisBuild::build` function for all runtime pallets, which is typically provided by
//!   pallet's author.
//! - deserialize the `GenesisConfig` from given json blob and put `GenesisConfig` into the state
//!   storage. Allows to build customized configuration.
//!
//! Providing externalities with empty storage and putting `GenesisConfig` into storage allows to
//! catch and build the raw storage of `GenesisConfig` which is the foundation for genesis block.

sp_api::decl_runtime_apis! {
	/// API to interact with GenesisConfig for the runtime
	pub trait GenesisBuilder {
		/// Get the default `GenesisConfig` as a JSON blob.
		///
		/// This function instantiates the default `GenesisConfig` struct for the runtime and serializes it into a JSON
		/// blob. It returns a `Vec<u8>` containing the JSON representation of the default `GenesisConfig`.
		fn get_default_as_json() -> sp_std::vec::Vec<u8>;

		/// Patch default `GenesisConfig` using given JSON patch and store it in the storage.
		///
		/// This function generates the `GenesisConfig` for the runtime by applying a provided JSON patch.
		/// The patch modifies the default `GenesisConfig` allowing customization of the specific keys.
		/// The resulting `GenesisConfig` is then deserialized from the patched JSON representation and
		/// stored in the storage.
		///
		/// If the provided JSON patch is incorrect or the deserialization fails, this method will panic.
		/// Any errors encountered during this process should be logged.
		///
		/// The patching process modifies the default `GenesisConfig` according to the following rules:
		/// 1. Existing keys in the default configuration will be overridden by the corresponding values in the patch.
		/// 2. If a key exists in the patch but not in the default configuration, it will be added to the resulting `GenesisConfig`.
		/// 3. Keys in the default configuration that have null values in the patch will be removed from the resulting
		///    `GenesisConfig`. This is helpful for changing enum variant value.
		///
		/// Please note the patch may contain full `GenesisConfig`.
		fn build_config(patch: sp_std::vec::Vec<u8>);
	}
}
