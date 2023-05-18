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

//! Substrate genesis config builder
//!
//! This Runtime API allows to construct `GenesisConfig`, in particular:
//! - serialize the runtime default `GenesisConfig` struct into json format,
//! - put the GenesisConfig struct into the storage. Internally this operation calls
//!   `GenesisBuild::build` function
//! for all runtime pallets, which is typically provided by pallet's author.
//! - deserialize the GenesisConfig from given json blob and put GenesisConfig into the state
//!   storage. Allows to build
//! customized configuration.
//!
//! Providing externalities with empty storage and putting GenesisConfig into storage allows to
//! catch and build the raw storage of `GenesisConfig` which is the foundation for genesis block.

sp_api::decl_runtime_apis! {
	/// API to interact with GenesisConfig for the runtime
	pub trait GenesisBuilder {
		/// Instantiate default `GenesisConfig` and serializes it to json blob.
		fn default_genesis_config_as_json() -> sp_std::vec::Vec<u8>;

		/// Deserialize the `GenesisConfig` from given json blob and put it into the storage.
		fn build_genesis_config_from_json(json: sp_std::vec::Vec<u8>);
	}
}
