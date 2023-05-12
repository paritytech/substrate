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

//! Substrate genesis config builder
//!
//! This Runtime API allows to construct `GenesisConfig`, in particular:
//! - serialize the runtime default `GenesisConfig` struct into json format,
//! - put the GenesisConfig struct into the storage. Internally this operation calls `GenesisBuild::build` function
//! for all runtime pallets, which is typically by pallet's author.
//! - deserialize the GenesisConfig from given json blob and put GenesisConfig into the state storage. Allows to build
//! customized configuration.
//!
//! Providing externalities with empty storage and putting GenesisConfig into storage allows to catch and build the raw
//! storage of `GenesisConfig` which is the foundation for genesis block. 

#![cfg_attr(not(feature = "std"), no_std)]

sp_api::decl_runtime_apis! {
	/// API to interact with GenesisConfig for the runtime
	pub trait GenesisBuilder {
		/// Instantiate default `GenesisConfig` and put it to storage. Typically this will be done by means of `GenesisBuild::build` function.
		fn build_default_config();

		// fn default_config_as_json() -> serde_json::Result<Vec<u8>>;
		/// Instantiate default `GenesisConfig` and serializes it to json blob.
		fn default_config_as_json() -> sp_std::vec::Vec<u8>;

		/// Deserialize the `GenesisConfig` from given json blob and put it into the storage.
		fn build_genesis_config_from_json(json: sp_std::vec::Vec<u8>);
	}
}
