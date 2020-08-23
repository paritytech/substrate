// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Substrate offchain API.

pub mod error;

use jsonrpc_derive::rpc;
use self::error::Result;
use sp_core::{Bytes, offchain::StorageKind};

pub use self::gen_client::Client as OffchainClient;

/// Substrate offchain RPC API
#[rpc]
pub trait OffchainApi {
	/// Set offchain local storage under given key and prefix.
	#[rpc(name = "offchain_localStorageSet")]
	fn set_local_storage(&self, kind: StorageKind, key: Bytes, value: Bytes) -> Result<()>;

	/// Get offchain local storage under given key and prefix.
	#[rpc(name = "offchain_localStorageGet")]
	fn get_local_storage(&self, kind: StorageKind, key: Bytes) -> Result<Option<Bytes>>;
}
