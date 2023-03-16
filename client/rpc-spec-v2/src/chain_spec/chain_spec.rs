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

//! API implementation for the specification of a chain.

use crate::chain_spec::api::ChainSpecApiServer;
use jsonrpsee::core::RpcResult;
use sc_chain_spec::Properties;

/// An API for chain spec RPC calls.
pub struct ChainSpec {
	/// The name of the chain.
	name: String,
	/// The hexadecimal encoded hash of the genesis block.
	genesis_hash: String,
	/// Chain properties.
	properties: Properties,
}

impl ChainSpec {
	/// Creates a new [`ChainSpec`].
	pub fn new<Hash: AsRef<[u8]>>(
		name: String,
		genesis_hash: Hash,
		properties: Properties,
	) -> Self {
		let genesis_hash = format!("0x{}", hex::encode(genesis_hash));

		Self { name, properties, genesis_hash }
	}
}

impl ChainSpecApiServer for ChainSpec {
	fn chain_spec_unstable_chain_name(&self) -> RpcResult<String> {
		Ok(self.name.clone())
	}

	fn chain_spec_unstable_genesis_hash(&self) -> RpcResult<String> {
		Ok(self.genesis_hash.clone())
	}

	fn chain_spec_unstable_properties(&self) -> RpcResult<Properties> {
		Ok(self.properties.clone())
	}
}
