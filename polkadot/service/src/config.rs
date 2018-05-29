// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Service configuration.

use transaction_pool;
pub use network::Role;
pub use network::NetworkConfiguration;

/// The chain specification (this should eventually be replaced by a more general JSON-based chain
/// specification).
#[derive(Clone)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The PoC-1 testnet.
	PoC1Testnet,
}

/// Service configuration.
pub struct Configuration {
	/// Node roles.
	pub roles: Role,
	/// Transaction pool configuration.
	pub transaction_pool: transaction_pool::Options,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Path to key files.
	pub keystore_path: String,
	/// Path to the database.
	pub database_path: String,
	/// Additional key seeds.
	pub keys: Vec<String>,
	/// Chain specification.
	pub chain_spec: ChainSpec,
}

impl Default for Configuration {
	fn default() -> Configuration {
		Configuration {
			roles: Role::FULL,
			transaction_pool: Default::default(),
			network: Default::default(),
			keystore_path: Default::default(),
			database_path: Default::default(),
			keys: Default::default(),
			chain_spec: ChainSpec::Development,
		}
	}
}

impl Clone for Configuration {
	fn clone(&self) -> Configuration {
		Configuration {
			roles: self.roles.clone(),
			transaction_pool: transaction_pool::Options {
				max_count: self.transaction_pool.max_count.clone(),
				max_mem_usage: self.transaction_pool.max_mem_usage.clone(),
				max_per_sender: self.transaction_pool.max_per_sender.clone(),
			},
			network: self.network.clone(),
			keystore_path: self.keystore_path.clone(),
			database_path: self.database_path.clone(),
			keys: self.keys.clone(),
			chain_spec: self.chain_spec.clone(),
		}
	}
}
