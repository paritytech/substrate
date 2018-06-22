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
use runtime_primitives::MakeStorage;
pub use network::Role;
pub use network::NetworkConfiguration;

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
	/// The name of the chain.
	pub chain_name: String,
	/// Chain configuration.
	pub genesis_storage: MakeStorage,
	/// Telemetry server URL, optional - only `Some` if telemetry reporting is enabled
	pub telemetry: Option<String>,
	/// Node name.
	pub name: String,
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
			chain_name: Default::default(),
			genesis_storage: Box::new(Default::default),
			telemetry: Default::default(),
			name: "Anonymous".into(),
		}
	}
}
