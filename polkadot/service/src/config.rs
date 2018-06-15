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
#[derive(Clone, Copy, Debug)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The PoC-2 testnet.
	PoC2Testnet,
}

/// Synonym for Option<ChainSpec> because we cannot `impl From<..> for Option<ChainSpec>`
pub struct OptionChainSpec(Option<ChainSpec>);

impl OptionChainSpec {
	/// Return the inner part.
	pub fn inner(self) -> Option<ChainSpec> {
		self.0
	}
}

impl<'a> From<&'a str> for OptionChainSpec {
	fn from(s: &'a str) -> Self {
		OptionChainSpec(Some(match s {
			"dev" => ChainSpec::Development,
			"local" => ChainSpec::LocalTestnet,
			"poc-2" => ChainSpec::PoC2Testnet,
			_ => return OptionChainSpec(None),
		}))
	}
}

impl From<ChainSpec> for &'static str {
	fn from(s: ChainSpec) -> &'static str {
		match s {
			ChainSpec::Development => "dev",
			ChainSpec::LocalTestnet => "local",
			ChainSpec::PoC2Testnet => "poc-2",
		}
	}
}

impl ::std::fmt::Display for ChainSpec {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", match *self {
			ChainSpec::Development => "Development",
			ChainSpec::LocalTestnet => "Local Testnet",
			ChainSpec::PoC2Testnet => "PoC-2 Testnet",
		})
	}
}

/// Service configuration.
#[derive(Clone)]
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
			chain_spec: ChainSpec::Development,
			telemetry: Default::default(),
			name: "Anonymous".into(),
		}
	}
}
