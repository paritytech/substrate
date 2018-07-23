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

//! Predefined chains.

use service;
use std::path::PathBuf;

/// The chain specification (this should eventually be replaced by a more general JSON-based chain
/// specification).
#[derive(Clone, Debug)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The PoC-1 & PoC-2 era testnet.
	KrummeLanke,
	/// Whatever the current runtime is with the "global testnet" defaults.
	StagingTestnet,
	/// Custom Genesis file.
	Custom(String),
}

/// Get a chain config from a spec setting.
impl ChainSpec {
	pub(crate) fn load(self) -> Result<service::ChainSpec, String> {
		Ok(match self {
			ChainSpec::KrummeLanke => service::chain_spec::poc_1_testnet_config()?,
			ChainSpec::Development => service::chain_spec::development_config(),
			ChainSpec::LocalTestnet => service::chain_spec::local_testnet_config(),
			ChainSpec::StagingTestnet => service::chain_spec::staging_testnet_config(),
			ChainSpec::Custom(f) => service::ChainSpec::from_json_file(PathBuf::from(f))?,
		})
	}
}

impl<'a> From<&'a str> for ChainSpec {
	fn from(s: &'a str) -> Self {
		match s {
			"dev" => ChainSpec::Development,
			"local" => ChainSpec::LocalTestnet,
			"poc-1" => ChainSpec::KrummeLanke,
			"krummelanke" => ChainSpec::KrummeLanke,
			"staging" => ChainSpec::StagingTestnet,
			s => ChainSpec::Custom(s.into()),
		}
	}
}

impl From<ChainSpec> for String {
	fn from(s: ChainSpec) -> String {
		match s {
			ChainSpec::Development => "dev".into(),
			ChainSpec::LocalTestnet => "local".into(),
			ChainSpec::KrummeLanke => "krummelanke".into(),
			ChainSpec::StagingTestnet => "staging".into(),
			ChainSpec::Custom(f) => format!("custom ({})", f),
		}
	}
}
