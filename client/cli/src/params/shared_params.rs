// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::path::PathBuf;
use structopt::StructOpt;
use app_dirs::{AppInfo, AppDataType};
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis,
	config::DatabaseConfig, ChainSpec,
};

use crate::VersionInfo;
use crate::error;

/// default sub directory to store database
const DEFAULT_DB_CONFIG_PATH : &'static str = "db";

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, StructOpt, Clone)]
pub struct SharedParams {
	/// Specify the chain specification (one of dev, local or staging).
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain.
	#[structopt(long = "dev")]
	pub dev: bool,

	/// Specify custom base path.
	#[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
	pub base_path: Option<PathBuf>,

	/// Sets a custom logging filter.
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	pub log: Option<String>,
}

impl SharedParams {
	/// Load spec to `Configuration` from `SharedParams` and spec factory.
	pub fn update_config<'a, G, E, F>(
		&self,
		mut config: &'a mut Configuration<G, E>,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<&'a ChainSpec<G, E>> where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	{
		let chain_key = match self.chain {
			Some(ref chain) => chain.clone(),
			None => if self.dev { "dev".into() } else { "".into() }
		};
		let spec = match spec_factory(&chain_key)? {
			Some(spec) => spec,
			None => ChainSpec::from_json_file(PathBuf::from(chain_key))?
		};

		config.network.boot_nodes = spec.boot_nodes().to_vec();
		config.telemetry_endpoints = spec.telemetry_endpoints().clone();

		config.chain_spec = Some(spec);

		if config.config_dir.is_none() {
			config.config_dir = Some(base_path(self, version));
		}

		if config.database.is_none() {
			config.database = Some(DatabaseConfig::Path {
				path: config
					.in_chain_config_dir(DEFAULT_DB_CONFIG_PATH)
					.expect("We provided a base_path/config_dir."),
				cache_size: None,
			});
		}

		Ok(config.chain_spec.as_ref().unwrap())
	}

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	pub fn init(&self, version: &VersionInfo) -> error::Result<()> {
		crate::init(self.log.as_ref().map(|v| v.as_ref()).unwrap_or(""), version)
	}
}

fn base_path(cli: &SharedParams, version: &VersionInfo) -> PathBuf {
	cli.base_path.clone()
		.unwrap_or_else(||
			app_dirs::get_app_root(
				AppDataType::UserData,
				&AppInfo {
					name: version.executable_name,
					author: version.author
				}
			).expect("app directories exist on all supported platforms; qed")
		)
}
