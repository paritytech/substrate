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

use sc_service::{config::DatabaseConfig, ChainSpec};
use std::path::PathBuf;
use structopt::StructOpt;

use crate::error::Result;
use crate::init_logger;
use crate::SubstrateCLI;

/// default sub directory to store database
const DEFAULT_DB_CONFIG_PATH: &'static str = "db";

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, StructOpt, Clone)]
pub struct SharedParams {
	/// Specify the chain specification (one of dev, local, or staging).
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain.
	#[structopt(long = "dev")]
	pub dev: bool,

	/// Specify custom base path.
	#[structopt(
		long = "base-path",
		short = "d",
		value_name = "PATH",
		parse(from_os_str)
	)]
	pub base_path: Option<PathBuf>,

	/// Sets a custom logging filter. Syntax is <target>=<level>, e.g. -lsync=debug.
	///
	/// Log levels (least to most verbose) are error, warn, info, debug, and trace.
	/// By default, all targets log `info`. The global log level can be set with -l<level>.
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	pub log: Option<String>,
}

impl SharedParams {
	/// Get the chain spec for the parameters provided
	pub fn get_chain_spec<C: SubstrateCLI>(&self) -> Result<Box<dyn ChainSpec>> {
		let chain_key = match self.chain {
			Some(ref chain) => chain.clone(),
			None => {
				if self.dev {
					"dev".into()
				} else {
					"".into()
				}
			}
		};

		Ok(C::spec_factory(&chain_key)?)
	}

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	pub fn init<C: SubstrateCLI>(&self) -> Result<()> {
		let logger_pattern = self.log.as_ref().map(|v| v.as_ref()).unwrap_or("");

		sp_panic_handler::set(C::get_support_url(), C::get_impl_version());

		fdlimit::raise_fd_limit();
		init_logger(logger_pattern);

		Ok(())
	}

	/// Get the database configuration object for the parameters provided
	pub fn get_database_config(
		&self,
		base_path: &PathBuf,
		cache_size: Option<usize>,
	) -> DatabaseConfig {
		DatabaseConfig::Path {
			path: base_path.join(DEFAULT_DB_CONFIG_PATH),
			cache_size,
		}
	}
}
