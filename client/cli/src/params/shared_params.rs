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
	pub log: Vec<String>,
}

impl SharedParams {
	/// Specify custom base path.
	pub fn base_path(&self) -> Option<PathBuf> {
		self.base_path.clone()
	}

	/// Specify the development chain.
	pub fn is_dev(&self) -> bool {
		self.dev
	}

	/// Get the chain spec for the parameters provided
	pub fn chain_id(&self, is_dev: bool) -> String {
		match self.chain {
			Some(ref chain) => chain.clone(),
			None => {
				if is_dev {
					"dev".into()
				} else {
					"".into()
				}
			}
		}
	}

	/// Get the filters for the logging
	pub fn log_filters(&self) -> &[String] {
		&self.log
	}
}
