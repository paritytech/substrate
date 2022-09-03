// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use crate::arg_enums::TracingReceiver;
use clap::Args;
use sc_service::config::BasePath;
use std::path::PathBuf;

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, Clone, PartialEq, Args)]
pub struct SharedParams {
	/// Specify the chain specification.
	///
	/// It can be one of the predefined ones (dev, local, or staging) or it can be a path to a file
	/// with the chainspec (such as one exported by the `build-spec` subcommand).
	#[clap(long, value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain.
	///
	/// This flag sets `--chain=dev`, `--force-authoring`, `--rpc-cors=all`,
	/// `--alice`, and `--tmp` flags, unless explicitly overridden.
	#[clap(long, conflicts_with_all = &["chain"])]
	pub dev: bool,

	/// Specify custom base path.
	#[clap(long, short = 'd', value_name = "PATH", parse(from_os_str))]
	pub base_path: Option<PathBuf>,

	/// Sets a custom logging filter. Syntax is <target>=<level>, e.g. -lsync=debug.
	///
	/// Log levels (least to most verbose) are error, warn, info, debug, and trace.
	/// By default, all targets log `info`. The global log level can be set with -l<level>.
	#[clap(short = 'l', long, value_name = "LOG_PATTERN", multiple_values(true))]
	pub log: Vec<String>,

	/// Enable detailed log output.
	///
	/// This includes displaying the log target, log level and thread name.
	///
	/// This is automatically enabled when something is logged with any higher level than `info`.
	#[clap(long)]
	pub detailed_log_output: bool,

	/// Disable log color output.
	#[clap(long)]
	pub disable_log_color: bool,

	/// Enable feature to dynamically update and reload the log filter.
	///
	/// Be aware that enabling this feature can lead to a performance decrease up to factor six or
	/// more. Depending on the global logging level the performance decrease changes.
	///
	/// The `system_addLogFilter` and `system_resetLogFilter` RPCs will have no effect with this
	/// option not being set.
	#[clap(long)]
	pub enable_log_reloading: bool,

	/// Sets a custom profiling filter. Syntax is the same as for logging: <target>=<level>
	#[clap(long, value_name = "TARGETS")]
	pub tracing_targets: Option<String>,

	/// Receiver to process tracing messages.
	#[clap(long, value_name = "RECEIVER", arg_enum, ignore_case = true, default_value = "log")]
	pub tracing_receiver: TracingReceiver,
}

impl SharedParams {
	/// Specify custom base path.
	pub fn base_path(&self) -> Result<Option<BasePath>, crate::Error> {
		match &self.base_path {
			Some(r) => Ok(Some(r.clone().into())),
			// If `dev` is enabled, we use the temp base path.
			None if self.is_dev() => Ok(Some(BasePath::new_temp_dir()?)),
			None => Ok(None),
		}
	}

	/// Specify the development chain.
	pub fn is_dev(&self) -> bool {
		self.dev
	}

	/// Get the chain spec for the parameters provided
	pub fn chain_id(&self, is_dev: bool) -> String {
		match self.chain {
			Some(ref chain) => chain.clone(),
			None =>
				if is_dev {
					"dev".into()
				} else {
					"".into()
				},
		}
	}

	/// Get the filters for the logging
	pub fn log_filters(&self) -> &[String] {
		&self.log
	}

	/// Should the detailed log output be enabled.
	pub fn detailed_log_output(&self) -> bool {
		self.detailed_log_output
	}

	/// Should the log color output be disabled?
	pub fn disable_log_color(&self) -> bool {
		self.disable_log_color
	}

	/// Is log reloading enabled
	pub fn enable_log_reloading(&self) -> bool {
		self.enable_log_reloading
	}

	/// Receiver to process tracing messages.
	pub fn tracing_receiver(&self) -> sc_service::TracingReceiver {
		self.tracing_receiver.into()
	}

	/// Comma separated list of targets for tracing.
	pub fn tracing_targets(&self) -> Option<String> {
		self.tracing_targets.clone()
	}
}
