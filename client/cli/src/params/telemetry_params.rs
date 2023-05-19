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

use clap::Args;

/// Parameters used to config telemetry.
#[derive(Debug, Clone, Args)]
pub struct TelemetryParams {
	/// Disable connecting to the Substrate telemetry server.
	/// Telemetry is on by default on global chains.
	#[arg(long)]
	pub no_telemetry: bool,

	/// The URL of the telemetry server to connect to.
	/// This flag can be passed multiple times as a means to specify multiple
	/// telemetry endpoints. Verbosity levels range from 0-9, with 0 denoting
	/// the least verbosity.
	/// Expected format is 'URL VERBOSITY', e.g. `--telemetry-url 'wss://foo/bar 0'`.
	#[arg(long = "telemetry-url", value_name = "URL VERBOSITY", value_parser = parse_telemetry_endpoints)]
	pub telemetry_endpoints: Vec<(String, u8)>,
}

#[derive(Debug)]
enum TelemetryParsingError {
	MissingVerbosity,
	VerbosityParsingError(std::num::ParseIntError),
}

impl std::error::Error for TelemetryParsingError {}

impl std::fmt::Display for TelemetryParsingError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			TelemetryParsingError::MissingVerbosity => write!(f, "Verbosity level missing"),
			TelemetryParsingError::VerbosityParsingError(e) => write!(f, "{}", e),
		}
	}
}

fn parse_telemetry_endpoints(s: &str) -> Result<(String, u8), TelemetryParsingError> {
	let pos = s.find(' ');
	match pos {
		None => Err(TelemetryParsingError::MissingVerbosity),
		Some(pos_) => {
			let url = s[..pos_].to_string();
			let verbosity =
				s[pos_ + 1..].parse().map_err(TelemetryParsingError::VerbosityParsingError)?;
			Ok((url, verbosity))
		},
	}
}
