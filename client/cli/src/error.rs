// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Initialization errors.

/// Result type alias for the CLI.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the CLI.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Io error
	Io(std::io::Error),
	/// Cli error
	Cli(structopt::clap::Error),
	/// Service error
	Service(sc_service::Error),
	/// Client error
	Client(sp_blockchain::Error),
	/// Input error
	#[from(ignore)]
	Input(String),
	/// Invalid listen multiaddress
	#[display(fmt="Invalid listen multiaddress")]
	#[from(ignore)]
	InvalidListenMultiaddress,
	/// Other uncategorized error.
	#[from(ignore)]
	Other(String),
}

/// Must be implemented explicitly because `derive_more` won't generate this
/// case due to conflicting derive for `Other(String)`.
impl std::convert::From<String> for Error {
	fn from(s: String) -> Error {
		Error::Input(s)
	}
}

impl std::convert::From<&str> for Error {
	fn from(s: &str) -> Error {
		Error::Input(s.to_string())
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Io(ref err) => Some(err),
			Error::Cli(ref err) => Some(err),
			Error::Service(ref err) => Some(err),
			Error::Client(ref err) => Some(err),
			Error::Input(_) => None,
			Error::InvalidListenMultiaddress => None,
			Error::Other(_) => None,
		}
	}
}
