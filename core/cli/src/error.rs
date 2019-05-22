// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Initialization errors.

use client;

/// Initialization result.
pub type Result<T> = std::result::Result<T, Error>;

/// Initialization errors.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// IO error.
	Io(::std::io::Error),
	/// CLI error.
	Cli(::clap::Error),
	/// Service error.
	Service(::service::Error),
	/// Client error.
	Client(client::error::Error),
	/// Input error.
	Input(String),
	/// Invalid listen multiaddress
	#[display(fmt="Invalid listen multiaddress")]
	InvalidListenMultiaddress,
}

impl std::error::Error for Error {}
