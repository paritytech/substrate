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
use std::{error, fmt};

/// Result type alias for the CLI.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the CLI.
pub enum Error {
	/// Io error
	Io(::std::io::Error),
	/// Cli error
	Cli(::clap::Error),
	/// Service error
	Service(::service::Error),
	/// Client error
	Client(client::error::Error),
	/// Input error
	Input(String),
}

impl From<::std::io::Error> for Error {
	fn from(err: ::std::io::Error) -> Self {
		Error::Io(err)
	}
}

impl From<::clap::Error> for Error {
	fn from(err: ::clap::Error) -> Self {
		Error::Cli(err)
	}
}

impl From<::service::Error> for Error {
	fn from(err: ::service::Error) -> Self {
		Error::Service(err)
	}
}

impl From<client::error::Error> for Error {
	fn from(err: client::error::Error) -> Self {
		Error::Client(err)
	}
}

impl From<String> for Error {
	fn from(err: String) -> Self {
		Error::Input(err)
	}
}

impl<'a> From<&'a str> for Error {
	fn from(err: &'a str) -> Self {
		Error::Input(err.to_string())
	}
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::Io(ref err) => Some(err),
			Error::Cli(ref err) => Some(err),
			Error::Service(ref err) => Some(err),
			Error::Client(ref err) => Some(err),
			Error::Input(_) => None,
		}
	}
}

impl fmt::Debug for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Error::Io(t) => write!(f, "{}", t),
			Error::Cli(t) => write!(f, "{}", t),
			Error::Service(t) => write!(f, "{}", t),
			Error::Client(t) => write!(f, "{}", t),
			Error::Input(t) => write!(f, "{}", t),
		}
	}
}
