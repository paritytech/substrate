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

use client;
use crate::rpc;
use crate::errors;
use std::{error, fmt};

/// Result type alias for the RPC.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the RPC.
pub enum Error {
	/// Client error
	Client(client::error::Error),
	/// Not implemented yet
	Unimplemented,
}

impl From<client::error::Error> for Error {
	fn from(err: client::error::Error) -> Self {
		Error::Client(err)
	}
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(err),
			Error::Unimplemented => None,
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
			Error::Client(t) => write!(f, "{}", t),
			Error::Unimplemented => write!(f, "Not implemented yet"),
		}
	}
}

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error::Unimplemented => errors::unimplemented(),
			e => errors::internal(e),
		}
	}
}
