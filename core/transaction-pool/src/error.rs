// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Transaction pool error.

use client;
use txpool;
use std::{error, fmt};

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
pub enum Error {
	/// Client error
	Client(client::error::Error),
	/// Pool error
	Pool(txpool::error::Error),
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(err),
			Error::Pool(ref err) => Some(err),
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
			Error::Client(ref err) => write!(f, "{}", err),
			Error::Pool(ref err) => write!(f, "{}", err),
		}
	}
}

impl From<client::error::Error> for Error {
	fn from(err: client::error::Error) -> Error {
		Error::Client(err)
	}
}

impl From<txpool::error::Error> for Error {
	fn from(err: txpool::error::Error) -> Error {
		Error::Pool(err)
	}
}

impl txpool::IntoPoolError for Error {
	fn into_pool_error(self) -> ::std::result::Result<txpool::error::Error, Self> {
		match self {
			Error::Pool(e) => Ok(txpool::error::Error(e, c)),
			e => Err(e),
		}
	}
}
