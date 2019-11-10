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

/// Transaction pool result.
pub type Result<T> = std::result::Result<T, Error>;

/// Transaction pool error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Client error.
	Client(client::error::Error),
	/// Pool error.
	Pool(txpool::error::Error),
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(err),
			Error::Pool(ref err) => Some(err),
		}
	}
}

impl txpool::IntoPoolError for Error {
	fn into_pool_error(self) -> std::result::Result<txpool::error::Error, Self> {
		match self {
			Error::Pool(e) => Ok(e),
			e => Err(e),
		}
	}
}
