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

//! State RPC errors.

use client;
use crate::rpc;
use crate::errors;

/// State RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// State RPC errors.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Client error.
	Client(client::error::Error),
	/// Provided block range couldn't be resolved to a list of blocks.
	#[display(fmt = "Cannot resolve a block range ['{:?}' ... '{:?}]. {}", from, to, details)]
	InvalidBlockRange {
		/// Beginning of the block range.
		from: String,
		/// End of the block range.
		to: String,
		/// Details of the error message.
		details: String,
	},
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(err),
			_ => None,
		}
	}
}

/// Base code for all state errors.
const BASE_ERROR: i64 = 4000;

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error::InvalidBlockRange { .. } => rpc::Error {
				code: rpc::ErrorCode::ServerError(BASE_ERROR + 1),
				message: format!("{}", e),
				data: None,
			},
			e => errors::internal(e),
		}
	}
}
