// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! State RPC errors.

use crate::errors;
use jsonrpc_core as rpc;

/// State RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// State RPC future Result type.
pub type FutureResult<T> = jsonrpc_core::BoxFuture<Result<T>>;

/// State RPC errors.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Client error.
	#[display(fmt = "Client error: {}", _0)]
	Client(Box<dyn std::error::Error + Send>),
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
	/// Provided count exceeds maximum value.
	#[display(fmt = "count exceeds maximum value. value: {}, max: {}", value, max)]
	InvalidCount {
		/// Provided value
		value: u32,
		/// Maximum allowed value
		max: u32,
	},
	/// Call to an unsafe RPC was denied.
	UnsafeRpcCalled(crate::policy::UnsafeRpcError),
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(&**err),
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
			Error::InvalidCount { .. } => rpc::Error {
				code: rpc::ErrorCode::ServerError(BASE_ERROR + 2),
				message: format!("{}", e),
				data: None,
			},
			e => errors::internal(e),
		}
	}
}
