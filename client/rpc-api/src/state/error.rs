// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};
/// State RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// State RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Client error.
	#[error("Client error: {}", .0)]
	Client(#[from] Box<dyn std::error::Error + Send + Sync>),
	/// Provided block range couldn't be resolved to a list of blocks.
	#[error("Cannot resolve a block range ['{:?}' ... '{:?}]. {}", .from, .to, .details)]
	InvalidBlockRange {
		/// Beginning of the block range.
		from: String,
		/// End of the block range.
		to: String,
		/// Details of the error message.
		details: String,
	},
	/// Provided count exceeds maximum value.
	#[error("count exceeds maximum value. value: {}, max: {}", .value, .max)]
	InvalidCount {
		/// Provided value
		value: u32,
		/// Maximum allowed value
		max: u32,
	},
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base code for all state errors.
const BASE_ERROR: i32 = 4000;

impl From<Error> for JsonRpseeError {
	fn from(e: Error) -> Self {
		match e {
			Error::InvalidBlockRange { .. } =>
				CallError::Custom(ErrorObject::owned(BASE_ERROR + 1, e.to_string(), None::<()>))
					.into(),
			Error::InvalidCount { .. } =>
				CallError::Custom(ErrorObject::owned(BASE_ERROR + 2, e.to_string(), None::<()>))
					.into(),
			e => Self::to_call_error(e),
		}
	}
}
