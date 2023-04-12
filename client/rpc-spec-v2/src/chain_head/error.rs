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

//! Error helpers for `chainHead` RPC module.

use jsonrpsee::{
	core::Error as RpcError,
	types::error::{CallError, ErrorObject},
};
use sp_blockchain::Error as BlockchainError;

/// ChainHead RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// The provided block hash is invalid.
	#[error("Invalid block hash")]
	InvalidBlock,
	/// Fetch block header error.
	#[error("Could not fetch block header: {0}")]
	FetchBlockHeader(BlockchainError),
	/// Invalid parameter provided to the RPC method.
	#[error("Invalid parameter: {0}")]
	InvalidParam(String),
	/// Invalid subscription ID provided by the RPC server.
	#[error("Invalid subscription ID")]
	InvalidSubscriptionID,
}

// Base code for all `chainHead` errors.
const BASE_ERROR: i32 = 2000;
/// The provided block hash is invalid.
const INVALID_BLOCK_ERROR: i32 = BASE_ERROR + 1;
/// Fetch block header error.
const FETCH_BLOCK_HEADER_ERROR: i32 = BASE_ERROR + 2;
/// Invalid parameter error.
const INVALID_PARAM_ERROR: i32 = BASE_ERROR + 3;
/// Invalid subscription ID.
const INVALID_SUB_ID: i32 = BASE_ERROR + 4;

impl From<Error> for ErrorObject<'static> {
	fn from(e: Error) -> Self {
		let msg = e.to_string();

		match e {
			Error::InvalidBlock => ErrorObject::owned(INVALID_BLOCK_ERROR, msg, None::<()>),
			Error::FetchBlockHeader(_) =>
				ErrorObject::owned(FETCH_BLOCK_HEADER_ERROR, msg, None::<()>),
			Error::InvalidParam(_) => ErrorObject::owned(INVALID_PARAM_ERROR, msg, None::<()>),
			Error::InvalidSubscriptionID => ErrorObject::owned(INVALID_SUB_ID, msg, None::<()>),
		}
		.into()
	}
}

impl From<Error> for RpcError {
	fn from(e: Error) -> Self {
		CallError::Custom(e.into()).into()
	}
}
