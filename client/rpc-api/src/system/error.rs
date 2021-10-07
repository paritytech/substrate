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

//! System RPC module errors.

use crate::system::helpers::Health;
use jsonrpc_core as rpc;

/// System RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// System RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Provided block range couldn't be resolved to a list of blocks.
	#[error("Node is not fully functional: {}", .0)]
	NotHealthy(Health),
	/// Peer argument is malformatted.
	#[error("{0}")]
	MalformattedPeerArg(String),
}

/// Base code for all system errors.
const BASE_ERROR: i64 = 2000;

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error::NotHealthy(ref h) => rpc::Error {
				code: rpc::ErrorCode::ServerError(BASE_ERROR + 1),
				message: format!("{}", e),
				data: serde_json::to_value(h).ok(),
			},
			Error::MalformattedPeerArg(ref e) => rpc::Error {
				code: rpc::ErrorCode::ServerError(BASE_ERROR + 2),
				message: e.clone(),
				data: None,
			},
		}
	}
}
