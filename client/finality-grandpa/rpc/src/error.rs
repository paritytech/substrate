// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::NOT_READY_ERROR_CODE;

#[derive(derive_more::Display, derive_more::From)]
/// Top-level error type for the RPC handler
pub enum Error {
	/// The GRANDPA RPC endpoint is not ready.
	#[display(fmt = "GRANDPA RPC endpoint not ready")]
	EndpointNotReady,
	/// GRANDPA reports the authority set id to be larger than 32-bits.
	#[display(fmt = "GRANDPA reports authority set id unreasonably large")]
	AuthoritySetIdReportedAsUnreasonablyLarge,
	/// GRANDPA reports voter state with round id or weights larger than 32-bits.
	#[display(fmt = "GRANDPA reports voter state as unreasonably large")]
	VoterStateReportsUnreasonablyLargeNumbers,
}

impl From<Error> for jsonrpc_core::Error {
	fn from(error: Error) -> Self {
		jsonrpc_core::Error {
			message: format!("{}", error).into(),
			code: jsonrpc_core::ErrorCode::ServerError(NOT_READY_ERROR_CODE),
			data: None,
		}
	}
}

impl From<std::num::TryFromIntError> for Error {
	fn from(_error: std::num::TryFromIntError) -> Self {
		Error::VoterStateReportsUnreasonablyLargeNumbers
	}
}
