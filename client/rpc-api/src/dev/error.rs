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

//! Error helpers for Dev RPC module.

use jsonrpsee::types::error::{ErrorObject, ErrorObjectOwned};

/// Dev RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Dev RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Failed to query specified block or its parent: Probably an invalid hash.
	#[error("Error while querying block: {0}")]
	BlockQueryError(Box<dyn std::error::Error + Send>),
	/// The re-execution of the specified block failed.
	#[error("Failed to re-execute the specified block")]
	BlockExecutionFailed,
	/// Failed to extract the proof.
	#[error("Failed to extract the proof")]
	ProofExtractionFailed,
	/// The witness compaction failed.
	#[error("Failed to create to compact the witness")]
	WitnessCompactionFailed,
	/// The method is marked as unsafe but unsafe flag wasn't supplied on the CLI.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base error code for all dev errors.
const BASE_ERROR: i32 = crate::error::base::DEV;

impl From<Error> for ErrorObjectOwned {
	fn from(e: Error) -> Self {
		let msg = e.to_string();

		match e {
			Error::BlockQueryError(_) => ErrorObject::owned(BASE_ERROR + 1, msg, None::<()>),
			Error::BlockExecutionFailed => ErrorObject::owned(BASE_ERROR + 3, msg, None::<()>),
			Error::WitnessCompactionFailed => ErrorObject::owned(BASE_ERROR + 4, msg, None::<()>),
			Error::ProofExtractionFailed => ErrorObject::owned(BASE_ERROR + 5, msg, None::<()>),
			Error::UnsafeRpcCalled(e) => e.into(),
		}
	}
}
