// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Offchain RPC errors.

use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};

/// Offchain RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Offchain RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Unavailable storage kind error.
	#[error("This storage kind is not available yet.")]
	UnavailableStorageKind,
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base error code for all offchain errors.
const BASE_ERROR: i32 = 5000;

impl From<Error> for JsonRpseeError {
	fn from(e: Error) -> Self {
		match e {
			Error::UnavailableStorageKind => CallError::Custom(ErrorObject::owned(
				BASE_ERROR + 1,
				"This storage kind is not available yet",
				None::<()>,
			))
			.into(),
			Error::UnsafeRpcCalled(e) => e.into(),
		}
	}
}
