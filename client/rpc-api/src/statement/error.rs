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

//! Statement RPC errors.

use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};

/// Statement RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Statement RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Statement store internal error.
	#[error("Statement store error")]
	StatementStore(String),
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base error code for all statement errors.
const BASE_ERROR: i32 = crate::error::base::STATEMENT;

impl From<Error> for JsonRpseeError {
	fn from(e: Error) -> Self {
		match e {
			Error::StatementStore(message) => CallError::Custom(ErrorObject::owned(
				BASE_ERROR + 1,
				format!("Statement store error: {message}"),
				None::<()>,
			))
			.into(),
			Error::UnsafeRpcCalled(e) => e.into(),
		}
	}
}
