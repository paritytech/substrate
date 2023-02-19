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

//! Error helpers for Chain RPC module.

use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};
/// Chain RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Chain RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Client error.
	#[error("Client error: {}", .0)]
	Client(#[from] Box<dyn std::error::Error + Send + Sync>),
	/// Other error type.
	#[error("{0}")]
	Other(String),
}

/// Base error code for all chain errors.
const BASE_ERROR: i32 = 3000;

impl From<Error> for JsonRpseeError {
	fn from(e: Error) -> Self {
		match e {
			Error::Other(message) =>
				CallError::Custom(ErrorObject::owned(BASE_ERROR + 1, message, None::<()>)).into(),
			e => e.into(),
		}
	}
}
