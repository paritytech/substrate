// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Keystore (and session key management) for ed25519 based chains like Polkadot.

#![warn(missing_docs)]
use sp_core::crypto::KeyTypeId;
use sp_keystore::Error as TraitError;
use std::io;

/// Local keystore implementation
mod local;
pub use local::LocalKeystore;

/// Keystore error.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// IO error.
	Io(io::Error),
	/// JSON error.
	Json(serde_json::Error),
	/// Invalid password.
	#[display(fmt = "Invalid password")]
	InvalidPassword,
	/// Invalid BIP39 phrase
	#[display(fmt = "Invalid recovery phrase (BIP39) data")]
	InvalidPhrase,
	/// Invalid seed
	#[display(fmt = "Invalid seed")]
	InvalidSeed,
	/// Public key type is not supported
	#[display(fmt = "Key crypto type is not supported")]
	KeyNotSupported(KeyTypeId),
	/// Keystore unavailable
	#[display(fmt = "Keystore unavailable")]
	Unavailable,
}

/// Keystore Result
pub type Result<T> = std::result::Result<T, Error>;

impl From<Error> for TraitError {
	fn from(error: Error) -> Self {
		match error {
			Error::KeyNotSupported(id) => TraitError::KeyNotSupported(id),
			Error::InvalidSeed | Error::InvalidPhrase | Error::InvalidPassword =>
				TraitError::ValidationError(error.to_string()),
			Error::Unavailable => TraitError::Unavailable,
			Error::Io(e) => TraitError::Other(e.to_string()),
			Error::Json(e) => TraitError::Other(e.to_string()),
		}
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Io(ref err) => Some(err),
			Error::Json(ref err) => Some(err),
			_ => None,
		}
	}
}
