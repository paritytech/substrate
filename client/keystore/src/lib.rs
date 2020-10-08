// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Keystore (and session key management) for ed25519 based chains like Polkadot.

#![warn(missing_docs)]
use std::io;
use sp_core::crypto::KeyTypeId;
use sp_keystore::Error as TraitError;

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
	#[display(fmt="Invalid password")]
	InvalidPassword,
	/// Invalid BIP39 phrase
	#[display(fmt="Invalid recovery phrase (BIP39) data")]
	InvalidPhrase,
	/// Invalid seed
	#[display(fmt="Invalid seed")]
	InvalidSeed,
	/// Public key type is not supported
	#[display(fmt="Key crypto type is not supported")]
	KeyNotSupported(KeyTypeId),
	/// Pair not found for public key and KeyTypeId
	#[display(fmt="Pair not found for {} public key", "_0")]
	PairNotFound(String),
	/// Keystore unavailable
	#[display(fmt="Keystore unavailable")]
	Unavailable,
}

/// Keystore Result
pub type Result<T> = std::result::Result<T, Error>;

impl From<Error> for TraitError {
	fn from(error: Error) -> Self {
		match error {
			Error::KeyNotSupported(id) => TraitError::KeyNotSupported(id),
			Error::PairNotFound(e) => TraitError::PairNotFound(e),
			Error::InvalidSeed | Error::InvalidPhrase | Error::InvalidPassword => {
				TraitError::ValidationError(error.to_string())
			},
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

