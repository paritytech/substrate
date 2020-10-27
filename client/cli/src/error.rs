// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Initialization errors.

use sp_core::crypto;

/// Result type alias for the CLI.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the CLI.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Io error
	#[error(transparent)]
	Io(#[from] std::io::Error),
	/// Cli error
	#[error(transparent)]
	Cli(#[from] structopt::clap::Error),
	/// Service error
	#[error(transparent)]
	Service(#[from] sc_service::Error),
	/// Client error
	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),
	/// scale codec error
	#[error(transparent)]
	Codec(#[from] parity_scale_codec::Error),
	/// Input error
	#[error("Invalid input: {0}")]
	Input(String),
	/// Invalid listen multiaddress
	#[error("Invalid listen multiaddress")]
	InvalidListenMultiaddress,
	/// Application specific error chain sequence forwarder.
	#[error(transparent)]
	Application(#[from] Box<dyn std::error::Error>),
	/// URI error.
	#[error("Invalid URI; expecting either a secret URI or a public URI.")]
	InvalidUri(crypto::PublicError),
	/// Signature length mismatch.
	#[error("Signature has an invalid length. Read {read} bytes, expected {expected} bytes")]
	SignatureInvalidLength {
		/// Amount of signature bytes read.
		read: usize,
		/// Expected number of signature bytes.
		expected: usize,
	},
	/// Missing base path argument.
	#[error("The base path is missing, please provide one")]
	MissingBasePath,
	/// Unknown key type specifier or missing key type specifier.
	#[error("Unknown key type, must be a known 4-character sequence")]
	KeyTypeInvalid,
	/// Signature verification failed.
	#[error("Signature verification failed")]
	SignatureInvalid,
	/// Storing a given key failed.
	#[error("Key store operation failed")]
	KeyStoreOperation,
	/// An issue with the underlying key storage was encountered.
	#[error("Key storage issue encountered")]
	KeyStorage(#[from] sc_keystore::Error),
	/// Bytes are not decodable when interpreted as hexadecimal string.
	#[error("Invalid hex base data")]
	HexDataConversion(#[from] hex::FromHexError),
	/// Shortcut type to specify types on the fly, discouraged.
	#[deprecated = "Use `Forwarded` with an error type instead."]
	#[error("Other: {0}")]
	Other(String),
}

impl std::convert::From<&str> for Error {
	fn from(s: &str) -> Error {
		Error::Input(s.to_string())
	}
}

impl std::convert::From<String> for Error {
	fn from(s: String) -> Error {
		Error::Input(s.to_string())
	}
}

impl std::convert::From<crypto::PublicError> for Error {
	fn from(e: crypto::PublicError) -> Error {
		Error::InvalidUri(e)
	}
}
