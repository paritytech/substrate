// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Rust executor possible errors.

use state_machine;
use std::{error, fmt};
use serializer;
use wasmi;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
pub enum Error {
	/// Unserializable Data
	InvalidData(serializer::Error),
	/// Trap occured during execution
	Trap(wasmi::Trap),
	/// Wasmi loading/instantiating error
	Wasmi(wasmi::Error),
	/// Error in the API. Parameter is an error message.
	ApiError(String),
	/// Method is not found
	MethodNotFound(String),
	/// Code is invalid (expected single byte)
	InvalidCode(Vec<u8>),
	/// Could not get runtime version.
	VersionInvalid,
	/// Externalities have failed.
	Externalities,
	/// Invalid index.
	InvalidIndex,
	/// Invalid return type.
	InvalidReturn,
	/// Runtime failed.
	Runtime,
	/// Runtime failed.
	InvalidMemoryReference,
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::InvalidData(ref err) => Some(err),
			Error::Trap(ref err) => Some(err),
			Error::Wasmi(ref err) => Some(err),
			_ => None,
		}
	}
}

impl fmt::Debug for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Error::InvalidData(ref err) => write!(f, "{}", err),
			Error::Trap(ref err) => write!(f, "{}", err),
			Error::Wasmi(ref err) => write!(f, "{}", err),
			Error::ApiError(ref err) => write!(f, "{}", err),
			Error::MethodNotFound(ref t) => write!(f, "Method not found: '{}'", t),
			Error::InvalidCode(ref c) => write!(f, "Invalid Code: {:?}", c),
			Error::VersionInvalid => write!(f, "On-chain runtime does not specify version"),
			Error::Externalities => write!(f, "Externalities error"),
			Error::InvalidIndex => write!(f, "Invalid index provided"),
			Error::InvalidReturn => write!(f, "Invalid type returned (should be u64)"),
			Error::Runtime => write!(f, "Runtime error"),
			Error::InvalidMemoryReference => write!(f, "Invalid memory reference"),
		}
	}
}

impl From<serializer::Error> for Error {
	fn from(err: serializer::Error) -> Error {
		Error::InvalidData(err)
	}
}

impl From<wasmi::Trap> for Error {
	fn from(err: wasmi::Trap) -> Error {
		Error::Trap(err)
	}
}

impl From<wasmi::Error> for Error {
	fn from(err: wasmi::Error) -> Error {
		Error::Wasmi(err)
	}
}

impl state_machine::Error for Error {}
