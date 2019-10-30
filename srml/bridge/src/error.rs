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

//! Common error types for the srml-bridge crate.

use crate::Error as BridgeError;

#[derive(PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Error {
	StorageRootMismatch,
	StorageValueUnavailable,
}

impl From<Error> for BridgeError {
	fn from(e: Error) -> BridgeError {
		match e {
			Error::StorageRootMismatch => BridgeError::InvalidStorageProof,
			Error::StorageValueUnavailable => BridgeError::StorageValueUnavailable,
		}
	}
}

