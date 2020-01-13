// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

/// State Machine Errors

use std::fmt;

/// State Machine Error bound.
///
/// This should reflect Wasm error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}

impl<T: 'static + fmt::Debug + fmt::Display + Send> Error for T {}

/// Externalities Error.
///
/// Externalities are not really allowed to have errors, since it's assumed that dependent code
/// would not be executed unless externalities were available. This is included for completeness,
/// and as a transition away from the pre-existing framework.
#[derive(Debug, Eq, PartialEq)]
pub enum ExecutionError {
	/// Backend error.
	Backend(String),
	/// The entry `:code` doesn't exist in storage so there's no way we can execute anything.
	CodeEntryDoesNotExist,
	/// Backend is incompatible with execution proof generation process.
	UnableToGenerateProof,
	/// Invalid execution proof.
	InvalidProof,
}

impl fmt::Display for ExecutionError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Externalities Error") }
}
