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

//! Error types in Consensus
use runtime_version::RuntimeVersion;
use primitives::ed25519::{Public, Signature};
use std::{error, fmt};

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
pub enum Error {
	/// Missing state at block with given descriptor.
	StateUnavailable(String),
	/// I/O terminated unexpectedly
	IoTerminated,
	/// Unable to schedule wakeup.
	FaultyTimer(::tokio_timer::Error),
	/// Error while working with inherent data.
	InherentData(String),
	/// Unable to propose a block.
	CannotPropose,
	/// Error checking signature
	InvalidSignature(Signature, Public),
	/// Invalid authorities set received from the runtime.
	InvalidAuthoritiesSet,
	/// Account is not an authority.
	InvalidAuthority(Public),
	/// Authoring interface does not match the runtime.
	IncompatibleAuthoringRuntime { native: RuntimeVersion, on_chain: RuntimeVersion },
	/// Authoring interface does not match the runtime.
	RuntimeVersionMissing,
	/// Authoring interface does not match the runtime.
	NativeRuntimeMissing,
	/// Justification requirements not met.
	InvalidJustification,
	/// Some other error.
	Other(Box<error::Error + Send>),
	/// Error from the client while importing
	ClientImport(String),
	/// Error from the client while importing
	ChainLookup(String),
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::FaultyTimer(ref err) => Some(err),
			// Note: we really would like to return `Some(err)` here, but for some reason we can't
			// convert a `&dyn Error + Send + 'static` into a `&dyn Error + 'static`.
			Error::Other(ref _err) => None,
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
			Error::StateUnavailable(ref b) => write!(f, "State unavailable at block {}", b),
			Error::IoTerminated => write!(f, "I/O terminated unexpectedly."),
			Error::FaultyTimer(ref e) => write!(f, "Timer error: {}", e),
			Error::InherentData(ref e) => write!(f, "InherentData error: {}", e),
			Error::CannotPropose => write!(f, "Unable to create block proposal."),
			Error::InvalidSignature(ref s, ref a) => write!(f, "Message signature {:?} by {:?} is invalid.", s, a),
			Error::InvalidAuthoritiesSet => write!(f, "Current state of blockchain has invalid authorities set"),
			Error::InvalidAuthority(ref a) => write!(f, "Message sender {:?} is not a valid authority.", a),
			Error::IncompatibleAuthoringRuntime { ref native, ref on_chain } => write!(f, "Authoring for current \
				runtime is not supported. Native ({}) cannot author for on-chain ({}).", native, on_chain),
			Error::RuntimeVersionMissing => write!(f, "Authoring for current runtime is not supported since \
				it has no version."),
			Error::NativeRuntimeMissing => write!(f, "Authoring in current build is not supported since it has no runtime."),
			Error::InvalidJustification => write!(f, "Invalid justification."),
			Error::Other(ref e) => write!(f, "Other error: {}", e),
			Error::ClientImport(ref reason) => write!(f, "Import failed: {}", reason),
			Error::ChainLookup(ref reason) => write!(f, "Chain lookup failed: {}", reason),
		}
	}
}
