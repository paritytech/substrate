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
use std::error;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	#[display(fmt="State unavailable at block {}", _0)]
	/// Missing state at block with given descriptor.
	StateUnavailable(String),
	#[display(fmt="I/O terminated unexpectedly.")]
	/// I/O terminated unexpectedly
	IoTerminated,
	#[display(fmt="Timer error: {}", _0)]
	/// Unable to schedule wakeup.
	FaultyTimer(tokio_timer::Error),
	#[display(fmt="InherentData error: {}", _0)]
	/// Error while working with inherent data.
	InherentData(String),
	#[display(fmt="Unable to create block proposal.")]
	/// Unable to propose a block.
	CannotPropose,
	#[display(fmt="Message signature {:?} by {:?} is invalid.", _0, _1)]
	/// Error checking signature
	InvalidSignature(Signature, Public),
	#[display(fmt="Current state of blockchain has invalid authorities set")]
	/// Invalid authorities set received from the runtime.
	InvalidAuthoritiesSet,
	#[display(fmt="Message sender {:?} is not a valid authority.", _0)]
	/// Account is not an authority.
	InvalidAuthority(Public),
	#[display(fmt="Authoring for current \
				runtime is not supported. Native ({}) cannot author for on-chain ({}).", native, on_chain)]
	/// Authoring interface does not match the runtime.
	IncompatibleAuthoringRuntime { native: RuntimeVersion, on_chain: RuntimeVersion },
	#[display(fmt="Authoring for current runtime is not supported since it has no version.")]
	/// Authoring interface does not match the runtime.
	RuntimeVersionMissing,
	#[display(fmt="Authoring in current build is not supported since it has no runtime.")]
	/// Authoring interface does not match the runtime.
	NativeRuntimeMissing,
	#[display(fmt="Invalid justification.")]
	/// Justification requirements not met.
	InvalidJustification,
	#[display(fmt="Other error: {}", _0)]
	/// Some other error.
	Other(Box<error::Error + Send>),
	#[display(fmt="Import failed: {}", _0)]
	/// Error from the client while importing
	ClientImport(String),
	#[display(fmt="Chain lookup failed: {}", _0)]
	/// Error from the client while importing
	ChainLookup(String),
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::FaultyTimer(ref err) => Some(err),
			Error::Other(ref err) => Some(&**err),
			_ => None,
		}
	}
}
