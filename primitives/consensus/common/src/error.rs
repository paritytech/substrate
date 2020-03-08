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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Error types in Consensus
use sp_version::RuntimeVersion;
use sp_core::ed25519::{Public, Signature};
use std::error;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Missing state at block with given descriptor.
	#[display(fmt="State unavailable at block {}", _0)]
	StateUnavailable(String),
	/// I/O terminated unexpectedly
	#[display(fmt="I/O terminated unexpectedly.")]
	IoTerminated,
	/// Intermediate missing.
	#[display(fmt="Missing intermediate.")]
	NoIntermediate,
	/// Intermediate is of wrong type.
	#[display(fmt="Invalid intermediate.")]
	InvalidIntermediate,
	/// Unable to schedule wake-up.
	#[display(fmt="Timer error: {}", _0)]
	FaultyTimer(std::io::Error),
	/// Error while working with inherent data.
	#[display(fmt="InherentData error: {}", _0)]
	InherentData(sp_inherents::Error),
	/// Unable to propose a block.
	#[display(fmt="Unable to create block proposal.")]
	CannotPropose,
	/// Error checking signature
	#[display(fmt="Message signature {:?} by {:?} is invalid.", _0, _1)]
	InvalidSignature(Signature, Public),
	/// Invalid authorities set received from the runtime.
	#[display(fmt="Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Account is not an authority.
	#[display(fmt="Message sender {:?} is not a valid authority.", _0)]
	InvalidAuthority(Public),
	/// Authoring interface does not match the runtime.
	#[display(fmt="Authoring for current \
				runtime is not supported. Native ({}) cannot author for on-chain ({}).", native, on_chain)]
	IncompatibleAuthoringRuntime { native: RuntimeVersion, on_chain: RuntimeVersion },
	/// Authoring interface does not match the runtime.
	#[display(fmt="Authoring for current runtime is not supported since it has no version.")]
	RuntimeVersionMissing,
	/// Authoring interface does not match the runtime.
	#[display(fmt="Authoring in current build is not supported since it has no runtime.")]
	NativeRuntimeMissing,
	/// Justification requirements not met.
	#[display(fmt="Invalid justification.")]
	InvalidJustification,
	/// Some other error.
	#[display(fmt="Other error: {}", _0)]
	Other(Box<dyn error::Error + Send>),
	/// Error from the client while importing
	#[display(fmt="Import failed: {}", _0)]
	#[from(ignore)]
	ClientImport(String),
	/// Error from the client while importing
	#[display(fmt="Chain lookup failed: {}", _0)]
	#[from(ignore)]
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
