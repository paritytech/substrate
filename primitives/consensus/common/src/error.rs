// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Error types in Consensus
use sp_version::RuntimeVersion;
use sp_core::ed25519::Public;
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
	InvalidSignature(Vec<u8>, Vec<u8>),
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
	/// Signing failed
	#[display(fmt="Failed to sign using key: {:?}. Reason: {}", _0, _1)]
	CannotSign(Vec<u8>, String)
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
