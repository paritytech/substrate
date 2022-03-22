// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
use sp_core::ed25519::Public;
use sp_version::RuntimeVersion;
use std::error;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
	/// Missing state at block with given descriptor.
	#[error("State unavailable at block {0}")]
	StateUnavailable(String),
	/// I/O terminated unexpectedly
	#[error("I/O terminated unexpectedly.")]
	IoTerminated,
	/// Intermediate missing.
	#[error("Missing intermediate.")]
	NoIntermediate,
	/// Intermediate is of wrong type.
	#[error("Invalid intermediate.")]
	InvalidIntermediate,
	/// Unable to schedule wake-up.
	#[error("Timer error: {0}")]
	FaultyTimer(#[from] std::io::Error),
	/// Error while working with inherent data.
	#[error("InherentData error: {0}")]
	InherentData(#[from] sp_inherents::Error),
	/// Unable to propose a block.
	#[error("Unable to create block proposal.")]
	CannotPropose,
	/// Error checking signature
	#[error("Message signature {0:?} by {1:?} is invalid.")]
	InvalidSignature(Vec<u8>, Vec<u8>),
	/// Invalid authorities set received from the runtime.
	#[error("Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Account is not an authority.
	#[error("Message sender {0:?} is not a valid authority")]
	InvalidAuthority(Public),
	/// Authoring interface does not match the runtime.
	#[error(
		"Authoring for current \
				runtime is not supported. Native ({native}) cannot author for on-chain ({on_chain})."
	)]
	IncompatibleAuthoringRuntime { native: RuntimeVersion, on_chain: RuntimeVersion },
	/// Authoring interface does not match the runtime.
	#[error("Authoring for current runtime is not supported since it has no version.")]
	RuntimeVersionMissing,
	/// Authoring interface does not match the runtime.
	#[error("Authoring in current build is not supported since it has no runtime.")]
	NativeRuntimeMissing,
	/// Justification requirements not met.
	#[error("Invalid justification.")]
	InvalidJustification,
	/// Some other error.
	#[error(transparent)]
	Other(#[from] Box<dyn error::Error + Sync + Send + 'static>),
	/// Error from the client while importing
	#[error("Import failed: {0}")]
	ClientImport(String),
	/// Error from the client while importing
	#[error("Chain lookup failed: {0}")]
	ChainLookup(String),
	/// Signing failed
	#[error("Failed to sign using key: {0:?}. Reason: {1}")]
	CannotSign(Vec<u8>, String),
}

impl core::convert::From<Public> for Error {
	fn from(p: Public) -> Self {
		Self::InvalidAuthority(p)
	}
}

impl core::convert::From<String> for Error {
	fn from(s: String) -> Self {
		Self::StateUnavailable(s)
	}
}
