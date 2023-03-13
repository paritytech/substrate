// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Error types for consensus modules.

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// The error type for consensus-related operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Missing state at block with given descriptor.
	#[error("State unavailable at block {0}")]
	StateUnavailable(String),
	/// Intermediate missing.
	#[error("Missing intermediate")]
	NoIntermediate,
	/// Intermediate is of wrong type.
	#[error("Invalid intermediate")]
	InvalidIntermediate,
	/// Error checking signature.
	#[error("Message signature {0:?} by {1:?} is invalid")]
	InvalidSignature(Vec<u8>, Vec<u8>),
	/// Invalid authorities set received from the runtime.
	#[error("Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Justification requirements not met.
	#[error("Invalid justification")]
	InvalidJustification,
	/// Error from the client while importing.
	#[error("Import failed: {0}")]
	ClientImport(String),
	/// Error from the client while fetching some data from the chain.
	#[error("Chain lookup failed: {0}")]
	ChainLookup(String),
	/// Signing failed.
	#[error("Failed to sign using key: {0:?}. Reason: {1}")]
	CannotSign(Vec<u8>, String),
	/// Some other error.
	#[error(transparent)]
	Other(#[from] Box<dyn std::error::Error + Sync + Send + 'static>),
}
