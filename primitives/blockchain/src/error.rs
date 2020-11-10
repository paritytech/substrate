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

//! Substrate client possible errors.

use std::{self, result, path::PathBuf};
use sp_state_machine;
use sp_runtime::transaction_validity::TransactionValidityError;
use sp_consensus;
use codec::Error as CodecError;

/// Client Result type alias
pub type Result<T> = result::Result<T, Error>;

/// Error when the runtime failed to apply an extrinsic.
#[derive(Debug, thiserror::Error)]
pub enum ApplyExtrinsicFailed {
	/// The transaction cannot be included into the current block.
	///
	/// This doesn't necessary mean that the transaction itself is invalid, but it might be just
	/// unappliable onto the current block.
	#[error("Extrinsic is not valid: {0:?}")]
	Validity(#[from] TransactionValidityError),

	/// This is used for miscellaneous errors that can be represented by string and not handleable.
	///
	/// This will become obsolete with complete migration to v4 APIs.
	#[deprecated(note = "Introduce more typed error variants as needed")]
	#[error("Extrinsic failed: {0}")]
	Msg(String),
}

/// Substrate Client error
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error(transparent)]
	Consensus(#[from] sp_consensus::Error),

	#[error("Backend error: {0}")]
	Backend(String),

	#[error("UnknownBlock: {0}")]
	UnknownBlock(String),

	#[error(transparent)]
	ApplyExtrinsicFailed(#[from] ApplyExtrinsicFailed),

	// `inner` cannot be made member, since it lacks `std::error::Error` trait bounds.
	#[error("Execution failed: {0:?}")]
	Execution(Box<dyn sp_state_machine::Error>),

	#[error("Blockchain")]
	Blockchain(#[source] Box<Error>),

	#[error("Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,

	#[error("Failed to get runtime version: {0}")]
	VersionInvalid(String),

	#[error("Genesis config provided is invalid")]
	GenesisInvalid,

	#[error("error decoding justification for header")]
	JustificationDecode,

	#[error("bad justification for header: {0}")]
	BadJustification(String),

	#[error("This method is not currently available when running in light client mode")]
	NotAvailableOnLightClient,

	#[error("Remote node has responded with invalid header proof")]
	InvalidCHTProof,

	#[error("Remote data fetch has been cancelled")]
	RemoteFetchCancelled,

	#[error("Remote data fetch has been failed")]
	RemoteFetchFailed,

	#[error("Error decoding call result of {0}")]
	CallResultDecode(&'static str, #[source] CodecError),

	#[error("Error converting `{0}` between runtime and node")]
	RuntimeParamConversion(String),

	#[error("Changes tries are not supported by the runtime")]
	ChangesTriesNotSupported,

	#[error("Error reading changes tries configuration")]
	ErrorReadingChangesTriesConfig,

	#[error("Failed to check changes proof: {0}")]
	ChangesTrieAccessFailed(String),

	#[error("Did not finalize blocks in sequential order.")]
	NonSequentialFinalization(String),

	#[error("Potential long-range attack: block not in finalized chain.")]
	NotInFinalizedChain,

	#[error("Failed to get hash of block for building CHT")]
	MissingHashRequiredForCHT,

	#[error("Calculated state root does not match.")]
	InvalidStateRoot,

	#[error("Incomplete block import pipeline.")]
	IncompletePipeline,

	#[error("Transaction pool not ready for block production.")]
	TransactionPoolNotReady,

	#[error("Database")]
	DatabaseError(#[from] sp_database::error::DatabaseError),

	#[error("Failed to get header for hash {0}")]
	MissingHashInHeader(String),

	#[error("Failed to load the block weight for block {0}")]
	MissingBlockWeightInHeader(String),

	#[error("WASM override IO error")]
	WasmOverrideIo(PathBuf, #[source] std::io::Error),

	#[error("Overwriting WASM requires a directory where local \
	WASM is stored. {} is not a directory", .0.display())]
	WasmOverrideNotADirectory(PathBuf),

	#[error("Duplicate WASM Runtimes found: \n{}\n", .0.join("\n") )]
	DuplicateWasmRuntime(Vec<String>),

	#[error(transparent)]
	Foreign(#[from] Box<dyn std::error::Error + Send + Sync + 'static>),

	/// Should be avoided if possible, use `Foreign` instead.
	#[error("{0}")]
	Msg(String),
}

impl From<Box<dyn sp_state_machine::Error + Send + Sync>> for Error {
	fn from(e: Box<dyn sp_state_machine::Error + Send + Sync>) -> Self {
		Self::from_state(e)
	}
}

impl From<Box<dyn sp_state_machine::Error>> for Error {
	fn from(e: Box<dyn sp_state_machine::Error>) -> Self {
		Self::from_state(e)
	}
}

impl From<String> for Error {
	fn from(msg: String) -> Self {
		Self::Msg(msg)
	}
}
impl From<&str> for Error {
	fn from(msg: &str) -> Self {
		Self::Msg(msg.to_owned())
	}
}


impl Error {
	/// Chain a blockchain error.
	pub fn from_blockchain(e: Box<Error>) -> Self {
		Error::Blockchain(e)
	}

	/// Chain a state error.
	pub fn from_state(e: Box<dyn sp_state_machine::Error>) -> Self {
		Error::Execution(e)
	}
}
