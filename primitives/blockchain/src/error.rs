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

use std::{self, result};
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
	#[error("Extrinsic failed: {0}")]
	Msg(String),
}

/// Substrate Client error
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Consensus Error
	#[error(transparent)]
	Consensus(#[from] sp_consensus::Error),
	/// Backend error.
	#[error("Backend error: {0}")]
	Backend(String),
	/// Unknown block.
	#[error("UnknownBlock: {0}")]
	UnknownBlock(String),
	/// The `apply_extrinsic` is not valid due to the given `TransactionValidityError`.
	#[error(transparent)]
	ApplyExtrinsicFailed(#[from] ApplyExtrinsicFailed),
	/// Execution error.
	#[error("Execution failed: {0:?}")]
	Execution(Box<dyn sp_state_machine::Error>),
	/// Blockchain error.
	#[error("Blockchain")]
	Blockchain(#[source] Box<Error>),
	/// Invalid authorities set received from the runtime.
	#[error("Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Could not get runtime version.
	#[error("Failed to get runtime version: {0}")]
	VersionInvalid(String),
	/// Genesis config is invalid.
	#[error("Genesis config provided is invalid")]
	GenesisInvalid,
	/// Error decoding header justification.
	#[error("error decoding justification for header")]
	JustificationDecode,
	/// Justification for header is correctly encoded, but invalid.
	#[error("bad justification for header: {0}")]
	BadJustification(String),
	/// Not available on light client.
	#[error("This method is not currently available when running in light client mode")]
	NotAvailableOnLightClient,
	/// Invalid remote CHT-based proof.
	#[error("Remote node has responded with invalid header proof")]
	InvalidCHTProof,
	/// Remote fetch has been cancelled.
	#[error("Remote data fetch has been cancelled")]
	RemoteFetchCancelled,
	/// Remote fetch has been failed.
	#[error("Remote data fetch has been failed")]
	RemoteFetchFailed,
	/// Error decoding call result.
	#[error("Error decoding call result of {0}")]
	CallResultDecode(&'static str, #[source] CodecError),
	/// Error converting a parameter between runtime and node.
	#[error("Error converting `{0}` between runtime and node")]
	RuntimeParamConversion(String),
	/// Changes tries are not supported.
	#[error("Changes tries are not supported by the runtime")]
	ChangesTriesNotSupported,
	/// Error reading changes tries configuration.
	#[error("Error reading changes tries configuration")]
	ErrorReadingChangesTriesConfig,
	/// Key changes query has failed.
	#[error("Failed to check changes proof: {0}")]
	ChangesTrieAccessFailed(String),
	/// Last finalized block not parent of current.
	#[error("Did not finalize blocks in sequential order.")]
	NonSequentialFinalization(String),
	/// Safety violation: new best block not descendent of last finalized.
	#[error("Potential long-range attack: block not in finalized chain.")]
	NotInFinalizedChain,
	/// Hash that is required for building CHT is missing.
	#[error("Failed to get hash of block for building CHT")]
	MissingHashRequiredForCHT,
	/// Invalid calculated state root on block import.
	#[error("Calculated state root does not match.")]
	InvalidStateRoot,
	/// Incomplete block import pipeline.
	#[error("Incomplete block import pipeline.")]
	IncompletePipeline,
	#[error("Transaction pool not ready for block production.")]
	TransactionPoolNotReady,
	#[error("Database")]
	DatabaseError(#[from] sp_database::error::DatabaseError),
	/// A convenience variant for String
	#[error("{0}")]
	Msg(String),
}

impl<'a> From<&'a str> for Error {
	fn from(s: &'a str) -> Self {
		Error::Msg(s.into())
	}
}

impl From<String> for Error {
	fn from(s: String) -> Self {
		Error::Msg(s)
	}
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
