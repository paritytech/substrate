// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use codec::Error as CodecError;
use sp_api::ApiError;
use sp_consensus;
use sp_runtime::transaction_validity::TransactionValidityError;
use sp_state_machine;
use std::{self, result};

/// Client Result type alias
pub type Result<T> = result::Result<T, Error>;

/// Error when the runtime failed to apply an extrinsic.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum ApplyExtrinsicFailed {
	/// The transaction cannot be included into the current block.
	///
	/// This doesn't necessary mean that the transaction itself is invalid, but it might be just
	/// unappliable onto the current block.
	#[error("Extrinsic is not valid: {0:?}")]
	Validity(#[from] TransactionValidityError),

	#[error("Application specific error")]
	Application(#[source] Box<dyn 'static + std::error::Error + Send + Sync>),
}

/// Substrate Client error
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum Error {
	#[error("Cancelled oneshot channel {0}")]
	OneShotCancelled(#[from] futures::channel::oneshot::Canceled),

	#[error(transparent)]
	Consensus(#[from] sp_consensus::Error),

	#[error("Backend error: {0}")]
	Backend(String),

	#[error("UnknownBlock: {0}")]
	UnknownBlock(String),

	#[error(transparent)]
	ApplyExtrinsicFailed(#[from] ApplyExtrinsicFailed),

	#[error("Child type is invalid")]
	InvalidChildType,

	#[error("RemoteBodyRequest: invalid extrinsics root expected: {expected} but got {received}")]
	ExtrinsicRootInvalid { received: String, expected: String },

	// `inner` cannot be made member, since it lacks `std::error::Error` trait bounds.
	#[error("Execution failed: {0:?}")]
	Execution(Box<dyn sp_state_machine::Error>),

	#[error("Blockchain")]
	Blockchain(#[source] Box<Error>),

	/// A error used by various storage subsystems.
	///
	/// Eventually this will be replaced.
	#[error("{0}")]
	StorageChanges(sp_state_machine::DefaultError),

	#[error("Invalid child storage key")]
	InvalidChildStorageKey,

	#[error("Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,

	#[error("Failed to get runtime version: {0}")]
	VersionInvalid(String),

	#[error("Provided state is invalid")]
	InvalidState,

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

	#[error("Error at calling runtime api: {0}")]
	RuntimeApiError(#[from] ApiError),

	#[error("Runtime :code missing in storage")]
	RuntimeCodeMissing,

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
	MissingHeader(String),

	#[error("State Database error: {0}")]
	StateDatabase(String),

	#[error("Failed to set the chain head to a block that's too old.")]
	SetHeadTooOld,

	#[error(transparent)]
	Application(#[from] Box<dyn std::error::Error + Send + Sync + 'static>),

	// Should be removed/improved once
	// the storage `fn`s returns typed errors.
	#[error("Runtime code error: {0}")]
	RuntimeCode(&'static str),

	// Should be removed/improved once
	// the storage `fn`s returns typed errors.
	#[error("Storage error: {0}")]
	Storage(String),
}

impl From<Box<dyn sp_state_machine::Error + Send + Sync + 'static>> for Error {
	fn from(e: Box<dyn sp_state_machine::Error + Send + Sync + 'static>) -> Self {
		Self::from_state(e)
	}
}

impl From<Box<dyn sp_state_machine::Error>> for Error {
	fn from(e: Box<dyn sp_state_machine::Error>) -> Self {
		Self::from_state(e)
	}
}

impl From<Error> for ApiError {
	fn from(err: Error) -> ApiError {
		match err {
			Error::RuntimeApiError(err) => err,
			e => ApiError::Application(Box::new(e)),
		}
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

	/// Construct from a state db error.
	// Can not be done directly, since that would make cargo run out of stack if
	// `sc-state-db` is lib is added as dependency.
	pub fn from_state_db<E>(e: E) -> Self
	where
		E: std::fmt::Debug,
	{
		Error::StateDatabase(format!("{:?}", e))
	}
}
