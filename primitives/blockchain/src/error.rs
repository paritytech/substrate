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

//! Substrate client possible errors.

use std::{self, error, result};
use sp_state_machine;
use sp_runtime::transaction_validity::TransactionValidityError;
use sp_consensus;
use derive_more::{Display, From};
use codec::Error as CodecError;

/// Client Result type alias
pub type Result<T> = result::Result<T, Error>;

/// Error when the runtime failed to apply an extrinsic.
#[derive(Debug, Display)]
pub enum ApplyExtrinsicFailed {
	/// The transaction cannot be included into the current block.
	///
	/// This doesn't necessary mean that the transaction itself is invalid, but it might be just
	/// unappliable onto the current block.
	#[display(fmt = "Extrinsic is not valid: {:?}", _0)]
	Validity(TransactionValidityError),
	/// This is used for miscellaneous errors that can be represented by string and not handleable.
	///
	/// This will become obsolete with complete migration to v4 APIs.
	#[display(fmt = "Extrinsic failed: {:?}", _0)]
	Msg(String),
}

/// Substrate Client error
#[derive(Debug, Display, From)]
pub enum Error {
	/// Consensus Error
	#[display(fmt = "Consensus: {}", _0)]
	Consensus(sp_consensus::Error),
	/// Backend error.
	#[display(fmt = "Backend error: {}", _0)]
	#[from(ignore)]
	Backend(String),
	/// Unknown block.
	#[display(fmt = "UnknownBlock: {}", _0)]
	#[from(ignore)]
	UnknownBlock(String),
	/// The `apply_extrinsic` is not valid due to the given `TransactionValidityError`.
	#[display(fmt = "{:?}", _0)]
	ApplyExtrinsicFailed(ApplyExtrinsicFailed),
	/// Execution error.
	#[display(fmt = "Execution: {}", _0)]
	Execution(Box<dyn sp_state_machine::Error>),
	/// Blockchain error.
	#[display(fmt = "Blockchain: {}", _0)]
	Blockchain(Box<Error>),
	/// Invalid authorities set received from the runtime.
	#[display(fmt = "Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Could not get runtime version.
	#[display(fmt = "Failed to get runtime version: {}", _0)]
	#[from(ignore)]
	VersionInvalid(String),
	/// Genesis config is invalid.
	#[display(fmt = "Genesis config provided is invalid")]
	GenesisInvalid,
	/// Error decoding header justification.
	#[display(fmt = "error decoding justification for header")]
	JustificationDecode,
	/// Justification for header is correctly encoded, but invalid.
	#[display(fmt = "bad justification for header: {}", _0)]
	#[from(ignore)]
	BadJustification(String),
	/// Not available on light client.
	#[display(fmt = "This method is not currently available when running in light client mode")]
	NotAvailableOnLightClient,
	/// Invalid remote CHT-based proof.
	#[display(fmt = "Remote node has responded with invalid header proof")]
	InvalidCHTProof,
	/// Remote fetch has been cancelled.
	#[display(fmt = "Remote data fetch has been cancelled")]
	RemoteFetchCancelled,
	/// Remote fetch has been failed.
	#[display(fmt = "Remote data fetch has been failed")]
	RemoteFetchFailed,
	/// Error decoding call result.
	#[display(fmt = "Error decoding call result of {}: {}", _0, _1)]
	CallResultDecode(&'static str, CodecError),
	/// Error converting a parameter between runtime and node.
	#[display(fmt = "Error converting `{}` between runtime and node", _0)]
	#[from(ignore)]
	RuntimeParamConversion(String),
	/// Changes tries are not supported.
	#[display(fmt = "Changes tries are not supported by the runtime")]
	ChangesTriesNotSupported,
	/// Error reading changes tries configuration.
	#[display(fmt = "Error reading changes tries configuration")]
	ErrorReadingChangesTriesConfig,
	/// Key changes query has failed.
	#[display(fmt = "Failed to check changes proof: {}", _0)]
	#[from(ignore)]
	ChangesTrieAccessFailed(String),
	/// Last finalized block not parent of current.
	#[display(fmt = "Did not finalize blocks in sequential order.")]
	#[from(ignore)]
	NonSequentialFinalization(String),
	/// Safety violation: new best block not descendent of last finalized.
	#[display(fmt = "Potential long-range attack: block not in finalized chain.")]
	NotInFinalizedChain,
	/// Hash that is required for building CHT is missing.
	#[display(fmt = "Failed to get hash of block for building CHT")]
	MissingHashRequiredForCHT,
	/// Invalid calculated state root on block import.
	#[display(fmt = "Calculated state root does not match.")]
	InvalidStateRoot,
	/// Incomplete block import pipeline.
	#[display(fmt = "Incomplete block import pipeline.")]
	IncompletePipeline,
	#[display(fmt = "Transaction pool not ready for block production.")]
	TransactionPoolNotReady,
	/// A convenience variant for String
	#[display(fmt = "{}", _0)]
	Msg(String),
}

impl error::Error for Error {
	fn source(&self) -> Option<&(dyn error::Error + 'static)> {
		match self {
			Error::Consensus(e) => Some(e),
			Error::Blockchain(e) => Some(e),
			_ => None,
		}
	}
}

impl<'a> From<&'a str> for Error {
	fn from(s: &'a str) -> Self {
		Error::Msg(s.into())
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
