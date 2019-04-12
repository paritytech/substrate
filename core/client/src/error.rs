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

//! Substrate client possible errors.

use std::{self, error, result};
use state_machine;
use runtime_primitives::ApplyError;
use consensus;
use derive_more::{Display, From};

/// Client Result type alias
pub type Result<T> = result::Result<T, Error>;

/// Substrate Client error
#[derive(Debug, Display, From)]
pub enum Error {
	/// Consensus Error
	#[display(fmt = "Consensus: {}", _0)]
	Consensus(consensus::Error),
	/// Backend error.
	#[display(fmt = "Backend error: {}", _0)]
	Backend(String),
	/// Unknown block.
	#[display(fmt = "UnknownBlock: {}", _0)]
	UnknownBlock(String),
	/// Applying extrinsic error.
	#[display(fmt = "Extrinsic error: {:?}", _0)]
	ApplyExtrinsicFailed(ApplyError),
	/// Execution error.
	#[display(fmt = "Execution: {}", _0)]
	Execution(Box<state_machine::Error>),
	/// Blockchain error.
	#[display(fmt = "Blockchain: {}", _0)]
	Blockchain(Box<Error>),
	/// Invalid authorities set received from the runtime.
	#[display(fmt = "Current state of blockchain has invalid authorities set")]
	InvalidAuthoritiesSet,
	/// Could not get runtime version.
	#[display(fmt = "On-chain runtime does not specify version")]
	VersionInvalid,
	/// Genesis config is invalid.
	#[display(fmt = "Genesis config provided is invalid")]
	GenesisInvalid,
	/// Bad justification for header.
	#[display(fmt = "bad justification for header: {}", _0)]
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
	#[display(fmt = "Error decoding call result of {}", _0)]
	CallResultDecode(&'static str),
	/// Error converting a parameter between runtime and node.
	#[display(fmt = "Error converting `{}` between runtime and node", _0)]
	RuntimeParamConversion(&'static str),
	/// Changes tries are not supported.
	#[display(fmt = "Changes tries are not supported by the runtime")]
	ChangesTriesNotSupported,
	/// Key changes query has failed.
	#[display(fmt = "Failed to check changes proof: {}", _0)]
	ChangesTrieAccessFailed(String),
	/// Last finalized block not parent of current.
	#[display(fmt = "Did not finalize blocks in sequential order.")]
	NonSequentialFinalization(String),
	/// Safety violation: new best block not descendent of last finalized.
	#[display(fmt = "Potential long-range attack: block not in finalized chain.")]
	NotInFinalizedChain,
	/// Hash that is required for building CHT is missing.
	#[display(fmt = "Failed to get hash of block#{} for building CHT#{}", _0, _1)]
	MissingHashRequiredForCHT(u64, u64),
	/// A convenience variant for String
	#[display(fmt = "{}", _0)]
	Msg(String),
}

impl error::Error for Error {
	fn source(&self) -> Option<&(error::Error + 'static)> {
		match self {
			Error::Consensus(e) => Some(e),
			Error::Blockchain(e) => Some(e),
			_ => None,
		}
	}
}

impl From<String> for Error {
	fn from(s: String) -> Self {
		Error::Msg(s)
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
	pub fn from_state(e: Box<state_machine::Error + Send>) -> Self {
		Error::Execution(e)
	}
}

impl state_machine::Error for Error {}
