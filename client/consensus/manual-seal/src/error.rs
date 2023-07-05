// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! A manual sealing engine: the engine listens for rpc calls to seal blocks and create forks.
//! This is suitable for a testing environment.

use futures::channel::{mpsc::SendError, oneshot};
use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};
use sc_consensus::ImportResult;
use sp_blockchain::Error as BlockchainError;
use sp_consensus::Error as ConsensusError;
use sp_inherents::Error as InherentsError;

/// Error code for rpc
mod codes {
	pub const SERVER_SHUTTING_DOWN: i32 = 10_000;
	pub const BLOCK_IMPORT_FAILED: i32 = 11_000;
	pub const EMPTY_TRANSACTION_POOL: i32 = 12_000;
	pub const BLOCK_NOT_FOUND: i32 = 13_000;
	pub const CONSENSUS_ERROR: i32 = 14_000;
	pub const INHERENTS_ERROR: i32 = 15_000;
	pub const BLOCKCHAIN_ERROR: i32 = 16_000;
	pub const UNKNOWN_ERROR: i32 = 20_000;
}

/// errors encountered by background block authorship task
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// An error occurred while importing the block
	#[error("Block import failed: {0:?}")]
	BlockImportError(ImportResult),
	/// Transaction pool is empty, cannot create a block
	#[error(
		"Transaction pool is empty, set create_empty to true, if you want to create empty blocks"
	)]
	EmptyTransactionPool,
	/// encountered during creation of Proposer.
	#[error("Consensus Error: {0}")]
	ConsensusError(#[from] ConsensusError),
	/// Failed to create Inherents data
	#[error("Inherents Error: {0}")]
	InherentError(#[from] InherentsError),
	/// error encountered during finalization
	#[error("Finalization Error: {0}")]
	BlockchainError(#[from] BlockchainError),
	/// Supplied parent_hash doesn't exist in chain
	#[error("Supplied parent_hash: {0} doesn't exist in chain")]
	BlockNotFound(String),
	/// Some string error
	#[error("{0}")]
	StringError(String),
	/// send error
	#[error("Consensus process is terminating")]
	Canceled(#[from] oneshot::Canceled),
	/// send error
	#[error("Consensus process is terminating")]
	SendError(#[from] SendError),
	/// Some other error.
	#[error("Other error: {0}")]
	Other(Box<dyn std::error::Error + Send + Sync>),
}

impl From<ImportResult> for Error {
	fn from(err: ImportResult) -> Self {
		Error::BlockImportError(err)
	}
}

impl From<String> for Error {
	fn from(s: String) -> Self {
		Error::StringError(s)
	}
}

impl Error {
	fn to_code(&self) -> i32 {
		use Error::*;
		match self {
			BlockImportError(_) => codes::BLOCK_IMPORT_FAILED,
			BlockNotFound(_) => codes::BLOCK_NOT_FOUND,
			EmptyTransactionPool => codes::EMPTY_TRANSACTION_POOL,
			ConsensusError(_) => codes::CONSENSUS_ERROR,
			InherentError(_) => codes::INHERENTS_ERROR,
			BlockchainError(_) => codes::BLOCKCHAIN_ERROR,
			SendError(_) | Canceled(_) => codes::SERVER_SHUTTING_DOWN,
			_ => codes::UNKNOWN_ERROR,
		}
	}
}

impl From<Error> for JsonRpseeError {
	fn from(err: Error) -> Self {
		CallError::Custom(ErrorObject::owned(err.to_code(), err.to_string(), None::<()>)).into()
	}
}
