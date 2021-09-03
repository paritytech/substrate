// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use jsonrpsee::types::error::{CallError, Error as JsonRpseeError};
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
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// An error occurred while importing the block
	#[display(fmt = "Block import failed: {:?}", _0)]
	BlockImportError(ImportResult),
	/// Transaction pool is empty, cannot create a block
	#[display(fmt = "Transaction pool is empty, set create_empty to true,\
	if you want to create empty blocks")]
	EmptyTransactionPool,
	/// encountered during creation of Proposer.
	#[display(fmt = "Consensus Error: {}", _0)]
	ConsensusError(ConsensusError),
	/// Failed to create Inherents data
	#[display(fmt = "Inherents Error: {}", _0)]
	InherentError(InherentsError),
	/// error encountered during finalization
	#[display(fmt = "Finalization Error: {}", _0)]
	BlockchainError(BlockchainError),
	/// Supplied parent_hash doesn't exist in chain
	#[display(fmt = "Supplied parent_hash: {} doesn't exist in chain", _0)]
	#[from(ignore)]
	BlockNotFound(String),
	/// Some string error
	#[display(fmt = "{}", _0)]
	#[from(ignore)]
	StringError(String),
	/// send error
	#[display(fmt = "Consensus process is terminating")]
	Canceled(oneshot::Canceled),
	/// send error
	#[display(fmt = "Consensus process is terminating")]
	SendError(SendError),
	/// Some other error.
	#[display(fmt = "Other error: {}", _0)]
	Other(Box<dyn std::error::Error + Send + Sync>),
}

impl From<Error> for JsonRpseeError {
	fn from(err: Error) -> Self {
		use Error::*;
		match err {
			BlockImportError(e) => CallError::Custom {
				code: codes::BLOCK_IMPORT_FAILED,
				message: format!("{:?}", e),
				data: None,
			}
			.into(),
			BlockNotFound(e) => CallError::Custom {
				code: codes::BLOCK_NOT_FOUND,
				message: format!("{:?}", e),
				data: None,
			}
			.into(),
			EmptyTransactionPool => CallError::Custom {
				code: codes::EMPTY_TRANSACTION_POOL,
				message: "Empty transaction pool".to_string(),
				data: None,
			}
			.into(),
			ConsensusError(e) => CallError::Custom {
				code: codes::CONSENSUS_ERROR,
				message: format!("{:?}", e),
				data: None,
			}
			.into(),
			InherentError(e) => CallError::Custom {
				code: codes::INHERENTS_ERROR,
				message: format!("{:?}", e),
				data: None,
			}
			.into(),
			BlockchainError(e) => CallError::Custom {
				code: codes::BLOCKCHAIN_ERROR,
				message: format!("{:?}", e),
				data: None,
			}
			.into(),
			SendError(_) | Canceled(_) => CallError::Custom {
				code: codes::SERVER_SHUTTING_DOWN,
				message: "Server is shutting down".to_string(),
				data: None,
			}
			.into(),
			_ => CallError::Custom {
				code: codes::UNKNOWN_ERROR,
				message: "Unknown error".to_string(),
				data: None,
			}
			.into(),
		}
	}
}
