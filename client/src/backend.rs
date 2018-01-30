// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot Client data backend

use state_machine;
use error;
use primitives::block;
use blockchain::{self, BlockId};

/// Block insertion transction. Keeps hold if the inseted block state and data.
pub trait BlockImportOperation {
	/// Associated state backend type.
	type State: state_machine::backend::Backend;

	/// Returns pending state.
	fn state(&self) -> error::Result<Self::State>;
	/// Append block data to the transaction.
	fn import_block(&mut self, header: block::Header, body: Option<block::Body>, is_new_best: bool) -> error::Result<()>;
}

/// Client backend. Manages the data layer.
pub trait Backend {
	/// Associated block insertion transaction type.
	type BlockImportOperation: BlockImportOperation;
	/// Associated blockchain backend type.
	type Blockchain: blockchain::Backend;
	/// Associated state backend type.
	type State: state_machine::backend::Backend;

	/// Begin a new block insertion transaction with given parent block id.
	fn begin_transaction(&self, block: BlockId) -> error::Result<Self::BlockImportOperation>;
	/// Commit block insertion.
	fn commit_transaction(&self, transaction: Self::BlockImportOperation) -> error::Result<()>;
	/// Returns reference to blockchain backend.
	fn blockchain(&self) -> &Self::Blockchain;
	/// Returns state backend for specified block.
	fn state_at(&self, block: BlockId) -> error::Result<Self::State>;
}

