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

use state_machine::backend::Backend as StateBackend;
use error;
use primitives::block::{self, Id as BlockId};
use primitives;

/// Block insertion operation. Keeps hold if the inserted block state and data.
pub trait BlockImportOperation {
	/// Associated state backend type.
	type State: StateBackend;

	/// Returns pending state.
	fn state(&self) -> error::Result<&Self::State>;
	/// Append block data to the transaction.
	fn set_block_data(&mut self, header: block::Header, body: Option<block::Body>, justification: Option<primitives::bft::Justification>, is_new_best: bool) -> error::Result<()>;
	/// Inject storage data into the database.
	fn update_storage(&mut self, update: <Self::State as StateBackend>::Transaction) -> error::Result<()>;
	/// Inject storage data into the database replacing any existing data.
	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> error::Result<()>;
}

/// Client backend. Manages the data layer.
///
/// Note on state pruning: while an object from `state_at` is alive, the state
/// should not be pruned. The backend should internally reference-count
/// its state objects.
///
/// The same applies for live `BlockImportOperation`s: while an import operation building on a parent `P`
/// is alive, the state for `P` should not be pruned.
pub trait Backend {
	/// Associated block insertion operation type.
	type BlockImportOperation: BlockImportOperation;
	/// Associated blockchain backend type.
	type Blockchain: ::blockchain::Backend;
	/// Associated state backend type.
	type State: StateBackend;

	/// Begin a new block insertion transaction with given parent block id.
	/// When constructing the genesis, this is called with all-zero hash.
	fn begin_operation(&self, block: BlockId) -> error::Result<Self::BlockImportOperation>;
	/// Commit block insertion.
	fn commit_operation(&self, transaction: Self::BlockImportOperation) -> error::Result<()>;
	/// Returns reference to blockchain backend.
	fn blockchain(&self) -> &Self::Blockchain;
	/// Returns state backend with post-state of given block.
	fn state_at(&self, block: BlockId) -> error::Result<Self::State>;
}
