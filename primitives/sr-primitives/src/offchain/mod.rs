// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! A collection of higher lever helpers for offchain calls.

use crate::{
	traits,
	generic::BlockId,
};

pub mod http;

/// An abstraction for transaction pool.
///
/// This trait is used by offchain calls to be able to submit transactions.
/// The main use case is for offchain workers, to feed back the results of computations,
/// but since the transaction pool access is a separate `ExternalitiesExtension` it can
/// be also used in context of other offchain calls. For one may generate and submit
/// a transaction for some misbehavior reports (say equivocation).
pub trait TransactionPool<Block: traits::Block>: Send + Sync {
	/// Submit transaction.
	///
	/// The transaction will end up in the pool and be propagated to others.
	fn submit_at(
		&self,
		at: &BlockId<Block>,
		extrinsic: Block::Extrinsic,
	) -> Result<(), ()>;
}
