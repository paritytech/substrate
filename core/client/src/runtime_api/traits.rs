// Copyright 2018 Parity Technologies (UK) Ltd.
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

use primitives::OpaqueMetadata;
use runtime_primitives::{
	traits::{Block as BlockT},
	transaction_validity::TransactionValidity
};

decl_runtime_apis! {
	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		/// Returns the metadata of a runtime.
		fn metadata() -> OpaqueMetadata;
	}

	/// The `TaggedTransactionQueue` api trait for interfering with the new transaction queue.
	pub trait TaggedTransactionQueue<Block: BlockT> {
		/// Validate the given transaction.
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;
	}
}
