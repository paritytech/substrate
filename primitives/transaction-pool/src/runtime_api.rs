// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Tagged Transaction Queue Runtime API.

use sp_runtime::transaction_validity::{TransactionValidity, TransactionSource};
use sp_runtime::traits::Block as BlockT;

sp_api::decl_runtime_apis! {
	/// The `TaggedTransactionQueue` api trait for interfering with the transaction queue.
	#[api_version(2)]
	pub trait TaggedTransactionQueue {
		/// Validate the transaction.
		#[changed_in(2)]
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;

		/// Validate the transaction.
		///
		/// This method is invoked by the transaction pool to learn details about given transaction.
		/// The implementation should make sure to verify the correctness of the transaction
		/// against current state.
		/// Note that this call may be performed by the pool multiple times and transactions
		/// might be verified in any possible order.
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
		) -> TransactionValidity;
	}
}
