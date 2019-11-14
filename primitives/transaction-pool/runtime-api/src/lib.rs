// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Substrate runtime api for the transaction queue.

#![cfg_attr(not(feature = "std"), no_std)]

use sr_primitives::{transaction_validity::TransactionValidity, traits::Block as BlockT};

sr_api::decl_runtime_apis! {
	/// The `TaggedTransactionQueue` api trait for interfering with the transaction queue.
	pub trait TaggedTransactionQueue {
		/// Validate the given transaction.
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;
	}
}
