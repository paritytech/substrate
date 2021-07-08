// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tagged Transaction Queue Runtime API.

use sp_runtime::transaction_validity::{TransactionValidity, TransactionSource};
use sp_runtime::traits::Block as BlockT;

sp_api::decl_runtime_apis! {
	/// The `TaggedTransactionQueue` api trait for interfering with the transaction queue.
	#[api_version(3)]
	pub trait TaggedTransactionQueue {
		/// Validate the transaction.
		#[changed_in(2)]
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;

		/// Validate the transaction.
		#[changed_in(3)]
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
		) -> TransactionValidity;

		/// Validate the transaction.
		///
		/// This method is invoked by the transaction pool to learn details about given transaction.
		/// The implementation should make sure to verify the correctness of the transaction
		/// against current state. The given `block_hash` corresponds to the hash of the block
		/// that is used as current state.
		///
		/// Note that this call may be performed by the pool multiple times and transactions
		/// might be verified in any possible order.
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
			block_hash: Block::Hash,
		) -> TransactionValidity;
	}
}
