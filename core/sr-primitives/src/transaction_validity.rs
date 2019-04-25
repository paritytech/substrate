// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Transaction validity interface.

use rstd::prelude::*;
use crate::codec::{Encode, Decode};

/// Priority for a transaction. Additive. Higher is better.
pub type TransactionPriority = u64;

/// Minimum number of blocks a transaction will remain valid for.
/// `TransactionLongevity::max_value()` means "forever".
pub type TransactionLongevity = u64;

/// Tag for a transaction. No two transactions with the same tag should be placed on-chain.
pub type TransactionTag = Vec<u8>;

/// Information on a transaction's validity and, if valid, on how it relates to other transactions.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum TransactionValidity {
	/// Transaction is invalid. Details are described by the error code.
	Invalid(i8),
	/// Transaction is valid.
	Valid {
		/// Priority of the transaction.
		///
		/// Priority determines the ordering of two transactions that have all
		/// their dependencies (required tags) satisfied.
		priority: TransactionPriority,
		/// Transaction dependencies
		///
		/// A non-empty list signifies that some other transactions which provide
		/// given tags are required to be included before that one.
		requires: Vec<TransactionTag>,
		/// Provided tags
		///
		/// A list of tags this transaction provides. Successfuly importing the transaction
		/// will enable other transactions that depend on (require) those tags to be included as well.
		/// Provided and requried tags allow Substrate to build a dependency graph of transactions
		/// and import them in the right (linear) order.
		provides: Vec<TransactionTag>,
		/// Transaction longevity
		///
		/// Longevity describes minimum number of blocks the validity is correct.
		/// After this period transaction should be removed from the pool or revalidated.
		longevity: TransactionLongevity,
	},
	/// Transaction validity can't be determined.
	Unknown(i8),
}
