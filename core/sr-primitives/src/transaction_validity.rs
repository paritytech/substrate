// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
		/// A list of tags this transaction provides. Successfully importing the transaction
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
