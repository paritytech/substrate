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
#[derive(Clone, PartialEq, Eq, Encode)]
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
		/// Provided and required tags allow Substrate to build a dependency graph of transactions
		/// and import them in the right (linear) order.
		provides: Vec<TransactionTag>,
		/// Transaction longevity
		///
		/// Longevity describes minimum number of blocks the validity is correct.
		/// After this period transaction should be removed from the pool or revalidated.
		longevity: TransactionLongevity,
		/// A flag indicating if the transaction should be propagated to other peers.
		///
		/// By setting `false` here the transaction will still be considered for
		/// including in blocks that are authored on the current node, but will
		/// never be sent to other peers.
		propagate: bool,
	},
	/// Transaction validity can't be determined.
	Unknown(i8),
}

impl Decode for TransactionValidity {
	fn decode<I: crate::codec::Input>(value: &mut I) -> Option<Self> {
		match value.read_byte()? {
			0 => Some(TransactionValidity::Invalid(i8::decode(value)?)),
			1 => {
				let priority = TransactionPriority::decode(value)?;
				let requires = Vec::decode(value)?;
				let provides = Vec::decode(value)?;
				let longevity = TransactionLongevity::decode(value)?;
				let propagate = bool::decode(value).unwrap_or(true);

				Some(TransactionValidity::Valid {
					priority, requires, provides, longevity, propagate,
				})
			},
			2 => Some(TransactionValidity::Unknown(i8::decode(value)?)),
			_ => None,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_decode_with_backward_compat() {
		let old_encoding = vec![
			1, 5, 0, 0, 0, 0, 0, 0, 0, 4, 16, 1, 2, 3, 4, 4, 12, 4, 5, 6, 42, 0, 0, 0, 0, 0, 0, 0
		];

		assert_eq!(TransactionValidity::decode(&mut &*old_encoding), Some(TransactionValidity::Valid {
			priority: 5,
			requires: vec![vec![1, 2, 3, 4]],
			provides: vec![vec![4, 5, 6]],
			longevity: 42,
			propagate: true,
		}));
	}

	#[test]
	fn should_encode_and_decode() {
		let v = TransactionValidity::Valid {
			priority: 5,
			requires: vec![vec![1, 2, 3, 4]],
			provides: vec![vec![4, 5, 6]],
			longevity: 42,
			propagate: false,
		};

		let encoded = v.encode();
		assert_eq!(
			encoded,
			vec![1, 5, 0, 0, 0, 0, 0, 0, 0, 4, 16, 1, 2, 3, 4, 4, 12, 4, 5, 6, 42, 0, 0, 0, 0, 0, 0, 0, 0]
		);

		// decode back
		assert_eq!(TransactionValidity::decode(&mut &*encoded), Some(v));
	}
}
