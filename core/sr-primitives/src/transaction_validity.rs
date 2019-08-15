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

/// An invalid transaction validity.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy)]
#[cfg_attr(feature = "std", derive(Debug, serde::Serialize))]
pub enum InvalidTransactionValidity {
	/// General error to do with the transaction not yet being valid (e.g. nonce too high).
	Future,
	/// General error to do with the transaction being outdated (e.g. nonce too low).
	Stale,
	/// General error to do with the transaction's proofs (e.g. signature).
	BadProof,
	/// The transaction birth block is ancient.
	AncientBirthBlock,
	/// The transaction **alone** would exhaust the resources of a block.
	ExhaustResources,
	/// Any other custom invalid validity that is not covered by this enum.
	Custom(u8),
}

/// An unknown transaction validity.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy)]
#[cfg_attr(feature = "std", derive(Debug, serde::Serialize))]
pub enum UnknownTransactionValidity {
	/// An invalid/unknown account index
	InvalidIndex,
	/// No validator found for the given unsigned transaction.
	NoUnsignedValidator,
	/// Any other custom unknown validity that is not covered by this enum.
	Custom(u8),
}

/// The error that can occur while checking the validity of a transaction.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy)]
#[cfg_attr(feature = "std", derive(Debug, serde::Serialize))]
pub enum TransactionValidityError {
	/// The transaction is invalid.
	Invalid(InvalidTransactionValidity),
	/// Transaction validity can't be determined.
	Unknown(UnknownTransactionValidity),
}

impl Into<TransactionValidityError> for InvalidTransactionValidity {
	fn into(self) -> TransactionValidityError {
		TransactionValidityError::Invalid(self)
	}
}

impl Into<TransactionValidityError> for UnknownTransactionValidity {
	fn into(self) -> TransactionValidityError {
		TransactionValidityError::Unknown(self)
	}
}

impl Into<crate::ApplyError> for InvalidTransactionValidity {
	fn into(self) -> crate::ApplyError {
		TransactionValidityError::from(self.into()).into()
	}
}

impl Into<crate::ApplyError> for UnknownTransactionValidity {
	fn into(self) -> crate::ApplyError {
		TransactionValidityError::from(self.into()).into()
	}
}

/// Information on a transaction's validity and, if valid, on how it relates to other transactions.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum TransactionValidity {
	/// Transaction is invalid.
	Invalid(InvalidTransactionValidity),
	/// Transaction is valid.
	Valid(ValidTransaction),
	/// Transaction validity can't be determined.
	Unknown(UnknownTransactionValidity),
}

impl Into<TransactionValidity> for TransactionValidityError {
	fn into(self) -> TransactionValidity {
		match self {
			TransactionValidityError::Invalid(invalid) => TransactionValidity::Invalid(invalid),
			TransactionValidityError::Unknown(unknown) => TransactionValidity::Unknown(unknown),
		}
	}
}

impl Into<TransactionValidity> for InvalidTransactionValidity {
	fn into(self) -> TransactionValidity {
		TransactionValidity::Invalid(self)
	}
}

impl Into<TransactionValidity> for UnknownTransactionValidity {
	fn into(self) -> TransactionValidity {
		TransactionValidity::Unknown(self)
	}
}

impl Into<TransactionValidity> for ValidTransaction {
	fn into(self) -> TransactionValidity {
		TransactionValidity::Valid(self)
	}
}

impl TransactionValidity {
	/// Combine two `TransactionValidity`s.
	///
	/// If both are valid, they are combined.
	///
	/// If one of them is not valid, the non-valid one is returned. If both are not valid, `self` is
	/// returned.
	pub fn combine_with<F: FnOnce() -> Self>(self, other: F) -> Self {
		match self {
			TransactionValidity::Valid(valid) => {
				match other() {
					TransactionValidity::Valid(other_valid) => {
						TransactionValidity::Valid(valid.combine_with(other_valid))
					},
					o => o,
				}
			},
			_ => self,
		}
	}

	/// Convert this `TransactionValidity` into a `Result`.
	pub fn into_result(self) -> Result<ValidTransaction, TransactionValidityError> {
		match self {
			TransactionValidity::Valid(valid) => Ok(valid),
			TransactionValidity::Invalid(invalid) => Err(invalid.into()),
			TransactionValidity::Unknown(unknown) => Err(unknown.into()),
		}
	}
}

/// Information concerning a valid transaction.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidTransaction {
	/// Priority of the transaction.
	///
	/// Priority determines the ordering of two transactions that have all
	/// their dependencies (required tags) satisfied.
	pub priority: TransactionPriority,
	/// Transaction dependencies
	///
	/// A non-empty list signifies that some other transactions which provide
	/// given tags are required to be included before that one.
	pub requires: Vec<TransactionTag>,
	/// Provided tags
	///
	/// A list of tags this transaction provides. Successfully importing the transaction
	/// will enable other transactions that depend on (require) those tags to be included as well.
	/// Provided and required tags allow Substrate to build a dependency graph of transactions
	/// and import them in the right (linear) order.
	pub provides: Vec<TransactionTag>,
	/// Transaction longevity
	///
	/// Longevity describes minimum number of blocks the validity is correct.
	/// After this period transaction should be removed from the pool or revalidated.
	pub longevity: TransactionLongevity,
	/// A flag indicating if the transaction should be propagated to other peers.
	///
	/// By setting `false` here the transaction will still be considered for
	/// including in blocks that are authored on the current node, but will
	/// never be sent to other peers.
	pub propagate: bool,
}

impl Default for ValidTransaction {
	fn default() -> Self {
		ValidTransaction {
			priority: 0,
			requires: vec![],
			provides: vec![],
			longevity: TransactionLongevity::max_value(),
			propagate: true,
		}
	}
}

impl ValidTransaction {
	/// Combine two instances into one, as a best effort. This will take the superset of each of the
	/// `provides` and `requires` tags, it will sum the priorities, take the minimum longevity and
	/// the logic *And* of the propagate flags.
	pub fn combine_with(mut self, mut other: ValidTransaction) -> Self {
		ValidTransaction {
			priority: self.priority.saturating_add(other.priority),
			requires: { self.requires.append(&mut other.requires); self.requires },
			provides: { self.provides.append(&mut other.provides); self.provides },
			longevity: self.longevity.min(other.longevity),
			propagate: self.propagate && other.propagate,
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

		assert_eq!(TransactionValidity::decode(&mut &*old_encoding), Ok(TransactionValidity::Valid(ValidTransaction {
			priority: 5,
			requires: vec![vec![1, 2, 3, 4]],
			provides: vec![vec![4, 5, 6]],
			longevity: 42,
			propagate: true,
		})));
	}

	#[test]
	fn should_encode_and_decode() {
		let v = TransactionValidity::Valid(ValidTransaction {
			priority: 5,
			requires: vec![vec![1, 2, 3, 4]],
			provides: vec![vec![4, 5, 6]],
			longevity: 42,
			propagate: false,
		});

		let encoded = v.encode();
		assert_eq!(
			encoded,
			vec![1, 5, 0, 0, 0, 0, 0, 0, 0, 4, 16, 1, 2, 3, 4, 4, 12, 4, 5, 6, 42, 0, 0, 0, 0, 0, 0, 0, 0]
		);

		// decode back
		assert_eq!(TransactionValidity::decode(&mut &*encoded), Ok(v));
	}
}
