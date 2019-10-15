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
use crate::RuntimeDebug;

/// Priority for a transaction. Additive. Higher is better.
pub type TransactionPriority = u64;

/// Minimum number of blocks a transaction will remain valid for.
/// `TransactionLongevity::max_value()` means "forever".
pub type TransactionLongevity = u64;

/// Tag for a transaction. No two transactions with the same tag should be placed on-chain.
pub type TransactionTag = Vec<u8>;

/// An invalid transaction validity.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(serde::Serialize))]
pub enum InvalidTransaction {
	/// The call of the transaction is not expected.
	Call,
	/// General error to do with the inability to pay some fees (e.g. account balance too low).
	Payment,
	/// General error to do with the transaction not yet being valid (e.g. nonce too high).
	Future,
	/// General error to do with the transaction being outdated (e.g. nonce too low).
	Stale,
	/// General error to do with the transaction's proofs (e.g. signature).
	BadProof,
	/// The transaction birth block is ancient.
	AncientBirthBlock,
	/// The transaction would exhaust the resources of current block.
	///
	/// The transaction might be valid, but there are not enough resources left in the current block.
	ExhaustsResources,
	/// Any other custom invalid validity that is not covered by this enum.
	Custom(u8),
}

impl InvalidTransaction {
	/// Returns if the reason for the invalidity was block resource exhaustion.
	pub fn exhausted_resources(&self) -> bool {
		match self {
			Self::ExhaustsResources => true,
			_ => false,
		}
	}
}

impl From<InvalidTransaction> for &'static str {
	fn from(invalid: InvalidTransaction) -> &'static str {
		match invalid {
			InvalidTransaction::Call => "Transaction call is not expected",
			InvalidTransaction::Future => "Transaction will be valid in the future",
			InvalidTransaction::Stale => "Transaction is outdated",
			InvalidTransaction::BadProof => "Transaction has a bad signature",
			InvalidTransaction::AncientBirthBlock => "Transaction has an ancient birth block",
			InvalidTransaction::ExhaustsResources =>
				"Transaction would exhausts the block limits",
			InvalidTransaction::Payment =>
				"Inability to pay some fees (e.g. account balance too low)",
			InvalidTransaction::Custom(_) => "InvalidTransaction custom error",
		}
	}
}

/// An unknown transaction validity.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(serde::Serialize))]
pub enum UnknownTransaction {
	/// Could not lookup some information that is required to validate the transaction.
	CannotLookup,
	/// No validator found for the given unsigned transaction.
	NoUnsignedValidator,
	/// Any other custom unknown validity that is not covered by this enum.
	Custom(u8),
}

impl From<UnknownTransaction> for &'static str {
	fn from(unknown: UnknownTransaction) -> &'static str {
		match unknown {
			UnknownTransaction::CannotLookup =>
				"Could not lookup information required to validate the transaction",
			UnknownTransaction::NoUnsignedValidator =>
				"Could not find an unsigned validator for the unsigned transaction",
			UnknownTransaction::Custom(_) => "UnknownTransaction custom error",
		}
	}
}

/// Errors that can occur while checking the validity of a transaction.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(serde::Serialize))]
pub enum TransactionValidityError {
	/// The transaction is invalid.
	Invalid(InvalidTransaction),
	/// Transaction validity can't be determined.
	Unknown(UnknownTransaction),
}

impl TransactionValidityError {
	/// Returns `true` if the reason for the error was block resource exhaustion.
	pub fn exhausted_resources(&self) -> bool {
		match self {
			Self::Invalid(e) => e.exhausted_resources(),
			Self::Unknown(_) => false,
		}
	}
}

impl From<TransactionValidityError> for &'static str {
	fn from(err: TransactionValidityError) -> &'static str {
		match err {
			TransactionValidityError::Invalid(invalid) => invalid.into(),
			TransactionValidityError::Unknown(unknown) => unknown.into(),
		}
	}
}

impl From<InvalidTransaction> for TransactionValidityError {
	fn from(err: InvalidTransaction) -> Self {
		TransactionValidityError::Invalid(err)
	}
}

impl From<UnknownTransaction> for TransactionValidityError {
	fn from(err: UnknownTransaction) -> Self {
		TransactionValidityError::Unknown(err)
	}
}

impl From<InvalidTransaction> for crate::ApplyError {
	fn from(invalid: InvalidTransaction) -> crate::ApplyError {
		TransactionValidityError::from(invalid).into()
	}
}

impl From<UnknownTransaction> for crate::ApplyError {
	fn from(unknown: UnknownTransaction) -> crate::ApplyError {
		TransactionValidityError::from(unknown).into()
	}
}

/// Information on a transaction's validity and, if valid, on how it relates to other transactions.
pub type TransactionValidity = Result<ValidTransaction, TransactionValidityError>;

impl Into<TransactionValidity> for InvalidTransaction {
	fn into(self) -> TransactionValidity {
		Err(self.into())
	}
}

impl Into<TransactionValidity> for UnknownTransaction {
	fn into(self) -> TransactionValidity {
		Err(self.into())
	}
}

/// Information concerning a valid transaction.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
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
	fn should_encode_and_decode() {
		let v: TransactionValidity = Ok(ValidTransaction {
			priority: 5,
			requires: vec![vec![1, 2, 3, 4]],
			provides: vec![vec![4, 5, 6]],
			longevity: 42,
			propagate: false,
		});

		let encoded = v.encode();
		assert_eq!(
			encoded,
			vec![0, 5, 0, 0, 0, 0, 0, 0, 0, 4, 16, 1, 2, 3, 4, 4, 12, 4, 5, 6, 42, 0, 0, 0, 0, 0, 0, 0, 0]
		);

		// decode back
		assert_eq!(TransactionValidity::decode(&mut &*encoded), Ok(v));
	}
}
