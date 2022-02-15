// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Transaction pool errors.

use sp_runtime::transaction_validity::{
	InvalidTransaction, TransactionPriority as Priority, UnknownTransaction,
};

/// Transaction pool result.
pub type Result<T> = std::result::Result<T, Error>;

/// Transaction pool error type.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error("Unknown transaction validity: {0:?}")]
	UnknownTransaction(UnknownTransaction),

	#[error("Invalid transaction validity: {0:?}")]
	InvalidTransaction(InvalidTransaction),

	/// The transaction validity returned no "provides" tag.
	///
	/// Such transactions are not accepted to the pool, since we use those tags
	/// to define identity of transactions (occupance of the same "slot").
	#[error("Transaction does not provide any tags, so the pool can't identify it")]
	NoTagsProvided,

	#[error("Transaction temporarily Banned")]
	TemporarilyBanned,

	#[error("[{0:?}] Already imported")]
	AlreadyImported(Box<dyn std::any::Any + Send>),

	#[error("Too low priority ({} > {})", old, new)]
	TooLowPriority {
		/// Transaction already in the pool.
		old: Priority,
		/// Transaction entering the pool.
		new: Priority,
	},
	#[error("Transaction with cyclic dependency")]
	CycleDetected,

	#[error("Transaction couldn't enter the pool because of the limit")]
	ImmediatelyDropped,

	#[error("Transaction cannot be propagated and the local node does not author blocks")]
	Unactionable,

	#[error("{0}")]
	InvalidBlockId(String),

	#[error("The pool is not accepting future transactions")]
	RejectedFutureTransaction,
}

/// Transaction pool error conversion.
pub trait IntoPoolError: std::error::Error + Send + Sized {
	/// Try to extract original `Error`
	///
	/// This implementation is optional and used only to
	/// provide more descriptive error messages for end users
	/// of RPC API.
	fn into_pool_error(self) -> std::result::Result<Error, Self> {
		Err(self)
	}
}

impl IntoPoolError for Error {
	fn into_pool_error(self) -> std::result::Result<Error, Self> {
		Ok(self)
	}
}
