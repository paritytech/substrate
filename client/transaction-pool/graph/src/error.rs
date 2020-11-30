// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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
	TransactionPriority as Priority, InvalidTransaction, UnknownTransaction,
};

/// Transaction pool result.
pub type Result<T> = std::result::Result<T, Error>;

/// Transaction pool error type.
#[derive(Debug, thiserror::Error, derive_more::From)]
#[allow(missing_docs)]
pub enum Error {
	/// Transaction is not verifiable yet, but might be in the future.
	#[error("Unknown transaction validity: {0:?}")]
	UnknownTransaction(UnknownTransaction),

	#[error("Invalid transaction validity: {0:?}")]
	InvalidTransaction(InvalidTransaction),
	/// The transaction validity returned no "provides" tag.
	///
	/// Such transactions are not accepted to the pool, since we use those tags
	/// to define identity of transactions (occupance of the same "slot").
	#[error("The transaction validity returned no `provides` tags, so the pool can't identify it.")]
	NoTagsProvided,

	#[error("Temporarily Banned")]
	TemporarilyBanned,

	#[error("[{0:?}] Transaction is already in the pool")]
	AlreadyImported(Box<dyn std::any::Any + Send>),

	#[error("Transaction cannot be imported due to too low priority ({0} > {1})", old, new)]
	TooLowPriority {
		/// Transaction already in the pool.
		old: Priority,
		/// Transaction entering the pool.
		new: Priority
	},

	#[error("Dependency cycle detected")]
	CycleDetected,

	#[error("Transaction couldn't enter the pool because of the limit.")]
	ImmediatelyDropped,

	#[error("Invlaid block id: {0}")]
	InvalidBlockId(String),
}

/// Transaction pool error conversion.
pub trait IntoPoolError: ::std::error::Error + Send + Sized {
	/// Try to extract original `Error`
	///
	/// This implementation is optional and used only to
	/// provide more descriptive error messages for end users
	/// of RPC API.
	fn into_pool_error(self) -> ::std::result::Result<Error, Self> { Err(self) }
}

impl IntoPoolError for Error {
	fn into_pool_error(self) -> ::std::result::Result<Error, Self> { Ok(self) }
}
