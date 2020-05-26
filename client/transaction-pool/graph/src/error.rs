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
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Transaction is not verifiable yet, but might be in the future.
	#[display(fmt="Unknown transaction validity: {:?}", _0)]
	UnknownTransaction(UnknownTransaction),
	/// Transaction is invalid.
	#[display(fmt="Invalid transaction validity: {:?}", _0)]
	InvalidTransaction(InvalidTransaction),
	/// The transaction validity returned no "provides" tag.
	///
	/// Such transactions are not accepted to the pool, since we use those tags
	/// to define identity of transactions (occupance of the same "slot").
	#[display(fmt="The transaction does not provide any tags, so the pool can't identify it.")]
	NoTagsProvided,
	/// The transaction is temporarily banned.
	#[display(fmt="Temporarily Banned")]
	TemporarilyBanned,
	/// The transaction is already in the pool.
	#[display(fmt="[{:?}] Already imported", _0)]
	AlreadyImported(Box<dyn std::any::Any + Send>),
	/// The transaction cannot be imported cause it's a replacement and has too low priority.
	#[display(fmt="Too low priority ({} > {})", old, new)]
	TooLowPriority {
		/// Transaction already in the pool.
		old: Priority,
		/// Transaction entering the pool.
		new: Priority
	},
	/// Deps cycle detected and we couldn't import transaction.
	#[display(fmt="Cycle Detected")]
	CycleDetected,
	/// Transaction was dropped immediately after it got inserted.
	#[display(fmt="Transaction couldn't enter the pool because of the limit.")]
	ImmediatelyDropped,
	/// Invalid block id.
	InvalidBlockId(String),
}

impl std::error::Error for Error {}

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
