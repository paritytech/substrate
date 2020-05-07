// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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
	/// The pool is not accepting future transactions.
	#[display(fmt="The pool is not accepting future transactions")]
	RejectedFutureTransaction,
}

impl std::error::Error for Error {}

/// Transaction pool error conversion.
pub trait IntoPoolError: std::error::Error + Send + Sized {
	/// Try to extract original `Error`
	///
	/// This implementation is optional and used only to
	/// provide more descriptive error messages for end users
	/// of RPC API.
	fn into_pool_error(self) -> std::result::Result<Error, Self> { Err(self) }
}

impl IntoPoolError for Error {
	fn into_pool_error(self) -> std::result::Result<Error, Self> { Ok(self) }
}
