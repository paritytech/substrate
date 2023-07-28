// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Authoring RPC module errors.

use jsonrpsee::{
	core::Error as JsonRpseeError,
	types::error::{CallError, ErrorObject},
};
use sp_runtime::transaction_validity::InvalidTransaction;

/// Author RPC Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Author RPC errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Client error.
	#[error("Client error: {}", .0)]
	Client(Box<dyn std::error::Error + Send + Sync>),
	/// Transaction pool error,
	#[error("Transaction pool error: {}", .0)]
	Pool(#[from] sc_transaction_pool_api::error::Error),
	/// Verification error
	#[error("Extrinsic verification error: {}", .0)]
	Verification(Box<dyn std::error::Error + Send + Sync>),
	/// Incorrect extrinsic format.
	#[error("Invalid extrinsic format: {}", .0)]
	BadFormat(#[from] codec::Error),
	/// Key type ID has an unknown format.
	#[error("Invalid key type ID format (should be of length four)")]
	BadKeyType,
	/// Some random issue with the key store. Shouldn't happen.
	#[error("The key store is unavailable")]
	KeystoreUnavailable,
	/// Invalid session keys encoding.
	#[error("Session keys are not encoded correctly")]
	InvalidSessionKeys,
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base code for all authorship errors.
const BASE_ERROR: i32 = crate::error::base::AUTHOR;
/// Extrinsic has an invalid format.
const BAD_FORMAT: i32 = BASE_ERROR + 1;
/// Error during transaction verification in runtime.
const VERIFICATION_ERROR: i32 = BASE_ERROR + 2;

/// Pool rejected the transaction as invalid
const POOL_INVALID_TX: i32 = BASE_ERROR + 10;
/// Cannot determine transaction validity.
const POOL_UNKNOWN_VALIDITY: i32 = POOL_INVALID_TX + 1;
/// The transaction is temporarily banned.
const POOL_TEMPORARILY_BANNED: i32 = POOL_INVALID_TX + 2;
/// The transaction is already in the pool
const POOL_ALREADY_IMPORTED: i32 = POOL_INVALID_TX + 3;
/// Transaction has too low priority to replace existing one in the pool.
const POOL_TOO_LOW_PRIORITY: i32 = POOL_INVALID_TX + 4;
/// Including this transaction would cause a dependency cycle.
const POOL_CYCLE_DETECTED: i32 = POOL_INVALID_TX + 5;
/// The transaction was not included to the pool because of the limits.
const POOL_IMMEDIATELY_DROPPED: i32 = POOL_INVALID_TX + 6;
/// The transaction was not included to the pool since it is unactionable,
/// it is not propagable and the local node does not author blocks.
const POOL_UNACTIONABLE: i32 = POOL_INVALID_TX + 8;
/// Transaction does not provide any tags, so the pool can't identify it.
const POOL_NO_TAGS: i32 = POOL_INVALID_TX + 9;
/// Invalid block ID.
const POOL_INVALID_BLOCK_ID: i32 = POOL_INVALID_TX + 10;
/// The pool is not accepting future transactions.
const POOL_FUTURE_TX: i32 = POOL_INVALID_TX + 11;

impl From<Error> for JsonRpseeError {
	fn from(e: Error) -> Self {
		use sc_transaction_pool_api::error::Error as PoolError;

		match e {
			Error::BadFormat(e) => CallError::Custom(ErrorObject::owned(
				BAD_FORMAT,
				format!("Extrinsic has invalid format: {}", e),
				None::<()>,
			)),
			Error::Verification(e) => CallError::Custom(ErrorObject::owned(
				VERIFICATION_ERROR,
				format!("Verification Error: {}", e),
				Some(format!("{:?}", e)),
			)),
			Error::Pool(PoolError::InvalidTransaction(InvalidTransaction::Custom(e))) => {
				CallError::Custom(ErrorObject::owned(
					POOL_INVALID_TX,
					"Invalid Transaction",
					Some(format!("Custom error: {}", e)),
				))
			},
			Error::Pool(PoolError::InvalidTransaction(e)) => {
				let msg: &str = e.into();
				CallError::Custom(ErrorObject::owned(
					POOL_INVALID_TX,
					"Invalid Transaction",
					Some(msg),
				))
			},
			Error::Pool(PoolError::UnknownTransaction(e)) => {
				CallError::Custom(ErrorObject::owned(
					POOL_UNKNOWN_VALIDITY,
					"Unknown Transaction Validity",
					Some(format!("{:?}", e)),
				))
			},
			Error::Pool(PoolError::TemporarilyBanned) =>
				CallError::Custom(ErrorObject::owned(
				POOL_TEMPORARILY_BANNED,
				"Transaction is temporarily banned",
				None::<()>,
			)),
			Error::Pool(PoolError::AlreadyImported(hash)) =>
				CallError::Custom(ErrorObject::owned(
				POOL_ALREADY_IMPORTED,
				"Transaction Already Imported",
				Some(format!("{:?}", hash)),
			)),
			Error::Pool(PoolError::TooLowPriority { old, new }) => CallError::Custom(ErrorObject::owned(
				POOL_TOO_LOW_PRIORITY,
				format!("Priority is too low: ({} vs {})", old, new),
				Some("The transaction has too low priority to replace another transaction already in the pool.")
			)),
			Error::Pool(PoolError::CycleDetected) =>
				CallError::Custom(ErrorObject::owned(
				POOL_CYCLE_DETECTED,
				"Cycle Detected",
				None::<()>
			)),
			Error::Pool(PoolError::ImmediatelyDropped) => CallError::Custom(ErrorObject::owned(
				POOL_IMMEDIATELY_DROPPED,
				"Immediately Dropped",
				Some("The transaction couldn't enter the pool because of the limit"),
			)),
			Error::Pool(PoolError::Unactionable) => CallError::Custom(ErrorObject::owned(
				POOL_UNACTIONABLE,
				"Unactionable",
				Some("The transaction is unactionable since it is not propagable and \
				the local node does not author blocks")
			)),
			Error::Pool(PoolError::NoTagsProvided) => CallError::Custom(ErrorObject::owned(
				POOL_NO_TAGS,
				"No tags provided",
				Some("Transaction does not provide any tags, so the pool can't identify it")
			)),
			Error::Pool(PoolError::InvalidBlockId(_)) =>
				CallError::Custom(ErrorObject::owned(
				POOL_INVALID_BLOCK_ID,
				"The provided block ID is not valid",
				None::<()>
			)),
			Error::Pool(PoolError::RejectedFutureTransaction) => {
				CallError::Custom(ErrorObject::owned(
					POOL_FUTURE_TX,
					"The pool is not accepting future transactions",
					None::<()>,
				))
			},
			Error::UnsafeRpcCalled(e) => e.into(),
			e => CallError::Failed(e.into()),
		}.into()
	}
}
