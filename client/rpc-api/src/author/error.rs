// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use jsonrpsee::types::{
	error::{CallError, Error as JsonRpseeError},
	to_json_raw_value, JsonRawValue,
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
	/// Incorrect seed phrase.
	#[error("Invalid seed phrase/SURI")]
	BadSeedPhrase,
	/// Key type ID has an unknown format.
	#[error("Invalid key type ID format (should be of length four)")]
	BadKeyType,
	/// Key type ID has some unsupported crypto.
	#[error("The crypto of key type ID is unknown")]
	UnsupportedKeyType,
	/// Some random issue with the key store. Shouldn't happen.
	#[error("The key store is unavailable")]
	KeyStoreUnavailable,
	/// Invalid session keys encoding.
	#[error("Session keys are not encoded correctly")]
	InvalidSessionKeys,
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] crate::policy::UnsafeRpcError),
}

/// Base code for all authorship errors.
const BASE_ERROR: i32 = 1000;
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
/// The key type crypto is not known.
const UNSUPPORTED_KEY_TYPE: i32 = POOL_INVALID_TX + 7;
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
			Error::BadFormat(e) => CallError::Custom {
				code: BAD_FORMAT,
				message: format!("Extrinsic has invalid format: {}", e).into(),
				data: None,
			}.into(),
			Error::Verification(e) => CallError::Custom {
				code: VERIFICATION_ERROR,
				message: format!("Verification Error: {}", e).into(),
				data: JsonRawValue::from_string(format!("\"{:?}\"", e)).ok(),
			}.into(),
			Error::Pool(PoolError::InvalidTransaction(InvalidTransaction::Custom(e))) => CallError::Custom {
				code: POOL_INVALID_TX,
				message: "Invalid Transaction".into(),
				data: JsonRawValue::from_string(format!("\"Custom error: {}\"", e)).ok(),
			}.into(),
			Error::Pool(PoolError::InvalidTransaction(e)) => {
				CallError::Custom {
					code: POOL_INVALID_TX,
					message: "Invalid Transaction".into(),
					data: to_json_raw_value(&e).ok(),
				}
			}.into(),
			Error::Pool(PoolError::UnknownTransaction(e)) => CallError::Custom {
				code: POOL_UNKNOWN_VALIDITY,
				message: "Unknown Transaction Validity".into(),
				data: to_json_raw_value(&e).ok(),
			}.into(),
			Error::Pool(PoolError::TemporarilyBanned) => CallError::Custom {
				code: (POOL_TEMPORARILY_BANNED),
				message: "Transaction is temporarily banned".into(),
				data: None,
			}.into(),
			Error::Pool(PoolError::AlreadyImported(hash)) => CallError::Custom {
				code: (POOL_ALREADY_IMPORTED),
				message: "Transaction Already Imported".into(),
				data: JsonRawValue::from_string(format!("\"{:?}\"", hash)).ok(),
			}.into(),
			Error::Pool(PoolError::TooLowPriority { old, new }) => CallError::Custom {
				code: (POOL_TOO_LOW_PRIORITY),
				message: format!("Priority is too low: ({} vs {})", old, new),
				data: to_json_raw_value(&"The transaction has too low priority to replace another transaction already in the pool.").ok(),
			}.into(),
			Error::Pool(PoolError::CycleDetected) => CallError::Custom {
				code: (POOL_CYCLE_DETECTED),
				message: "Cycle Detected".into(),
				data: None,
			}.into(),
			Error::Pool(PoolError::ImmediatelyDropped) => CallError::Custom {
				code: (POOL_IMMEDIATELY_DROPPED),
				message: "Immediately Dropped".into(),
				data: to_json_raw_value(&"The transaction couldn't enter the pool because of the limit").ok(),
			}.into(),
			Error::Pool(PoolError::Unactionable) => CallError::Custom {
				code: (POOL_UNACTIONABLE),
				message: "Unactionable".into(),
				data: to_json_raw_value(
					&"The transaction is unactionable since it is not propagable and \
					 the local node does not author blocks"
				).ok(),
			}.into(),
			Error::Pool(PoolError::NoTagsProvided) => CallError::Custom {
				code: (POOL_NO_TAGS),
				message: "No tags provided".into(),
				data: to_json_raw_value(
					&"Transaction does not provide any tags, so the pool can't identify it"
				).ok(),
			}.into(),
			Error::Pool(PoolError::InvalidBlockId(_)) => CallError::Custom {
				code: (POOL_INVALID_BLOCK_ID),
				message: "The provided block ID is not valid".into(),
				data: None,
			}.into(),
			Error::Pool(PoolError::RejectedFutureTransaction) => CallError::Custom {
				code: (POOL_FUTURE_TX),
				message: "The pool is not accepting future transactions".into(),
				data: None,
			}.into(),
			Error::UnsupportedKeyType => CallError::Custom {
				code: UNSUPPORTED_KEY_TYPE,
				message: "Unknown key type crypto" .into(),
				data: to_json_raw_value(
					&"The crypto for the given key type is unknown, please add the public key to the \
					request to insert the key successfully."
				).ok(),
			}.into(),
			Error::UnsafeRpcCalled(e) => e.into(),
			Error::Client(e) => CallError::Failed(anyhow::anyhow!(e)).into(),
			Error::BadSeedPhrase | Error::BadKeyType => CallError::InvalidParams(e.into()).into(),
			Error::InvalidSessionKeys | Error::KeyStoreUnavailable => CallError::Failed(e.into()).into(),
		}
	}
}
