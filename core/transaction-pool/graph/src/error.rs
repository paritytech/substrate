// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Transaction pool errors.

use sr_primitives::transaction_validity::TransactionPriority as Priority;
use error_chain::{
	error_chain, error_chain_processing, impl_error_chain_processed, impl_extract_backtrace, impl_error_chain_kind
};

error_chain! {
	errors {
		/// Transaction is not verifiable yet, but might be in the future.
		UnknownTransactionValidity(e: i8) {
			description("Runtime cannot determine validity of the transaction yet."),
			display("Unkown Transaction Validity. Error code: {}", e),
		}
		/// Transaction is invalid
		InvalidTransaction(e: i8) {
			description("Runtime check for the transaction failed."),
			display("Invalid Transaction. Error Code: {}", e),
		}
		/// The transaction is temporarily baned
		TemporarilyBanned {
			description("Transaction is temporarily banned from importing to the pool."),
			display("Temporarily Banned"),
		}
		/// The transaction is already in the pool.
		AlreadyImported(hash: Box<::std::any::Any + Send>) {
			description("Transaction is already in the pool"),
			display("[{:?}] Already imported", hash),
		}
		/// The transaction cannot be imported cause it's a replacement and has too low priority.
		TooLowPriority(old: Priority, new: Priority) {
			description("The priority is too low to replace transactions already in the pool."),
			display("Too low priority ({} > {})", old, new)
		}
		/// Deps cycle detected and we couldn't import transaction.
		CycleDetected {
			description("Transaction was not imported because of detected cycle."),
			display("Cycle Detected"),
		}
		/// Transaction was dropped immediately after it got inserted.
		ImmediatelyDropped {
			description("Transaction couldn't enter the pool because of the limit."),
			display("Immediately Dropped"),
		}
	}
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
