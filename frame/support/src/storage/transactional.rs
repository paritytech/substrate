// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Provides functionality around the transaction storage.
//!
//! Transactional storage provides functionality to run an entire code block
//! in a storage transaction. This means that either the entire changes to the
//! storage are committed or everything is thrown away. This simplifies the
//! writing of functionality that may bail at any point of operation. Otherwise
//! you would need to first verify all storage accesses and then do the storage
//! modifications.
//!
//! [`with_transaction`] provides a way to run a given closure in a transactional context.

use sp_io::storage::{commit_transaction, rollback_transaction, start_transaction};
use sp_runtime::{DispatchError, TransactionOutcome, TransactionalError};

/// The type that is being used to store the current number of active layers.
pub type Layer = u32;
/// The key that is holds the current number of active layers.
pub const TRANSACTION_LEVEL_KEY: &[u8] = b":transaction_level:";
/// The maximum number of nested layers.
pub const TRANSACTIONAL_LIMIT: Layer = 255;

/// Returns the current number of nested transactional layers.
fn get_transaction_level() -> Layer {
	crate::storage::unhashed::get_or_default::<Layer>(TRANSACTION_LEVEL_KEY)
}

/// Set the current number of nested transactional layers.
fn set_transaction_level(level: Layer) {
	crate::storage::unhashed::put::<Layer>(TRANSACTION_LEVEL_KEY, &level);
}

/// Kill the transactional layers storage.
fn kill_transaction_level() {
	crate::storage::unhashed::kill(TRANSACTION_LEVEL_KEY);
}

/// Increments the transaction level. Returns an error if levels go past the limit.
///
/// Returns a guard that when dropped decrements the transaction level automatically.
fn inc_transaction_level() -> Result<StorageLayerGuard, ()> {
	let existing_levels = get_transaction_level();
	if existing_levels >= TRANSACTIONAL_LIMIT {
		return Err(())
	}
	// Cannot overflow because of check above.
	set_transaction_level(existing_levels + 1);
	Ok(StorageLayerGuard)
}

fn dec_transaction_level() {
	let existing_levels = get_transaction_level();
	if existing_levels == 0 {
		log::warn!(
				"We are underflowing with calculating transactional levels. Not great, but let's not panic...",
			);
	} else if existing_levels == 1 {
		// Don't leave any trace of this storage item.
		kill_transaction_level();
	} else {
		// Cannot underflow because of checks above.
		set_transaction_level(existing_levels - 1);
	}
}

struct StorageLayerGuard;

impl Drop for StorageLayerGuard {
	fn drop(&mut self) {
		dec_transaction_level()
	}
}

/// Check if the current call is within a transactional layer.
pub fn is_transactional() -> bool {
	get_transaction_level() > 0
}

/// Execute the supplied function in a new storage transaction.
///
/// All changes to storage performed by the supplied function are discarded if the returned
/// outcome is `TransactionOutcome::Rollback`.
///
/// Transactions can be nested up to `TRANSACTIONAL_LIMIT` times; more than that will result in an
/// error.
///
/// Commits happen to the parent transaction.
pub fn with_transaction<T, E, F>(f: F) -> Result<T, E>
where
	E: From<DispatchError>,
	F: FnOnce() -> TransactionOutcome<Result<T, E>>,
{
	// This needs to happen before `start_transaction` below.
	// Otherwise we may rollback the increase, then decrease as the guard goes out of scope
	// and then end in some bad state.
	let _guard = inc_transaction_level().map_err(|()| TransactionalError::LimitReached.into())?;

	start_transaction();

	match f() {
		TransactionOutcome::Commit(res) => {
			commit_transaction();
			res
		},
		TransactionOutcome::Rollback(res) => {
			rollback_transaction();
			res
		},
	}
}

/// Same as [`with_transaction`] but without a limit check on nested transactional layers.
///
/// This is mostly for backwards compatibility before there was a transactional layer limit.
/// It is recommended to only use [`with_transaction`] to avoid users from generating too many
/// transactional layers.
pub fn with_transaction_unchecked<R, F>(f: F) -> R
where
	F: FnOnce() -> TransactionOutcome<R>,
{
	// This needs to happen before `start_transaction` below.
	// Otherwise we may rollback the increase, then decrease as the guard goes out of scope
	// and then end in some bad state.
	let maybe_guard = inc_transaction_level();

	if maybe_guard.is_err() {
		log::warn!(
			"The transactional layer limit has been reached, and new transactional layers are being
			spawned with `with_transaction_unchecked`. This could be caused by someone trying to
			attack your chain, and you should investigate usage of `with_transaction_unchecked` and
			potentially migrate to `with_transaction`, which enforces a transactional limit.",
		);
	}

	start_transaction();

	match f() {
		TransactionOutcome::Commit(res) => {
			commit_transaction();
			res
		},
		TransactionOutcome::Rollback(res) => {
			rollback_transaction();
			res
		},
	}
}

/// Execute the supplied function, adding a new storage layer.
///
/// This is the same as `with_transaction`, but assuming that any function returning
/// an `Err` should rollback, and any function returning `Ok` should commit. This
/// provides a cleaner API to the developer who wants this behavior.
pub fn with_storage_layer<T, E, F>(f: F) -> Result<T, E>
where
	E: From<DispatchError>,
	F: FnOnce() -> Result<T, E>,
{
	with_transaction(|| {
		let r = f();
		if r.is_ok() {
			TransactionOutcome::Commit(r)
		} else {
			TransactionOutcome::Rollback(r)
		}
	})
}

/// Execute the supplied function, ensuring we are at least in one storage layer.
///
/// If we are already in a storage layer, we just execute the provided closure.
/// If we are not, we execute the closure within a [`with_storage_layer`].
pub fn in_storage_layer<T, E, F>(f: F) -> Result<T, E>
where
	E: From<DispatchError>,
	F: FnOnce() -> Result<T, E>,
{
	if is_transactional() {
		f()
	} else {
		with_storage_layer(f)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{assert_noop, assert_ok};
	use sp_io::TestExternalities;
	use sp_runtime::DispatchResult;

	#[test]
	fn is_transactional_should_return_false() {
		TestExternalities::default().execute_with(|| {
			assert!(!is_transactional());
		});
	}

	#[test]
	fn is_transactional_should_not_error_in_with_transaction() {
		TestExternalities::default().execute_with(|| {
			assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
				assert!(is_transactional());
				TransactionOutcome::Commit(Ok(()))
			}));

			assert_noop!(
				with_transaction(|| -> TransactionOutcome<DispatchResult> {
					assert!(is_transactional());
					TransactionOutcome::Rollback(Err("revert".into()))
				}),
				"revert"
			);
		});
	}

	fn recursive_transactional(num: u32) -> DispatchResult {
		if num == 0 {
			return Ok(())
		}

		with_transaction(|| -> TransactionOutcome<DispatchResult> {
			let res = recursive_transactional(num - 1);
			TransactionOutcome::Commit(res)
		})
	}

	#[test]
	fn transaction_limit_should_work() {
		TestExternalities::default().execute_with(|| {
			assert_eq!(get_transaction_level(), 0);

			assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
				assert_eq!(get_transaction_level(), 1);
				TransactionOutcome::Commit(Ok(()))
			}));

			assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
				assert_eq!(get_transaction_level(), 1);
				let res = with_transaction(|| -> TransactionOutcome<DispatchResult> {
					assert_eq!(get_transaction_level(), 2);
					TransactionOutcome::Commit(Ok(()))
				});
				TransactionOutcome::Commit(res)
			}));

			assert_ok!(recursive_transactional(255));
			assert_noop!(
				recursive_transactional(256),
				sp_runtime::TransactionalError::LimitReached
			);

			assert_eq!(get_transaction_level(), 0);
		});
	}

	#[test]
	fn in_storage_layer_works() {
		TestExternalities::default().execute_with(|| {
			assert_eq!(get_transaction_level(), 0);

			let res = in_storage_layer(|| -> DispatchResult {
				assert_eq!(get_transaction_level(), 1);
				in_storage_layer(|| -> DispatchResult {
					// We are still in the same layer :)
					assert_eq!(get_transaction_level(), 1);
					Ok(())
				})
			});

			assert_ok!(res);

			let res = in_storage_layer(|| -> DispatchResult {
				assert_eq!(get_transaction_level(), 1);
				in_storage_layer(|| -> DispatchResult {
					// We are still in the same layer :)
					assert_eq!(get_transaction_level(), 1);
					Err("epic fail".into())
				})
			});

			assert_noop!(res, "epic fail");
		});
	}
}
