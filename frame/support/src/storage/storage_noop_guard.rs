// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

// Feature gated since it can panic.
#![cfg(any(feature = "std", feature = "runtime-benchmarks", feature = "try-runtime", test))]

//! Contains the [`crate::StorageNoopGuard`] for conveniently asserting
//! that no storage mutation has been made by a whole code block.

/// Asserts that no storage changes took place between con- and destruction of [`Self`].
///
/// This is easier than wrapping the whole code-block inside a `assert_storage_noop!`.
///
/// # Example
///
/// ```should_panic
/// use frame_support::{StorageNoopGuard, storage::unhashed::put};
///
/// sp_io::TestExternalities::default().execute_with(|| {
/// 	let _guard = frame_support::StorageNoopGuard::default();
/// 	put(b"key", b"value");
/// 	// Panics since there are storage changes.
/// });
/// ```
#[must_use]
pub struct StorageNoopGuard(sp_std::vec::Vec<u8>);

impl Default for StorageNoopGuard {
	fn default() -> Self {
		Self(frame_support::storage_root(frame_support::StateVersion::V1))
	}
}

impl Drop for StorageNoopGuard {
	fn drop(&mut self) {
		// No need to double panic, eg. inside a test assertion failure.
		if sp_std::thread::panicking() {
			return
		}
		assert_eq!(
			frame_support::storage_root(frame_support::StateVersion::V1),
			self.0,
			"StorageNoopGuard detected wrongful storage changes.",
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_io::TestExternalities;

	#[test]
	#[should_panic(expected = "StorageNoopGuard detected wrongful storage changes.")]
	fn storage_noop_guard_panics_on_changed() {
		TestExternalities::default().execute_with(|| {
			let _guard = StorageNoopGuard::default();
			frame_support::storage::unhashed::put(b"key", b"value");
		});
	}

	#[test]
	fn storage_noop_guard_works_on_unchanged() {
		TestExternalities::default().execute_with(|| {
			let _guard = StorageNoopGuard::default();
			frame_support::storage::unhashed::put(b"key", b"value");
			frame_support::storage::unhashed::kill(b"key");
		});
	}

	#[test]
	#[should_panic(expected = "StorageNoopGuard detected wrongful storage changes.")]
	fn storage_noop_guard_panics_on_early_drop() {
		TestExternalities::default().execute_with(|| {
			let guard = StorageNoopGuard::default();
			frame_support::storage::unhashed::put(b"key", b"value");
			sp_std::mem::drop(guard);
			frame_support::storage::unhashed::kill(b"key");
		});
	}

	#[test]
	fn storage_noop_guard_works_on_changed_forget() {
		TestExternalities::default().execute_with(|| {
			let guard = StorageNoopGuard::default();
			frame_support::storage::unhashed::put(b"key", b"value");
			sp_std::mem::forget(guard);
		});
	}

	#[test]
	#[should_panic(expected = "Something else")]
	fn storage_noop_guard_does_not_double_panic() {
		TestExternalities::default().execute_with(|| {
			let _guard = StorageNoopGuard::default();
			frame_support::storage::unhashed::put(b"key", b"value");
			panic!("Something else");
		});
	}
}
