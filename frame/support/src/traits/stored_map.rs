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

//! Traits and associated datatypes for managing abstract stored values.

use crate::storage::StorageMap;
use codec::FullCodec;
use sp_runtime::DispatchError;

/// An abstraction of a value stored within storage, but possibly as part of a larger composite
/// item.
pub trait StoredMap<K, T: Default> {
	/// Get the item, or its default if it doesn't yet exist; we make no distinction between the
	/// two.
	fn get(k: &K) -> T;

	/// Maybe mutate the item only if an `Ok` value is returned from `f`. Do nothing if an `Err` is
	/// returned. It is removed or reset to default value if it has been mutated to `None`.
	/// `f` will always be called with an option representing if the storage item exists (`Some<V>`)
	/// or if the storage item does not exist (`None`), independent of the `QueryType`.
	fn try_mutate_exists<R, E: From<DispatchError>>(
		k: &K,
		f: impl FnOnce(&mut Option<T>) -> Result<R, E>,
	) -> Result<R, E>;

	// Everything past here has a default implementation.

	/// Mutate the item.
	fn mutate<R>(k: &K, f: impl FnOnce(&mut T) -> R) -> Result<R, DispatchError> {
		Self::mutate_exists(k, |maybe_account| match maybe_account {
			Some(ref mut account) => f(account),
			x @ None => {
				let mut account = Default::default();
				let r = f(&mut account);
				*x = Some(account);
				r
			},
		})
	}

	/// Mutate the item, removing or resetting to default value if it has been mutated to `None`.
	///
	/// This is infallible as long as the value does not get destroyed.
	fn mutate_exists<R>(k: &K, f: impl FnOnce(&mut Option<T>) -> R) -> Result<R, DispatchError> {
		Self::try_mutate_exists(k, |x| -> Result<R, DispatchError> { Ok(f(x)) })
	}

	/// Set the item to something new.
	fn insert(k: &K, t: T) -> Result<(), DispatchError> {
		Self::mutate(k, |i| *i = t)
	}

	/// Remove the item or otherwise replace it with its default value; we don't care which.
	fn remove(k: &K) -> Result<(), DispatchError> {
		Self::mutate_exists(k, |x| *x = None)
	}
}

/// A shim for placing around a storage item in order to use it as a `StoredValue`. Ideally this
/// wouldn't be needed as `StorageValue`s should blanket implement `StoredValue`s, however this
/// would break the ability to have custom impls of `StoredValue`. The other workaround is to
/// implement it directly in the macro.
///
/// This form has the advantage that two additional types are provides, `Created` and `Removed`,
/// which are both generic events that can be tied to handlers to do something in the case of being
/// about to create an account where one didn't previously exist (at all; not just where it used to
/// be the default value), or where the account is being removed or reset back to the default value
/// where previously it did exist (though may have been in a default state). This works well with
/// system module's `CallOnCreatedAccount` and `CallKillAccount`.
pub struct StorageMapShim<S, K, T>(sp_std::marker::PhantomData<(S, K, T)>);
impl<S: StorageMap<K, T, Query = T>, K: FullCodec, T: FullCodec + Default> StoredMap<K, T>
	for StorageMapShim<S, K, T>
{
	fn get(k: &K) -> T {
		S::get(k)
	}
	fn insert(k: &K, t: T) -> Result<(), DispatchError> {
		S::insert(k, t);
		Ok(())
	}
	fn remove(k: &K) -> Result<(), DispatchError> {
		if S::contains_key(&k) {
			S::remove(k);
		}
		Ok(())
	}
	fn mutate<R>(k: &K, f: impl FnOnce(&mut T) -> R) -> Result<R, DispatchError> {
		Ok(S::mutate(k, f))
	}
	fn mutate_exists<R>(k: &K, f: impl FnOnce(&mut Option<T>) -> R) -> Result<R, DispatchError> {
		S::try_mutate_exists(k, |maybe_value| {
			let r = f(maybe_value);
			Ok(r)
		})
	}
	fn try_mutate_exists<R, E: From<DispatchError>>(
		k: &K,
		f: impl FnOnce(&mut Option<T>) -> Result<R, E>,
	) -> Result<R, E> {
		S::try_mutate_exists(k, |maybe_value| {
			let r = f(maybe_value)?;
			Ok(r)
		})
	}
}
