// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! A set of storage helpers for offchain workers.

use sp_core::offchain::StorageKind;

/// A storage value with a static key.
pub type StorageValue = StorageValueRef<'static>;

/// An abstraction over local storage value.
pub struct StorageValueRef<'a> {
	key: &'a [u8],
	kind: StorageKind,
}

/// Reason for not being able to provide the stored value
#[derive(Debug, PartialEq, Eq)]
pub enum StorageRetrievalError {
	/// Value found but undecodable
	Undecodable,
}

/// Possible errors when mutating a storage value.
#[derive(Debug, PartialEq, Eq)]
pub enum MutateStorageError<T, E> {
	/// The underlying db failed to update due to a concurrent modification.
	/// Contains the new value that was not stored.
	ConcurrentModification(T),
	/// The function given to us to create the value to be stored failed.
	/// May be used to signal that having looked at the existing value,
	/// they don't want to mutate it.
	ValueFunctionFailed(E)
}

impl<'a> StorageValueRef<'a> {
	/// Create a new reference to a value in the persistent local storage.
	pub fn persistent(key: &'a [u8]) -> Self {
		Self { key, kind: StorageKind::PERSISTENT }
	}

	/// Create a new reference to a value in the fork-aware local storage.
	pub fn local(key: &'a [u8]) -> Self {
		Self { key, kind: StorageKind::LOCAL }
	}

	/// Set the value of the storage to encoding of given parameter.
	///
	/// Note that the storage may be accessed by workers running concurrently,
	/// if you happen to write a `get-check-set` pattern you should most likely
	/// be using `mutate` instead.
	pub fn set(&self, value: &impl codec::Encode) {
		value.using_encoded(|val| {
			sp_io::offchain::local_storage_set(self.kind, self.key, val)
		})
	}

	/// Remove the associated value from the storage.
	pub fn clear(&mut self) {
		sp_io::offchain::local_storage_clear(self.kind, self.key)
	}

	/// Retrieve & decode the value from storage.
	///
	/// Note that if you want to do some checks based on the value
	/// and write changes after that, you should rather be using `mutate`.
	///
	/// Returns the value if stored.
	/// Returns an error if the value could not be decoded.
	pub fn get<T: codec::Decode>(&self) -> Result<Option<T>, StorageRetrievalError> {
		sp_io::offchain::local_storage_get(self.kind, self.key)
			.map(|val| T::decode(&mut &*val)
			.map_err(|_| StorageRetrievalError::Undecodable))
			.transpose()
	}

	/// Retrieve & decode the current value and set it to a new value atomically.
	///
	/// Function `mutate_val` takes as input the current value and should
	/// return a new value that is attempted to be written to storage.
	///
	/// This function returns:
	/// 1. `Ok(T)` in case the value has been successfully set.
	/// 2. `Err(MutateStorageError::ConcurrentModification(T))` in case the value was calculated
	/// by the passed closure `mutate_val`, but it could not be stored.
	/// 3. `Err(MutateStorageError::ValueFunctionFailed(_))` in case `mutate_val` returns an error.
	pub fn mutate<T, E, F>(&self, mutate_val: F) -> Result<T, MutateStorageError<T,E>> where
		T: codec::Codec,
		F: FnOnce(Result<Option<T>, StorageRetrievalError>) -> Result<T, E>
	{
		let value = sp_io::offchain::local_storage_get(self.kind, self.key);
		let decoded = value.as_deref()
			.map(|mut bytes| {
				T::decode(&mut bytes)
					.map_err(|_| StorageRetrievalError::Undecodable)
			}).transpose();

		let val = mutate_val(decoded).map_err(|err| MutateStorageError::ValueFunctionFailed(err))?;

		let set = val.using_encoded(|new_val| {
			sp_io::offchain::local_storage_compare_and_set(
				self.kind,
				self.key,
				value,
				new_val,
			)
		});
		if set {
			Ok(val)
		} else {
			Err(MutateStorageError::ConcurrentModification(val))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_io::TestExternalities;
	use sp_core::offchain::{
		OffchainDbExt,
		testing,
	};

	#[test]
	fn should_set_and_get() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain));

		t.execute_with(|| {
			let val = StorageValue::persistent(b"testval");

			assert_eq!(val.get::<u32>(), Ok(None));

			val.set(&15_u32);

			assert_eq!(val.get::<u32>(), Ok(Some(15_u32)));
			assert_eq!(val.get::<Vec<u8>>(), Err(StorageRetrievalError::Undecodable));
			assert_eq!(
				state.read().persistent_storage.get(b"testval"),
				Some(vec![15_u8, 0, 0, 0])
			);
		})
	}

	#[test]
	fn should_mutate() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain));

		t.execute_with(|| {
			let val = StorageValue::persistent(b"testval");

			let result = val.mutate::<u32, (), _>(|val| {
				assert_eq!(val, Ok(None));

				Ok(16_u32)
			});
			assert_eq!(result, Ok(16_u32));
			assert_eq!(val.get::<u32>(), Ok(Some(16_u32)));
			assert_eq!(
				state.read().persistent_storage.get(b"testval"),
				Some(vec![16_u8, 0, 0, 0])
			);

			// mutate again, but this time early-exit.
			let res = val.mutate::<u32, (), _>(|val| {
				assert_eq!(val, Ok(Some(16_u32)));
				Err(())
			});
			assert_eq!(res, Err(MutateStorageError::ValueFunctionFailed(())));
		})
	}
}
