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
	/// and write changes after that you should rather be using `mutate`.
	///
	/// The function returns `None` if the value was not found in storage,
	/// otherwise a decoding of the value to requested type.
	pub fn get<T: codec::Decode>(&self) -> Option<Option<T>> {
		sp_io::offchain::local_storage_get(self.kind, self.key)
			.map(|val| T::decode(&mut &*val).ok())
	}

	/// Retrieve & decode the value and set it to a new one atomically.
	///
	/// Function `f` should return a new value that we should attempt to write to storage.
	/// This function returns:
	/// 1. `Ok(Ok(T))` in case the value has been successfully set.
	/// 2. `Ok(Err(T))` in case the value was calculated by the passed closure `f`,
	///    but it could not be stored.
	/// 3. `Err(_)` in case `f` returns an error.
	pub fn mutate<T, E, F>(&self, f: F) -> Result<Result<T, T>, E> where
		T: codec::Codec,
		F: FnOnce(Option<Option<T>>) -> Result<T, E>
	{
		let value = sp_io::offchain::local_storage_get(self.kind, self.key);
		let decoded = value.as_deref().map(|mut v| T::decode(&mut v).ok());
		let val = f(decoded)?;
		let set = val.using_encoded(|new_val| {
			sp_io::offchain::local_storage_compare_and_set(
				self.kind,
				self.key,
				value,
				new_val,
			)
		});

		if set {
			Ok(Ok(val))
		} else {
			Ok(Err(val))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_io::TestExternalities;
	use sp_core::offchain::{
		OffchainExt,
		testing,
	};

	#[test]
	fn should_set_and_get() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainExt::new(offchain));

		t.execute_with(|| {
			let val = StorageValue::persistent(b"testval");

			assert_eq!(val.get::<u32>(), None);

			val.set(&15_u32);

			assert_eq!(val.get::<u32>(), Some(Some(15_u32)));
			assert_eq!(val.get::<Vec<u8>>(), Some(None));
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
		t.register_extension(OffchainExt::new(offchain));

		t.execute_with(|| {
			let val = StorageValue::persistent(b"testval");

			let result = val.mutate::<u32, (), _>(|val| {
				assert_eq!(val, None);

				Ok(16_u32)
			});
			assert_eq!(result, Ok(Ok(16_u32)));
			assert_eq!(val.get::<u32>(), Some(Some(16_u32)));
			assert_eq!(
				state.read().persistent_storage.get(b"testval"),
				Some(vec![16_u8, 0, 0, 0])
			);

			// mutate again, but this time early-exit.
			let res = val.mutate::<u32, (), _>(|val| {
				assert_eq!(val, Some(Some(16_u32)));
				Err(())
			});
			assert_eq!(res, Err(()));
		})
	}
}
