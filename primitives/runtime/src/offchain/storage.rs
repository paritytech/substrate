// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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
	/// 2. `Ok(Err(T))` in case the value was returned, but it couldn't have been set.
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
		OffchainStorage,
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
				state.read().persistent_storage.get(b"", b"testval"),
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
				state.read().persistent_storage.get(b"", b"testval"),
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
