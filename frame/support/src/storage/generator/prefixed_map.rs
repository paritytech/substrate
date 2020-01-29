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

use codec::{FullCodec, Decode};
use crate::{storage::{generator::PrefixIterator, top}, hash::{Twox128, StorageHasher}};
/// Trait for maps that store all its value after a unique prefix.
///
/// typically the case for double_map and regular map.
///
/// By default the final prefix is:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait StoragePrefixedMap {
	/// The type of the value stored in storage.
	type Value: FullCodec;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Final full prefix that prefixes all keys.
	fn final_prefix() -> [u8; 32] {
		let mut final_key = [0u8; 32];
		final_key[0..16].copy_from_slice(&Twox128::hash(Self::module_prefix()));
		final_key[16..32].copy_from_slice(&Twox128::hash(Self::storage_prefix()));
		final_key
	}

	/// Remove all value of the storage.
	fn remove_all() {
		sp_io::storage::clear_prefix(&Self::final_prefix())
	}

	/// Iter over all value of the storage.
	fn iter() -> PrefixIterator<Self::Value> {
		let prefix = Self::final_prefix();
		PrefixIterator {
			prefix: prefix.to_vec(),
			previous_key: prefix.to_vec(),
			phantom_data: Default::default(),
		}
	}

	/// Translate the values from some previous `OldValue` to the current type.
	///
	/// `TV` translates values.
	///
	/// Returns `Err` if the map could not be interpreted as the old type, and Ok if it could.
	/// The `Err` contains the number of value that couldn't be interpreted, those value are
	/// removed from the map.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_initialize, while
	/// ensuring **no usage of this storage are made before the call to `on_initialize`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate_values<OldValue, TV>(translate_val: TV) -> Result<(), u32>
		where OldValue: Decode, TV: Fn(OldValue) -> Self::Value
	{
		let prefix = Self::final_prefix();
		let mut previous_key = prefix.to_vec();
		let mut errors = 0;
		while let Some(next_key) = sp_io::storage::next_key(&previous_key)
			.filter(|n| n.starts_with(&prefix[..]))
		{
			if let Some(value) = top::get(&next_key) {
				top::put(&next_key[..], &translate_val(value));
			} else {
				// We failed to read the value. Remove the key and increment errors.
				top::kill(&next_key[..]);
				errors += 1;
			}

			previous_key = next_key;
		}

		if errors == 0 {
			Ok(())
		} else {
			Err(errors)
		}
	}
}

#[cfg(test)]
mod test {
	use sp_core::hashing::twox_128;
	use sp_io::TestExternalities;
	use crate::{StoragePrefixedMap, storage::top};

	#[test]
	fn prefixed_map_works() {
		TestExternalities::default().execute_with(|| {
			struct MyStorage;
			impl StoragePrefixedMap for MyStorage {
				type Value = u64;

				fn module_prefix() -> &'static [u8] {
					b"MyModule"
				}

				fn storage_prefix() -> &'static [u8] {
					b"MyStorage"
				}
			}

			let key_before = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_sub(1).unwrap();
				k
			};
			let key_after = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_add(1).unwrap();
				k
			};

			top::put(&key_before[..], &32u64);
			top::put(&key_after[..], &33u64);

			let k = [twox_128(b"MyModule"), twox_128(b"MyStorage")].concat();
			assert_eq!(MyStorage::final_prefix().to_vec(), k);

			// test iteration
			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![]);

			top::put(&[&k[..], &vec![1][..]].concat(), &1u64);
			top::put(&[&k[..], &vec![1, 1][..]].concat(), &2u64);
			top::put(&[&k[..], &vec![8][..]].concat(), &3u64);
			top::put(&[&k[..], &vec![10][..]].concat(), &4u64);

			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![1, 2, 3, 4]);

			// test removal
			MyStorage::remove_all();
			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![]);

			// test migration
			top::put(&[&k[..], &vec![1][..]].concat(), &1u32);
			top::put(&[&k[..], &vec![8][..]].concat(), &2u32);

			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![]);
			MyStorage::translate_values(|v: u32| v as u64).unwrap();
			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![1, 2]);
			MyStorage::remove_all();

			// test migration 2
			top::put(&[&k[..], &vec![1][..]].concat(), &1u128);
			top::put(&[&k[..], &vec![1, 1][..]].concat(), &2u64);
			top::put(&[&k[..], &vec![8][..]].concat(), &3u128);
			top::put(&[&k[..], &vec![10][..]].concat(), &4u32);

			// (contains some value that successfully decoded to u64)
			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![1, 2, 3]);
			assert_eq!(MyStorage::translate_values(|v: u128| v as u64), Err(2));
			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![1, 3]);
			MyStorage::remove_all();

			// test that other values are not modified.
			assert_eq!(top::get(&key_before[..]), Some(32u64));
			assert_eq!(top::get(&key_after[..]), Some(33u64));
		});
	}
}
