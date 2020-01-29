// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Generators are a set of trait that implement some abstraction over top trie.
//!
//! They are used by `decl_storage`.

mod linked_map;
mod map;
mod double_map;
mod value;
mod prefixed_map;

pub use linked_map::{StorageLinkedMap, Enumerator, Linkage, KeyFormat as LinkedMapKeyFormat};
pub use map::StorageMap;
pub use double_map::StorageDoubleMap;
pub use value::StorageValue;
pub use prefixed_map::StoragePrefixedMap;

use sp_std::{prelude::*, marker::PhantomData};
use crate::storage::top;
use codec::Decode;

/// Iterator over all keys after a prefix in top trie.
pub struct PrefixIterator<Value> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	phantom_data: PhantomData<Value>,
}

impl<Value: Decode> Iterator for PrefixIterator<Value> {
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		match sp_io::storage::next_key(&self.previous_key)
			.filter(|n| n.starts_with(&self.prefix[..]))
		{
			Some(next_key) => {
				let value = top::get(&next_key);

				if value.is_none() {
					runtime_print!(
						"ERROR: returned next_key has no value:\nkey is {:?}\nnext_key is {:?}",
						&self.previous_key, &next_key,
					);
				}

				self.previous_key = next_key;

				value
			},
			_ => None,
		}
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use sp_io::TestExternalities;
	use codec::{Encode, Decode};
	use crate::storage::{top, generator::{StorageValue, StorageLinkedMap}};

	struct Runtime {}
	pub trait Trait {
		type Origin;
		type BlockNumber;
	}

	impl Trait for Runtime {
		type Origin = u32;
		type BlockNumber = u32;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}

	#[derive(Encode, Decode, Clone, Debug, Eq, PartialEq)]
	struct NumberNumber {
		a: u32,
		b: u32,
	}

	crate::decl_storage! {
		trait Store for Module<T: Trait> as Runtime {
			Value get(fn value) config(): (u64, u64);
			NumberMap: linked_map hasher(blake2_256) NumberNumber => u64;
		}
	}

	#[test]
	fn value_translate_works() {
		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			// put the old value `1111u32` in the storage.
			let key = Value::top_trie_key();
			top::put_raw(&key, &1111u32.encode());

			// translate
			let translate_fn = |old: Option<u32>| -> Option<(u64, u64)> {
				old.map(|o| (o.into(), (o*2).into()))
			};
			let _ = Value::translate(translate_fn);

			// new storage should be `(1111, 1111 * 2)`
			assert_eq!(Value::get(), (1111, 2222));
		})
	}

	#[test]
	fn linked_map_translate_works() {
		use super::linked_map::{self, Enumerator, KeyFormat};

		type Format = <NumberMap as StorageLinkedMap>::KeyFormat;

		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			// start with a map of u32 -> u32.
			for i in 0u32..100u32 {
				let final_key = <Format as KeyFormat>::top_trie_key(&i);

				let linkage = linked_map::new_head_linkage::<_, u32, u32, Format>(&i);
				top::put(final_key.as_ref(), &(&i, linkage));
			}

			let head = linked_map::read_head::<u32, Format>().unwrap();

			assert_eq!(
				Enumerator::<u32, u32, Format>::from_head(head).collect::<Vec<_>>(),
				(0..100).rev().map(|x| (x, x)).collect::<Vec<_>>(),
			);

			// do translation.
			NumberMap::translate(
				|k: u32| NumberNumber { a: k, b: k },
				|v: u32| (v as u64) << 32 | v as u64,
			).unwrap();

			assert!(linked_map::read_head::<NumberNumber, Format>().is_some());
			assert_eq!(
				NumberMap::enumerate().collect::<Vec<_>>(),
				(0..100u32).rev().map(|x| (
					NumberNumber { a: x, b: x },
					(x as u64) << 32 | x as u64,
				)).collect::<Vec<_>>(),
			);
		})
	}
}
