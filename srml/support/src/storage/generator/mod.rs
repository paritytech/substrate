// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Generators are a set of trait on which storage traits are implemented.
//!
//! (i.e. implementing the generator for StorageValue on a type will automatically derive the
//! implementation of StorageValue for this type).
//!
//! They are used by `decl_storage`.

mod linked_map;
mod map;
mod double_map;
mod value;

pub use linked_map::{StorageLinkedMap, Enumerator, Linkage};
pub use map::StorageMap;
pub use double_map::StorageDoubleMap;
pub use value::StorageValue;


#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use runtime_io::TestExternalities;
	use codec::Encode;
	use crate::storage::{unhashed, generator::StorageValue};

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

	crate::decl_storage! {
		trait Store for Module<T: Trait> as Runtime {
			Value get(fn value) config(): (u64, u64);
		}
	}

	#[test]
	fn value_translate_works() {
		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			// put the old value `1111u32` in the storage.
			let key = Value::storage_value_final_key();
			unhashed::put_raw(&key, &1111u32.encode());

			// translate
			let translate_fn = |old: Option<u32>| -> Option<(u64, u64)> {
				old.map(|o| (o.into(), (o*2).into()))
			};
			let _ = Value::translate(translate_fn);

			// new storage should be `(1111, 1111 * 2)`
			assert_eq!(Value::get(), (1111, 2222));
		})
	}
}
