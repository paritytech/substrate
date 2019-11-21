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

use codec::{Encode, Decode, EncodeLike};
use runtime_io::{TestExternalities, hashing};

pub trait Trait {
	type Origin;
	type BlockNumber: Encode + Decode + EncodeLike + Default + Clone;
}

support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

support::decl_storage!{
	trait Store for Module<T: Trait> as TestModule {
		pub PrefixedMap: prefixed_map u32 => u64;
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn prefixed_map_works() {
		TestExternalities::default().execute_with(|| {
			let key_before = {
				let mut k = PrefixedMap::prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_sub(1).unwrap();
				k
			};
			let key_after = {
				let mut k = PrefixedMap::prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_add(1).unwrap();
				k
			};

			support::storage::unhashed::put(&key_before[..], &32u64);
			support::storage::unhashed::put(&key_after[..], &33u64);
			let mut k = hashing::twox_128(b"TestModule").to_vec();
			k.extend(hashing::twox_128(b"PrefixedMap").iter());
			assert_eq!(PrefixedMap::prefix(), &k[..]);

			assert_eq!(PrefixedMap::iter().collect::<Vec<_>>(), vec![]);

			PrefixedMap::insert(1, 1);
			PrefixedMap::insert(2, 2);
			PrefixedMap::insert(4, 4);
			PrefixedMap::insert(10, 10);

			let mut key = PrefixedMap::prefix();
			let encoded = 1u32.encode();
			key.extend_from_slice(&hashing::blake2_256(&encoded[..])[..]);

			// NOTE: order is different because keys are hashed.
			assert_eq!(PrefixedMap::iter().collect::<Vec<_>>(), vec![4, 10, 2, 1]);
			PrefixedMap::remove_all();
			assert_eq!(PrefixedMap::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(support::storage::unhashed::get(&key_before[..]), Some(32u64));
			assert_eq!(support::storage::unhashed::get(&key_after[..]), Some(33u64));
		});
	}
}
