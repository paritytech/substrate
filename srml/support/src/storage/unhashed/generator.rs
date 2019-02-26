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

use crate::codec;
#[doc(hidden)]
pub use crate::rstd::borrow::Borrow;
#[doc(hidden)]
pub use crate::rstd::marker::PhantomData;
#[doc(hidden)]
pub use crate::rstd::boxed::Box;

/// Abstraction around storage with unhashed access.
pub trait UnhashedStorage {
	/// true if the key exists in storage.
	fn exists(&self, key: &[u8]) -> bool;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T>;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. Will panic if
	/// it's not there.
	fn require<T: codec::Decode>(&self, key: &[u8]) -> T { self.get(key).expect("Required values must be in storage") }

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. The type's
	/// default is returned if it's not there.
	fn get_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T { self.get(key).unwrap_or_default() }

	/// Put a value in under a key.
	fn put<T: codec::Encode>(&self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]);

	/// Remove the bytes of a key from storage.
	fn kill_prefix(&self, prefix: &[u8]);

	/// Take a value from storage, deleting it after reading.
	fn take<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		let value = self.get(key);
		self.kill(key);
		value
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_panic<T: codec::Decode>(&self, key: &[u8]) -> T { self.take(key).expect("Required values must be in storage") }

	/// Take a value from storage, deleting it after reading.
	fn take_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T { self.take(key).unwrap_or_default() }
}

// We use a construct like this during when genesis storage is being built.
#[cfg(feature = "std")]
impl<H> UnhashedStorage for (crate::rstd::cell::RefCell<&mut sr_primitives::StorageOverlay>, H) {
	fn exists(&self, key: &[u8]) -> bool {
		self.0.borrow().contains_key(key)
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		self.0.borrow().get(key)
			.map(|x| codec::Decode::decode(&mut x.as_slice()).expect("Unable to decode expected type."))
	}

	fn put<T: codec::Encode>(&self, key: &[u8], val: &T) {
		self.0.borrow_mut().insert(key.to_vec(), codec::Encode::encode(val));
	}

	fn kill(&self, key: &[u8]) {
		self.0.borrow_mut().remove(key);
	}

	fn kill_prefix(&self, prefix: &[u8]) {
		self.0.borrow_mut().retain(|key, _| {
			!key.starts_with(prefix)
		})
	}
}
