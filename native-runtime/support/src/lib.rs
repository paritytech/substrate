#[macro_use]
extern crate environmental;
extern crate polkadot_state_machine;

pub use std::vec::Vec;
pub use std::rc::Rc;
pub use std::cell::RefCell;
pub use std::boxed::Box;
pub use std::slice;
pub use std::mem::{size_of, transmute, swap, uninitialized};

pub use polkadot_state_machine::Externalities;
use std::fmt;

// TODO: use the real error, not NoError.

#[derive(Debug)]
pub struct NoError;
impl fmt::Display for NoError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "") }
}

pub struct ExternalitiesHolder<'a> {
	ext: &'a mut Externalities<Error=NoError>,
}

declare_generic!(ext : ExternalitiesHolder);

pub fn storage(key: &[u8]) -> Vec<u8> {
	ext::with(|holder| holder.ext.storage(key).ok().map(|s| s.to_vec()))
		.unwrap_or(None)
		.unwrap_or_else(|| vec![])
}

pub fn read_storage(key: &[u8], value_out: &mut [u8]) -> usize {
	ext::with(|holder| {
		if let Ok(value) = holder.ext.storage(key) {
			let written = ::std::cmp::min(value.len(), value_out.len());
			value_out[0..written].copy_from_slice(&value[0..written]);
			value.len()
		} else {
			0
		}
	}).unwrap_or(0)
}

pub fn storage_into<T: Sized>(_key: &[u8]) -> Option<T> {
	let size = size_of::<T>();

	ext::with(|holder| {
		if let Ok(value) = holder.ext.storage(_key) {
			if value.len() == size {
				unsafe {
					let mut result: T = std::mem::uninitialized();
					std::slice::from_raw_parts_mut(transmute::<*mut T, *mut u8>(&mut result), size)
						.copy_from_slice(&value);
					return Some(result);
				}
			}
		}
		None
	}).unwrap_or(None)
}

pub fn set_storage(_key: &[u8], _value: &[u8]) {
	ext::with(|holder|
		holder.ext.set_storage(_key.to_vec(), _value.to_vec())
	);
}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut Externalities<Error=NoError>, f: F) -> R {
	let mut h = ExternalitiesHolder { ext };
	ext::using(&mut h, f)
}

#[macro_export]
macro_rules! impl_stubs {
	($( $name:ident ),*) => {}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;

	#[derive(Debug, Default)]
	struct TestExternalities {
		storage: HashMap<Vec<u8>, Vec<u8>>,
	}
	impl Externalities for TestExternalities {
		type Error = NoError;

		fn storage(&self, key: &[u8]) -> Result<&[u8], NoError> {
			Ok(self.storage.get(&key.to_vec()).map_or(&[] as &[u8], Vec::as_slice))
		}

		fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
			self.storage.insert(key, value);
		}
	}

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn storage_works() {
		let mut t = TestExternalities { storage: map![], };
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), b"".to_vec());
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), b"world".to_vec());
			assert_eq!(storage(b"foo"), b"".to_vec());
			set_storage(b"foo", &[1, 2, 3][..]);
			assert_eq!(storage_into::<[u8; 3]>(b"foo"), Some([1, 2, 3]));
			assert_eq!(storage_into::<[u8; 3]>(b"hello"), None);
			true
		}));

		t.storage = map![b"foo".to_vec() => b"bar".to_vec()];

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), b"".to_vec());
			assert_eq!(storage(b"foo"), b"bar".to_vec());
			false
		}));
	}
}
