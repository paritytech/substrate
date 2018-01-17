#[macro_use]
extern crate environmental;
extern crate polkadot_state_machine;
extern crate tiny_keccak;

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

environmental!(ext : Externalities<Error=NoError> + 'static);

pub fn storage(key: &[u8]) -> Vec<u8> {
	ext::with(|ext| ext.storage(key).ok().map(|s| s.to_vec()))
		.unwrap_or(None)
		.unwrap_or_else(|| vec![])
}

pub fn read_storage(key: &[u8], value_out: &mut [u8]) -> usize {
	ext::with(|ext| {
		if let Ok(value) = ext.storage(key) {
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

	ext::with(|ext| {
		if let Ok(value) = ext.storage(_key) {
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
	ext::with(|ext|
		ext.set_storage(_key.to_vec(), _value.to_vec())
	);
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	ext::with(|ext|
		ext.chain_id()
	).unwrap_or(0)
}

/// Conduct a Keccak-256 hash of the given data.
pub use tiny_keccak::keccak256;

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut (Externalities<Error=NoError> + 'static), f: F) -> R {
	ext::using(ext, f)
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

		fn chain_id(&self) -> u64 { 42 }
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
