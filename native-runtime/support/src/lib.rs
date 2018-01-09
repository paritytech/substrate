#[macro_use]
extern crate lazy_static;
extern crate parking_lot;

pub use std::vec::Vec;
pub use std::rc::Rc;
pub use std::cell::RefCell;
pub use std::boxed::Box;
pub use std::mem::{size_of, transmute};

use std::collections::HashMap;
use parking_lot::Mutex;

lazy_static! {
	static ref HASHMAP: Mutex<HashMap<Vec<u8>, Vec<u8>>> = Mutex::new(HashMap::new());
}

pub fn storage(_key: &[u8]) -> Vec<u8> {
	HASHMAP.lock().get(_key).cloned().unwrap_or_else(Vec::new)
}

pub fn storage_into<T: Sized>(_key: &[u8]) -> Option<T> {
	let size = size_of::<T>();
	if let Some(value) = HASHMAP.lock().get(_key) {
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
}

pub fn set_storage(_key: &[u8], _value: &[u8]) {
	HASHMAP.lock().insert(_key.to_vec(), _value.to_vec());
}

pub fn init_storage(new: HashMap<Vec<u8>, Vec<u8>>) {
	*HASHMAP.lock() = new;
}

#[macro_export]
macro_rules! impl_stubs {
	($( $name:ident ),*) => {}
}

#[cfg(test)]
mod tests {
	use super::*;

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn storage_works() {
		assert_eq!(storage(b"hello"), vec![]);
		set_storage(b"hello", b"world");
		assert_eq!(storage(b"hello"), b"world".to_vec());
		assert_eq!(storage(b"foo"), vec![]);
		set_storage(b"foo", &[1, 2, 3][..]);
		assert_eq!(storage_into::<[u8; 3]>(b"foo"), Some([1, 2, 3]));
		assert_eq!(storage_into::<[u8; 3]>(b"hello"), None);
		init_storage(map![b"foo".to_vec() => b"bar".to_vec()]);
		assert_eq!(storage(b"hello"), vec![]);
		assert_eq!(storage(b"foo"), b"bar".to_vec());
	}
}
