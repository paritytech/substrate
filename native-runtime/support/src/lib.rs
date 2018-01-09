pub use std::vec::Vec;

pub fn storage(_key: &[u8]) -> Vec<u8> { vec![] }
pub fn storage_into<T: Sized>(_key: &[u8]) -> Option<T> { None }
pub fn set_storage(_key: &[u8], _value: &[u8]) {}

#[macro_export]
macro_rules! impl_stubs {
	($( $name:ident ),*) => {}
}
