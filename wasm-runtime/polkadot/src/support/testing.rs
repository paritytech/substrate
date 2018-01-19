use runtime_support::{NoError, Externalities};
use std::collections::HashMap;
use primitives::AccountID;
use statichex::StaticHexInto;

#[derive(Debug, Default)]
pub struct TestExternalities {
	pub storage: HashMap<Vec<u8>, Vec<u8>>,
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

#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

pub fn one() -> AccountID {
	"2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee".convert()
}
pub fn two() -> AccountID {
	"d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a".convert()
}

pub struct HexDisplay<'a>(&'a [u8]);

impl<'a> HexDisplay<'a> {
	pub fn from(d: &'a AsBytesRef) -> Self { HexDisplay(d.as_bytes_ref()) }
}

impl<'a> ::std::fmt::Display for HexDisplay<'a> {
	fn fmt(&self, fmtr: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
		for byte in self.0 {
			try!( fmtr.write_fmt(format_args!("{:02x}", byte)));
		}
		Ok(())
	}
}

pub trait AsBytesRef {
	fn as_bytes_ref(&self) -> &[u8];
}

impl AsBytesRef for [u8] {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

impl<'a> AsBytesRef for &'a[u8] {
	fn as_bytes_ref(&self) -> &[u8] { self }
}

impl AsBytesRef for Vec<u8> {
	fn as_bytes_ref(&self) -> &[u8] { &self[..] }
}

macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl AsBytesRef for $t {
			fn as_bytes_ref(&self) -> &[u8] { &self[..] }
		}
	)* }
}

impl_non_endians!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);
