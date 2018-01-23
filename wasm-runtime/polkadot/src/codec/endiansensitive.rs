// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Endian manager.

/// Trait to allow conversion to a know endian representation when sensitive.
// note: the copy bound and static lifetimes are necessary for safety of `Slicable` blanket implementation.
pub trait EndianSensitive: Copy + 'static {
	fn to_le(self) -> Self { self }
	fn to_be(self) -> Self { self }
	fn from_le(self) -> Self { self }
	fn from_be(self) -> Self { self }
	fn as_be_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { f(&self) }
	fn as_le_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { f(&self) }
}

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {
			fn to_le(self) -> Self { <$t>::to_le(self) }
			fn to_be(self) -> Self { <$t>::to_be(self) }
			fn from_le(self) -> Self { <$t>::from_le(self) }
			fn from_be(self) -> Self { <$t>::from_be(self) }
			fn as_be_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { let d = self.to_be(); f(&d) }
			fn as_le_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { let d = self.to_le(); f(&d) }
		}
	)* }
}
macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {}
	)* }
}

// NOTE: See test to ensure correctness.
impl EndianSensitive for bool {}

impl_endians!(u16, u32, u64, usize, i16, i32, i64, isize);
impl_non_endians!(u8, i8, [u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);

#[cfg(test)]
mod tests {
	use super::EndianSensitive;

	#[test]
	fn endian_sensitive_is_copy() {
		fn _takes_copy<T: Copy>() { }
		fn _takes_endian_sensitive<T: EndianSensitive>() { _takes_copy::<T>() }
	}

	#[test]
	fn endian_sensitive_outlives_static() {
		fn _takes_static<T: 'static>() { }
		fn _takes_endian_sensitive<T: EndianSensitive>() { _takes_static::<T>() }
	}

	#[test]
	fn bool_is_not_endian_sensitive() {
		let b = true;
		assert_eq!(b.to_be(), b.to_le());
		let b = false;
		assert_eq!(b.to_be(), b.to_le());
	}
}
