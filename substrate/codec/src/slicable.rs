// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Serialisation.

use alloc::vec::Vec;
use alloc::boxed::Box;
use core::{mem, slice};
use super::joiner::Joiner;
use arrayvec::ArrayVec;

/// Trait that allows reading of data into a slice.
pub trait Input {
	/// Read into the provided input slice. Returns the number of bytes read.
	fn read(&mut self, into: &mut [u8]) -> usize;

	/// Read a single byte from the input.
	fn read_byte(&mut self) -> Option<u8> {
		let mut buf = [0u8];
		match self.read(&mut buf[..]) {
			0 => None,
			1 => Some(buf[0]),
			_ => unreachable!(),
		}
	}
}

impl<'a> Input for &'a [u8] {
	fn read(&mut self, into: &mut [u8]) -> usize {
		let len = ::core::cmp::min(into.len(), self.len());
		into[..len].copy_from_slice(&self[..len]);
		*self = &self[len..];
		len
	}
}

/// Trait that allows zero-copy read/write of value-references to/from slices in LE format.
pub trait Slicable: Sized {
	/// Attempt to deserialise the value from input.
	fn decode<I: Input>(value: &mut I) -> Option<Self>;

	/// Convert self to an owned vector.
	fn encode(&self) -> Vec<u8> {
		self.using_encoded(|s| s.to_vec())
	}

	/// Convert self to a slice and then invoke the given closure with it.
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.encode())
	}
}

impl<T: Slicable, E: Slicable> Slicable for Result<T, E> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			0 => Some(Ok(T::decode(input)?)),
			1 => Some(Err(E::decode(input)?)),
			_ => None,
		}
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Ok(ref t) => {
				v.push(0);
				t.using_encoded(|s| v.extend(s));
			}
			Err(ref e) => {
				v.push(1);
				e.using_encoded(|s| v.extend(s));
			}
		}
		v
	}
}

/// Shim type because we can't do a specialised implementation for `Option<bool>` directly.
pub struct OptionBool(pub Option<bool>);

impl Slicable for OptionBool {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			0 => Some(OptionBool(None)),
			1 => Some(OptionBool(Some(true))),
			2 => Some(OptionBool(Some(false))),
			_ => None,
		}
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[match *self {
			OptionBool(None) => 0u8,
			OptionBool(Some(true)) => 1u8,
			OptionBool(Some(false)) => 2u8,
		}])
	}
}

impl<T: Slicable> Slicable for Option<T> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			0 => Some(None),
			1 => Some(Some(T::decode(input)?)),
			_ => None,
		}
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Some(ref t) => {
				v.push(1);
				t.using_encoded(|s| v.extend(s));
			}
			None => v.push(0),
		}
		v
	}
}

macro_rules! impl_array {
	( $( $n:expr )* ) => { $(
		impl<T: Slicable> Slicable for [T; $n] {
			fn decode<I: Input>(input: &mut I) -> Option<Self> {
				let mut r = ArrayVec::new();
				for _ in 0..$n {
					r.push(T::decode(input)?);
				}
				r.into_inner().ok()
			}

			fn encode(&self) -> Vec<u8> {
				use core::iter::Extend;
				let mut r = Vec::new();
				for item in self.iter() {
					item.using_encoded(|e| r.extend(e));
				}
				r
			}
		}
	)* }
}

impl_array!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
	40 48 56 64 72 96 128 160 192 224 256);

impl<T: Slicable> Slicable for Box<T> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Box::new(T::decode(input)?))
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.as_ref().using_encoded(f)
	}
}

impl Slicable for Vec<u8> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		u32::decode(input).and_then(move |len| {
			let len = len as usize;
			let mut vec = vec![0; len];
			if input.read(&mut vec[..len]) != len {
				None
			} else {
				Some(vec)
			}
		})
	}

	fn encode(&self) -> Vec<u8> {
		let len = self.len();
		assert!(len <= u32::max_value() as usize, "Attempted to serialize vec with too many elements.");

		let mut r: Vec<u8> = Vec::new().and(&(len as u32));
		r.extend_from_slice(self);
		r
	}
}

impl<T: Slicable> Slicable for Vec<T> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		u32::decode(input).and_then(move |len| {
			let mut r = Vec::with_capacity(len as usize);
			for _ in 0..len {
				r.push(T::decode(input)?);
			}
			Some(r)
		})
	}

	fn encode(&self) -> Vec<u8> {
		use core::iter::Extend;

		let len = self.len();
		assert!(len <= u32::max_value() as usize, "Attempted to serialize vec with too many elements.");

		let mut r: Vec<u8> = Vec::new().and(&(len as u32));
		for item in self {
			item.using_encoded(|e| r.extend(e))
		}
		r
	}
}

impl Slicable for () {
	fn decode<I: Input>(_: &mut I) -> Option<()> {
		Some(())
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[])
	}

	fn encode(&self) -> Vec<u8> {
		Vec::new()
	}
}

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<$one: Slicable> Slicable for ($one,) {
			fn decode<I: Input>(input: &mut I) -> Option<Self> {
				match $one::decode(input) {
					None => None,
					Some($one) => Some(($one,)),
				}
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.0.using_encoded(f)
			}
		}


	};
	($first:ident, $($rest:ident,)+) => {
		impl<$first: Slicable, $($rest: Slicable),+>
		Slicable for
		($first, $($rest),+) {
			fn decode<INPUT: Input>(input: &mut INPUT) -> Option<Self> {
				Some((
					match $first::decode(input) {
						Some(x) => x,
						None => return None,
					},
					$(match $rest::decode(input) {
						Some(x) => x,
						None => return None,
					},)+
				))
			}

			fn using_encoded<RETURN, PROCESS>(&self, f: PROCESS) -> RETURN
				where PROCESS: FnOnce(&[u8]) -> RETURN
			{
				let mut v = Vec::new();

				let (
					ref $first,
					$(ref $rest),+
				) = *self;

				$first.using_encoded(|s| v.extend(s));
				$($rest.using_encoded(|s| v.extend(s));)+

				f(v.as_slice())
			}
		}

		tuple_impl!($($rest,)+);
	}
}

#[allow(non_snake_case)]
mod inner_tuple_impl {
	use alloc::vec::Vec;

	use super::{Input, Slicable};
	tuple_impl!(A, B, C, D, E, F, G, H, I, J, K,);
}

/// Trait to allow conversion to a know endian representation when sensitive.
/// Types implementing this trait must have a size > 0.
// note: the copy bound and static lifetimes are necessary for safety of `Slicable` blanket
// implementation.
trait EndianSensitive: Copy + 'static {
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

		impl Slicable for $t {
			fn decode<I: Input>(input: &mut I) -> Option<Self> {
				let size = mem::size_of::<$t>();
				assert!(size > 0, "EndianSensitive can never be implemented for a zero-sized type.");
				let mut val: $t = unsafe { mem::zeroed() };

				unsafe {
					let raw: &mut [u8] = slice::from_raw_parts_mut(
						&mut val as *mut $t as *mut u8,
						size
					);
					if input.read(raw) != size { return None }
				}
				Some(val.from_le())
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.as_le_then(|le| {
					let size = mem::size_of::<$t>();
					let value_slice = unsafe {
						let ptr = le as *const _ as *const u8;
						if size != 0 {
							slice::from_raw_parts(ptr, size)
						} else {
							&[]
						}
					};

					f(value_slice)
				})
			}
		}
	)* }
}
macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {}

		impl Slicable for $t {
			fn decode<I: Input>(input: &mut I) -> Option<Self> {
				let size = mem::size_of::<$t>();
				assert!(size > 0, "EndianSensitive can never be implemented for a zero-sized type.");
				let mut val: $t = unsafe { mem::zeroed() };

				unsafe {
					let raw: &mut [u8] = slice::from_raw_parts_mut(
						&mut val as *mut $t as *mut u8,
						size
					);
					if input.read(raw) != size { return None }
				}
				Some(val.from_le())
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.as_le_then(|le| {
					let size = mem::size_of::<$t>();
					let value_slice = unsafe {
						let ptr = le as *const _ as *const u8;
						if size != 0 {
							slice::from_raw_parts(ptr, size)
						} else {
							&[]
						}
					};

					f(value_slice)
				})
			}
		}
	)* }
}

impl_endians!(u16, u32, u64, u128, usize, i16, i32, i64, i128, isize);
impl_non_endians!(i8, [u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128], bool);


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn vec_is_slicable() {
		let v = b"Hello world".to_vec();
		v.using_encoded(|ref slice|
			assert_eq!(slice, &b"\x0b\0\0\0Hello world")
		);
	}
}
