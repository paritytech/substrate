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

use rstd::{mem, slice};
use rstd::vec::Vec;
use super::joiner::Joiner;
use super::endiansensitive::EndianSensitive;

/// Trait that allows zero-copy read/write of value-references to/from slices in LE format.
pub trait Slicable: Sized {
	/// Attempt to deserialise the value from a slice. Ignore trailing bytes and
	/// set the slice's start to just after the last byte consumed.
	///
	/// If `None` is returned, then the slice should be unmodified.
	fn from_slice(value: &mut &[u8]) -> Option<Self>;
	/// Convert self to an owned vector.
	fn to_vec(&self) -> Vec<u8> {
		self.as_slice_then(|s| s.to_vec())
	}
	/// Convert self to a slice and then invoke the given closure with it.
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R;
}

/// Trait to mark that a type is not trivially (essentially "in place") serialisable.
pub trait NonTrivialSlicable: Slicable {}

/// Attempt to decode a value from the slice, providing an initial value
/// to replace it with should it fail.
#[macro_export]
macro_rules! try_decode {
	($initial: expr, $current: expr) => {
		match $crate::Slicable::from_slice($current) {
			Some(x) => x,
			None => {
				*$current = $initial;
				return None;
			}
		}
	}
}

impl<T: EndianSensitive> Slicable for T {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		let size = mem::size_of::<T>();
		assert!(size > 0, "EndianSensitive can never be implemented for a zero-sized type.");
		if value.len() >= size {
			let x: T = unsafe { ::rstd::ptr::read(value.as_ptr() as *const T) };
			*value = &value[size..];
			Some(x.from_le())
		} else {
			None
		}
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.as_le_then(|le| {
			let size = mem::size_of::<T>();
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

impl Slicable for Vec<u8> {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		u32::from_slice(value).map(move |len| {
			let len = len as usize;
			let res = value[..len].to_vec();
			*value = &value[len..];
			res
		})
	}
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec())
	}

	fn to_vec(&self) -> Vec<u8> {
		let len = self.len();
		assert!(len <= u32::max_value() as usize, "Attempted to serialize vec with too many elements.");

		let mut r: Vec<u8> = Vec::new().join(&(len as u32));
		r.extend_from_slice(self);
		r
	}
}

impl<T: Slicable> NonTrivialSlicable for Vec<T> where Vec<T>: Slicable {}

impl<T: NonTrivialSlicable> Slicable for Vec<T> {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		let initial = *value;
		u32::from_slice(value).and_then(move |len| {
			let len = len as usize;
			let mut r = Vec::with_capacity(len);
			for _ in 0..len {
				r.push(try_decode!(initial, value))
			}

			Some(r)
		})
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec())
	}

	fn to_vec(&self) -> Vec<u8> {
		use rstd::iter::Extend;

		let len = self.len();
		assert!(len <= u32::max_value() as usize, "Attempted to serialize vec with too many elements.");

		let mut r: Vec<u8> = Vec::new().join(&(len as u32));
		for item in self {
			r.extend(item.to_vec());
		}
		r
	}
}

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<$one: Slicable> Slicable for ($one,) {
			fn from_slice(value: &mut &[u8]) -> Option<Self> {
				match $one::from_slice(value) {
					None => None,
					Some($one) => Some(($one,)),
				}
			}

			fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.0.as_slice_then(f)
			}
		}
	};
	($first:ident, $($rest:ident,)+) => {
		impl<$first: Slicable, $($rest: Slicable),+>
		Slicable for
		($first, $($rest),+) {
			fn from_slice(value: &mut &[u8]) -> Option<Self> {
				let initial = *value;
				Some((
					try_decode!(initial, value),
					$({
						let x: $rest = try_decode!(initial, value);
						x
					},)+
				))
			}

			fn as_slice_then<RETURN, PROCESS>(&self, f: PROCESS) -> RETURN
				where PROCESS: FnOnce(&[u8]) -> RETURN
			{
				let mut v = Vec::new();

				let (
					ref $first,
					$(ref $rest),+
				) = *self;

				$first.as_slice_then(|s| v.extend(s));
				$($rest.as_slice_then(|s| v.extend(s));)+

				f(v.as_slice())
			}
		}

		tuple_impl!($($rest,)+);
	}
}

#[allow(non_snake_case)]
mod inner_tuple_impl {
	use super::Slicable;
	tuple_impl!(A, B, C, D, E, F, G, H, I, J, K,);
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn vec_is_slicable() {
		let v = b"Hello world".to_vec();
		v.as_slice_then(|ref slice|
			assert_eq!(slice, &b"\x0b\0\0\0Hello world")
		);
	}

	#[test]
	fn failed_tuple_decode_does_not_munch() {
		let encoded = (vec![1u8, 3, 5, 9], 6u64).to_vec();
		let mut data = &encoded[..];
		assert!(<(Vec<u8>, u64, Vec<u8>)>::from_slice(&mut data).is_none());

		// failure to decode shouldn't munch anything.
		assert_eq!(data.len(), encoded.len());

		// full decoding should have munched everything.
		let decoded = <(Vec<u8>, u64)>::from_slice(&mut data).unwrap();
		assert!(data.is_empty());

		assert_eq!(decoded, (vec![1, 3, 5,9], 6));
	}
}
