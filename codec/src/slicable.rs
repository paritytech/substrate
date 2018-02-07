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
		u32::from_slice(value).and_then(move |len| {
			let len = len as usize;
			let mut r = Vec::with_capacity(len);
			for _ in 0..len {
				match T::from_slice(value) {
					None => return None,
					Some(v) => r.push(v),
				}
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
}
