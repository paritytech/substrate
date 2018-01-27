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

//! Serialisation.

use runtime_support::prelude::*;
use runtime_support::{mem, slice};
use joiner::Joiner;
use endiansensitive::EndianSensitive;

/// Trait that allows zero-copy read/write of value-references to/from slices in LE format.
pub trait Slicable: Sized {
	fn from_slice(value: &[u8]) -> Option<Self> {
		Self::set_as_slice(&|out, offset| if value.len() >= out.len() + offset {
			let value = &value[offset..];
			let len = out.len();
			out.copy_from_slice(&value[0..len]);
			true
		} else {
			false
		})
	}
	fn to_vec(&self) -> Vec<u8> {
		self.as_slice_then(|s| s.to_vec())
	}
	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(set_slice: &F) -> Option<Self>;
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec())
	}
	fn size_of(_value: &[u8]) -> Option<usize>;
}

/// Trait to mark that a type is not trivially (essentially "in place") serialisable.
pub trait NonTrivialSlicable: Slicable {}

impl<T: EndianSensitive> Slicable for T {
	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(fill_slice: &F) -> Option<Self> {
		let size = mem::size_of::<T>();
		let mut result: T = unsafe { mem::zeroed() };
		let result_slice = unsafe {
			let ptr = &mut result as *mut _ as *mut u8;
			slice::from_raw_parts_mut(ptr, size)
		};
		if fill_slice(result_slice, 0) {
			Some(result.from_le())
		} else {
			None
		}
	}
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		let size = mem::size_of::<Self>();
		self.as_le_then(|le| {
			let value_slice = unsafe {
				let ptr = le as *const _ as *const u8;
				slice::from_raw_parts(ptr, size)
			};
			f(value_slice)
		})
	}
	fn size_of(_value: &[u8]) -> Option<usize> {
		Some(mem::size_of::<Self>())
	}
}

impl Slicable for Vec<u8> {
	fn from_slice(value: &[u8]) -> Option<Self> {
		Some(value[4..].to_vec())
	}
	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(fill_slice: &F) -> Option<Self> {
		u32::set_as_slice(fill_slice).and_then(|len| {
			let mut v = Vec::with_capacity(len as usize);
			unsafe { v.set_len(len as usize); }
			if fill_slice(&mut v, 4) {
				Some(v)
			} else {
				None
			}
		})
	}
	fn to_vec(&self) -> Vec<u8> {
		let mut r: Vec<u8> = Vec::new().join(&(self.len() as u32));
		r.extend_from_slice(&self);
		r
	}
	fn size_of(data: &[u8]) -> Option<usize> {
		u32::from_slice(&data[0..4]).map(|i| (i + 4) as usize)
	}
}

impl<T: Slicable> NonTrivialSlicable for Vec<T> where Vec<T>: Slicable {}

impl<T: NonTrivialSlicable> Slicable for Vec<T> {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let len = Self::size_of(&value[0..4])?;
		let mut off = 4;
		let mut r = Vec::new();
		while off < len {
			let element_len = T::size_of(&value[off..])?;
			r.push(T::from_slice(&value[off..off + element_len])?);
			off += element_len;
		}
		Some(r)
	}

	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(_fill_slice: &F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		let vecs = self.iter().map(Slicable::to_vec).collect::<Vec<_>>();
		let len = vecs.iter().fold(0, |mut a, v| {a += v.len(); a});
		let mut r = Vec::new().join(&(len as u32));
		vecs.iter().for_each(|v| r.extend_from_slice(v));
		r
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		u32::from_slice(&data[0..4]).map(|i| (i + 4) as usize)
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
