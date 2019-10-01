// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Linear historied data.

#[cfg(not(feature = "std"))]
use rstd::{vec::Vec, vec};
use rstd::marker::PhantomData;
use rstd::borrow::Cow;
use crate::HistoriedValue;


/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(not(feature = "std"))]
pub(crate) type MemoryOnly<V, I> = Vec<HistoriedValue<V, I>>;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(feature = "std")]
pub(crate) type MemoryOnly<V, I> = smallvec::SmallVec<[HistoriedValue<V, I>; ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
#[cfg(feature = "std")]
const ALLOCATED_HISTORY: usize = 2;

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
/// Arraylike buffer with in place byte data.
/// Can be written as is in underlying
/// storage.
/// Could be use for direct access memory to.
pub struct Serialized<'a, F>(Cow<'a, [u8]>, PhantomData<F>);

/// Serialized specific behavior.
pub trait SerializedConfig {
	/// encoded empty slice
	fn empty() -> &'static [u8];
	/// size at start for encoding version.
	fn version_len() -> usize;
}
/// Serialize without versioning.
pub struct NoVersion;

/// Serialize with default verison
pub struct DefaultVersion;

impl SerializedConfig for NoVersion {
	fn empty() -> &'static [u8] {
		&EMPTY_SERIALIZED
	}
	fn version_len() -> usize {
		0
	}
}

impl SerializedConfig for DefaultVersion {
	fn empty() -> &'static [u8] {
		&DEFAULT_VERSION_EMPTY_SERIALIZED
	}
	fn version_len() -> usize {
		1
	}
}

// encoding size as u64
const SIZE_BYTE_LEN: usize = 8;

// Basis implementation to be on par with implementation using
// vec like container. Those method could be move to a trait
// implementation.
// Those function requires checked index.
impl<'a, F: SerializedConfig> Serialized<'a, F> {

	pub fn into_owned(self) -> Serialized<'static, F> {
    Serialized(Cow::from(self.0.into_owned()), PhantomData)
  }

	pub(crate) fn len(&self) -> usize {
		let len = self.0.len();
		self.read_le_usize(len - SIZE_BYTE_LEN) as usize
	}

	fn clear(&mut self) {
		self.write_le_usize(F::version_len(), 0);
		self.0.to_mut().truncate(F::version_len() + SIZE_BYTE_LEN);
	}

	#[cfg(test)]
	fn truncate(&mut self, index: usize) {
		if index == 0 {
			self.clear();
			return;
		}
		let len = self.len();
		if index >= len {
			return;
		}
		let start_ix = self.index_start();
		let new_start = self.index_element(index) as usize;
		let len_ix = index * SIZE_BYTE_LEN;
		self.slice_copy(start_ix, new_start, len_ix);
		self.write_le_usize(new_start + len_ix - SIZE_BYTE_LEN, index);
		self.0.to_mut().truncate(new_start + len_ix);
	}

	// index stay in truncated content
	pub(crate) fn truncate_start(&mut self, index: usize) {
		self.remove_range(0, index);
	}

	pub(crate) fn pop(&mut self) -> Option<HistoriedValue<Vec<u8>, u64>> {
		let len = self.len();
		if len == 0 {
			return None;
		}
		let start_ix = self.index_element(len - 1);
		let end_ix = self.index_start();
		let state = self.read_le_u64(start_ix);
		let value = self.0[start_ix + SIZE_BYTE_LEN..end_ix].to_vec();
		if len - 1 == 0 {
			self.clear();
			return Some(HistoriedValue { value, index: state })	
		} else {
			self.write_le_usize(self.0.len() - (SIZE_BYTE_LEN * 2), len - 1);
		};
		let ix_size = (len * SIZE_BYTE_LEN) - SIZE_BYTE_LEN;
		self.slice_copy(end_ix, start_ix, ix_size);
		self.0.to_mut().truncate(start_ix + ix_size);
		Some(HistoriedValue { value, index: state })
	}

	pub(crate) fn push(&mut self, val: HistoriedValue<&[u8], u64>) {
		let len = self.len();
		let start_ix = self.index_start();
		let end_ix = self.0.len();
		// A sized buffer and multiple index to avoid to big copy
		// should be use here.
		let mut new_ix = self.0[start_ix..end_ix].to_vec();
		// truncate here can be bad
		self.0.to_mut().truncate(start_ix + SIZE_BYTE_LEN);
		self.write_le_u64(start_ix, val.index);
		self.0.to_mut().extend_from_slice(val.value);
		self.0.to_mut().append(&mut new_ix);
		if len > 0 {
			self.write_le_usize(self.0.len() - SIZE_BYTE_LEN, start_ix);
			self.append_le_usize(len + 1);
		} else {
			self.write_le_usize(self.0.len() - SIZE_BYTE_LEN, 1);
		}
	}

	#[cfg(test)]
	fn remove(&mut self, index: usize) {
		self.remove_range(index, index + 1);
	}

	fn remove_range(&mut self, index: usize, end: usize) {
		let len = self.len();
		if len == 1 && index == 0 {
			self.clear();
			return;
		}
		// eager removal is costy, running some gc impl
		// can be interesting.
		let elt_start = self.index_element(index);
		let start_ix = self.index_start();
		let elt_end = if end == len {
			start_ix
		} else {
			self.index_element(end) 
		};
		let delete_size = elt_end - elt_start;
		for _ in elt_start..elt_end {
			let _ = self.0.to_mut().remove(elt_start);
		}
		let start_ix = start_ix - delete_size;
		for i in 1..len - index - 1 {
			let old_value = self.read_le_usize(start_ix + i * SIZE_BYTE_LEN);
			self.write_le_usize(start_ix + (i - 1) * SIZE_BYTE_LEN, old_value - delete_size);
		}
		let len = len - (end - index);
		let end_index = start_ix + len * SIZE_BYTE_LEN;
		self.write_le_usize(end_index - SIZE_BYTE_LEN, len);
		self.0.to_mut().truncate(end_index);

	}

	pub(crate) fn get_state(&self, index: usize) -> HistoriedValue<&[u8], u64> {
		let start_ix = self.index_element(index);
		let len = self.len();
		let end_ix = if index == len - 1 {
			self.index_start()
		} else {
			self.index_element(index + 1)
		};
		let state = self.read_le_u64(start_ix);
		HistoriedValue {
			value: &self.0[start_ix + SIZE_BYTE_LEN..end_ix],
			index: state,
		}
	}

}

const EMPTY_SERIALIZED: [u8; SIZE_BYTE_LEN] = [0u8; SIZE_BYTE_LEN];
const DEFAULT_VERSION: u8 = 1;
const DEFAULT_VERSION_EMPTY_SERIALIZED: [u8; SIZE_BYTE_LEN + 1] = {
	let mut buf = [0u8; SIZE_BYTE_LEN + 1];
	buf[0] = DEFAULT_VERSION;
	buf
};

impl<'a, F: SerializedConfig> Default for Serialized<'a, F> {
	fn default() -> Self {
		Serialized(Cow::Borrowed(F::empty()), PhantomData)
	}
}

// Utility function for basis implementation.
impl<'a, F: SerializedConfig> Serialized<'a, F> {
	
	// Index at end, also contains the encoded size
	fn index_start(&self) -> usize {
		let nb_ix = self.len();
		if nb_ix == 0 { return F::version_len(); }
		let end = self.0.len();
		end - (nb_ix * SIZE_BYTE_LEN)
	}

	fn index_element(&self, position: usize) -> usize {
		if position == 0 {
			return F::version_len();
		}
		let i = self.index_start() + (position - 1) * SIZE_BYTE_LEN;
		self.read_le_usize(i)
	}

	// move part of array that can overlap
	// This is a memory inefficient implementation.
	fn slice_copy(&mut self, start_from: usize, start_to: usize, size: usize) {
		let buffer = self.0[start_from..start_from + size].to_vec();
		self.0.to_mut()[start_to..start_to + size].copy_from_slice(&buffer[..]);
	}

	// Usize encoded as le u64 (for historied value).
	fn read_le_u64(&self, pos: usize) -> u64 {
		let mut buffer = [0u8; SIZE_BYTE_LEN];
		buffer.copy_from_slice(&self.0[pos..pos + SIZE_BYTE_LEN]);
		u64::from_le_bytes(buffer)
	}

	// Usize encoded as le u64 (only for internal indexing).
	// TODO EMCH change usize encoding to u32?
	fn read_le_usize(&self, pos: usize) -> usize {
		let mut buffer = [0u8; SIZE_BYTE_LEN];
		buffer.copy_from_slice(&self.0[pos..pos + SIZE_BYTE_LEN]);
		u64::from_le_bytes(buffer) as usize
	}

	// Usize encoded as le u64.
	fn write_le_usize(&mut self, pos: usize, value: usize) {
		let buffer = (value as u64).to_le_bytes();
		self.0.to_mut()[pos..pos + SIZE_BYTE_LEN].copy_from_slice(&buffer[..]);
	}

	// Usize encoded as le u64.
	fn append_le_usize(&mut self, value: usize) {
		let buffer = (value as u64).to_le_bytes();
		self.0.to_mut().extend_from_slice(&buffer[..]);
	}

	// Usize encoded as le u64.
	fn write_le_u64(&mut self, pos: usize, value: u64) {
		let buffer = (value as u64).to_le_bytes();
		self.0.to_mut()[pos..pos + SIZE_BYTE_LEN].copy_from_slice(&buffer[..]);
	}

}

#[cfg(test)]
mod test {
	use super::*;

	fn test_serialized_basis<F: SerializedConfig>(mut ser: Serialized<F>) {
		// test basis unsafe function similar to a simple vec
		// without index checking.
		let v1 = &b"val1"[..];
		let v2 = &b"value_2"[..];
		let v3 = &b"a third value 3"[..];

		assert_eq!(ser.len(), 0);
		assert_eq!(ser.pop(), None);
		ser.push((v1, 1).into());
		assert_eq!(ser.get_state(0), (v1, 1).into());
		assert_eq!(ser.pop(), Some((v1.to_vec(), 1).into()));
		assert_eq!(ser.len(), 0);
		ser.push((v1, 1).into());
		ser.push((v2, 2).into());
		ser.push((v3, 3).into());
		assert_eq!(ser.get_state(0), (v1, 1).into());
		assert_eq!(ser.get_state(1), (v2, 2).into());
		assert_eq!(ser.get_state(2), (v3, 3).into());
		assert_eq!(ser.pop(), Some((v3.to_vec(), 3).into()));
		assert_eq!(ser.len(), 2);
		ser.push((v3, 3).into());
		assert_eq!(ser.get_state(2), (v3, 3).into());
		ser.remove(0);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2, 2).into());
		assert_eq!(ser.get_state(1), (v3, 3).into());
		ser.push((v1, 1).into());
		ser.remove(1);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2, 2).into());
		assert_eq!(ser.get_state(1), (v1, 1).into());
		ser.push((v1, 1).into());
		ser.truncate(1);
		assert_eq!(ser.len(), 1);
		assert_eq!(ser.get_state(0), (v2, 2).into());
		ser.push((v1, 1).into());
		ser.push((v3, 3).into());
		ser.truncate_start(1);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v1, 1).into());
		assert_eq!(ser.get_state(1), (v3, 3).into());
		ser.push((v2, 2).into());
		ser.truncate_start(2);
		assert_eq!(ser.len(), 1);
		assert_eq!(ser.get_state(0), (v2, 2).into());

	}

	#[test]
	fn serialized_basis() {
		let ser1: Serialized<NoVersion> = Default::default();
		let ser2: Serialized<DefaultVersion> = Default::default();
		test_serialized_basis(ser1);
		test_serialized_basis(ser2);
	}
}
