// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Byte packed encoded array.
//! Can be use to replace an array and skip serializing
//! deserializing step for persistent storage.

// TODO parameterized u32 (historied value) state (put it in config).

// TODO next split between consecutive indexed values (replace write length by generic write meta)
// TODO next split consecutive with range indexing

use sp_std::marker::PhantomData;
use sp_std::borrow::Cow;
use sp_std::ops::Range;
use sp_std::vec::Vec;
use crate::historied::HistoriedValue;
use super::{LinearStorage, LinearStorageSlice, LinearStorageRange};
use codec::{Encode, Decode, Input as CodecInput};
use derivative::Derivative;
use crate::InitFrom;

#[derive(Derivative, Debug)]
#[cfg_attr(test, derivative(PartialEq(bound="")))]
/// Arraylike buffer with in place byte data.
/// Can be written as is in underlying
/// storage.
/// Could be use for direct access memory to.
pub struct EncodedArray<'a, V, F>(EncodedArrayBuff<'a>, PhantomData<(F, V)>);


impl<'a, V, F> crate::backend::nodes::EstimateSize for EncodedArray<'a, V, F> {
	fn estimate_size(&self) -> usize {
		self.0.len()
	}
}

impl<'a, V, F> Clone for EncodedArray<'a, V, F> {
	fn clone(&self) -> Self {
		EncodedArray(self.0.clone(), PhantomData)
	}
}

pub trait EncodedArrayValue: AsRef<[u8]> + AsMut<[u8]> + Sized {
	fn from_slice(slice: &[u8]) -> Self;
}

impl EncodedArrayValue for Vec<u8> {
	fn from_slice(slice: &[u8]) -> Self {
		slice.to_vec()
	}
}

impl<'a, V, F> EncodedArrayValue for EncodedArray<'a, V, F> {
	// TODO non ownd variant that is very tricky to do.
	fn from_slice(slice: &[u8]) -> Self {
		EncodedArray(EncodedArrayBuff::Cow(Cow::Owned(slice.to_vec())), PhantomData)
	}
}

impl<'a, V, F> AsRef<[u8]> for EncodedArray<'a, V, F> {
	fn as_ref(&self) -> &[u8] {
		use sp_std::ops::Deref;
		self.0.deref()
	}
}

impl<'a, V, F> AsMut<[u8]> for EncodedArray<'a, V, F> {
	fn as_mut(&mut self) -> &mut [u8] {
		use sp_std::ops::DerefMut;
		self.0.deref_mut()
	}
}

impl<'a, V, A> Encode for EncodedArray<'a, V, A> {

	fn size_hint(&self) -> usize {
		self.0.len() + 8
	}

	fn encode(&self) -> Vec<u8> {
		self.0.encode()
	}

/*	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.0)
	}*/
}


impl<'a, V, A> Decode for EncodedArray<'a, V, A> {
	fn decode<I: CodecInput>(value: &mut I) -> Result<Self, codec::Error> {
		let v: Vec<u8> = Vec::decode(value)?;
		let cow_value = Cow::Owned(v);
		Ok(EncodedArray(EncodedArrayBuff::Cow(cow_value), PhantomData))
	}
}

#[derive(Debug)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
enum EncodedArrayBuff<'a> {
	Cow(Cow<'a, [u8]>), // TODO consider remove Cow and add third variant
	Mut(&'a mut Vec<u8>),
}

impl<'a> EncodedArrayBuff<'a> {
	pub fn to_mut(&mut self) -> &mut Vec<u8> {
		match self {
			EncodedArrayBuff::Cow(c) => c.to_mut(),
			EncodedArrayBuff::Mut(m) => m,
		}
	}
	pub fn into_owned(self) -> Vec<u8> {
		match self {
			EncodedArrayBuff::Cow(c) => c.into_owned(),
			EncodedArrayBuff::Mut(m) => m.clone(),
		}
	}
}

impl<'a> sp_std::ops::Deref for EncodedArrayBuff<'a> {
	type Target = [u8];
	fn deref(&self) -> &Self::Target {
		match self {
			EncodedArrayBuff::Cow(c) => c.deref(),
			EncodedArrayBuff::Mut(m) => m.deref(),
		}
	}
}

impl<'a> sp_std::ops::DerefMut for EncodedArrayBuff<'a> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.to_mut()[..]
	}
}

impl<'a> Clone for EncodedArrayBuff<'a> {
	fn clone(&self) -> Self {
		match self {
			EncodedArrayBuff::Cow(c) => EncodedArrayBuff::Cow(c.clone()),
			EncodedArrayBuff::Mut(m) => {
				let m: Vec<u8> = (*m).clone();
				EncodedArrayBuff::Cow(Cow::Owned(m))
			}
		}
	}
}

/// EncodedArray specific behavior.
pub trait EncodedArrayConfig {
	/// encoded empty slice
	fn empty() -> &'static [u8];
	/// size at start for encoding version.
	fn version_len() -> usize;
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
/// Serialize without versioning.
pub struct NoVersion;

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
/// Serialize with default verison
pub struct DefaultVersion;

impl EncodedArrayConfig for NoVersion {
	fn empty() -> &'static [u8] {
		&EMPTY_SERIALIZED
	}
	fn version_len() -> usize {
		0
	}
}

impl EncodedArrayConfig for DefaultVersion {
	fn empty() -> &'static [u8] {
		&DEFAULT_VERSION_EMPTY_SERIALIZED
	}
	fn version_len() -> usize {
		1
	}
}

// encoding size as u32
const SIZE_BYTE_LEN: usize = 4;

// Basis implementation to be on par with implementation using
// vec like container. Those method could be move to a trait
// implementation.
// Those function requires checked index.
impl<'a, V, F: EncodedArrayConfig> EncodedArray<'a, V, F>
	where V: EncodedArrayValue {
	pub fn into_owned(self) -> EncodedArray<'static, V, F> {
    EncodedArray(EncodedArrayBuff::Cow(Cow::from(self.0.into_owned())), PhantomData)
  }

	pub fn into_vec(self) -> Vec<u8> {
    self.0.into_owned()
  }

	pub fn push_slice(&mut self, val: HistoriedValue<&[u8], u32>) {
		self.push_extra(val, &[])
	}

	/// variant of push where part of the value is in a second slice.
	pub(crate) fn push_extra(&mut self, val: HistoriedValue<&[u8], u32>, extra: &[u8]) {
		let len = self.len();
		let start_ix = self.index_start();
		let end_ix = self.0.len();
		// TODO EMCH use slice copy within after extend, no need for buffer!!!!
		let mut new_ix = self.0[start_ix..end_ix].to_vec();
		// truncate here can be bad
		self.0.to_mut().truncate(start_ix + SIZE_BYTE_LEN);
		self.write_le_u32(start_ix, val.state);
		self.0.to_mut().extend_from_slice(val.value);
		self.0.to_mut().extend_from_slice(extra);
		self.0.to_mut().append(&mut new_ix);
		if len > 0 {
			self.write_le_usize(self.0.len() - SIZE_BYTE_LEN, start_ix);
			self.append_le_usize(len + 1);
		} else {
			self.write_le_usize(self.0.len() - SIZE_BYTE_LEN, 1);
		}
	}

	fn remove_range(&mut self, index: usize, end: usize) {
		if end == 0 {
			return;
		}
		let len = self.len();
		if len <= end - index && index == 0 {
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

		let len = len - (end - index);
		for i in index..end {
			let pos = i + (end - index);
			if pos < len {
				let old_value = self.read_le_usize(start_ix + pos * SIZE_BYTE_LEN);
				self.write_le_usize(start_ix + i * SIZE_BYTE_LEN, old_value - delete_size);
			}
		}
		let end_index = start_ix + len * SIZE_BYTE_LEN;
		self.write_le_usize(end_index - SIZE_BYTE_LEN, len);
		self.0.to_mut().truncate(end_index);
	}

	fn get_range(&self, index: usize) -> (usize, usize, u32) {
		let start_ix = self.index_element(index);
		let len = self.len();
		let end_ix = if index == len - 1 {
			self.index_start()
		} else {
			self.index_element(index + 1)
		};
		let state = self.read_le_u32(start_ix);
		(start_ix, end_ix, state)

	}
	fn get_state(&self, index: usize) -> HistoriedValue<&[u8], u32> {
		let (start_ix, end_ix, state) = self.get_range(index);
		HistoriedValue {
			value: &self.0[start_ix + SIZE_BYTE_LEN..end_ix],
			state,
		}
	}
	fn get_state_mut(&mut self, index: usize) -> HistoriedValue<&mut [u8], u32> {
		let (start_ix, end_ix, state) = self.get_range(index);
		HistoriedValue {
			value: &mut self.0[start_ix + SIZE_BYTE_LEN..end_ix],
			state,
		}
	}
	fn get_state_only(&self, index: usize) -> u32 {
		let start_ix = self.index_element(index);
		self.read_le_u32(start_ix)
	}

}

const EMPTY_SERIALIZED: [u8; SIZE_BYTE_LEN] = [0u8; SIZE_BYTE_LEN];
const DEFAULT_VERSION: u8 = 1;
const DEFAULT_VERSION_EMPTY_SERIALIZED: [u8; SIZE_BYTE_LEN + 1] = {
	let mut buf = [0u8; SIZE_BYTE_LEN + 1];
	buf[0] = DEFAULT_VERSION;
	buf
};

impl<'a, V, F: EncodedArrayConfig> Default for EncodedArray<'a, V, F> {
	fn default() -> Self {
		EncodedArray(EncodedArrayBuff::Cow(Cow::Borrowed(F::empty())), PhantomData)
	}
}

impl<'a, V, F> Into<EncodedArray<'a, V, F>> for &'a[u8] {
	fn into(self) -> EncodedArray<'a, V, F> {
		EncodedArray(EncodedArrayBuff::Cow(Cow::Borrowed(self)), PhantomData)
	}
}

impl<V, F> Into<EncodedArray<'static, V, F>> for Vec<u8> {
	fn into(self) -> EncodedArray<'static, V, F> {
		EncodedArray(EncodedArrayBuff::Cow(Cow::Owned(self)), PhantomData)
	}
}

impl<'a, V, F> Into<EncodedArray<'a, V, F>> for &'a mut Vec<u8> {
	fn into(self) -> EncodedArray<'a, V, F> {
		EncodedArray(EncodedArrayBuff::Mut(self), PhantomData)
	}
}


// Utility function for basis implementation.
impl<'a, V, F: EncodedArrayConfig> EncodedArray<'a, V, F>
	where V: EncodedArrayValue {
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

	// Usize encoded as le u32 (for historied value).
	fn read_le_u32(&self, pos: usize) -> u32 {
		let mut buffer = [0u8; SIZE_BYTE_LEN];
		buffer.copy_from_slice(&self.0[pos..pos + SIZE_BYTE_LEN]);
		u32::from_le_bytes(buffer)
	}

	// Usize encoded as le u32 (only for internal indexing).
	fn read_le_usize(&self, pos: usize) -> usize {
		let mut buffer = [0u8; SIZE_BYTE_LEN];
		buffer.copy_from_slice(&self.0[pos..pos + SIZE_BYTE_LEN]);
		u32::from_le_bytes(buffer) as usize
	}

	// Usize encoded as le u32.
	fn write_le_usize(&mut self, pos: usize, value: usize) {
		let buffer = (value as u32).to_le_bytes();
		self.0.to_mut()[pos..pos + SIZE_BYTE_LEN].copy_from_slice(&buffer[..]);
	}

	// Usize encoded as le u32.
	fn append_le_usize(&mut self, value: usize) {
		let buffer = (value as u32).to_le_bytes();
		self.0.to_mut().extend_from_slice(&buffer[..]);
	}

	// Usize encoded as le u32.
	fn write_le_u32(&mut self, pos: usize, value: u32) {
		let buffer = (value as u32).to_le_bytes();
		self.0.to_mut()[pos..pos + SIZE_BYTE_LEN].copy_from_slice(&buffer[..]);
	}

}

impl<'a, F: EncodedArrayConfig, V> InitFrom for EncodedArray<'a, V, F>
{
	type Init = ();
	fn init_from(_init: Self::Init) -> Self {
		Self::default()
	}
}

impl<'a, F: EncodedArrayConfig, V> LinearStorage<V, u32> for EncodedArray<'a, V, F>
	where V: EncodedArrayValue,
{
	// Node index.
	type Index = usize;

	fn last(&self) -> Option<Self::Index> {
		let len = self.len();
		if len == 0 {
			return None;
		}
		Some(len - 1)
	}
	fn previous_index(&self, index: Self::Index) -> Option<Self::Index> {
		if index == 0 {
			return None;
		}
		Some(index)
	}
	fn lookup(&self, index: usize) -> Option<Self::Index> {
		let len = self.len();
		if index >= len {
			return None;
		}
		Some(index)
	}
	fn truncate_until(&mut self, split_off: usize) {
		self.remove_range(0, split_off);
	}

	fn len(&self) -> usize {
		let len = self.0.len();
		self.read_le_usize(len - SIZE_BYTE_LEN) as usize
	}

	fn get(&self, index: Self::Index) -> HistoriedValue<V, u32> {
		self.get_state(index).map(|v| V::from_slice(v.as_ref()))
	}
	fn get_state(&self, index: Self::Index) -> u32 {
		self.get_state_only(index)
	}
	//fn push(&mut self, value: HistoriedValue<&'a[u8], u32>) {
	fn push(&mut self, value: HistoriedValue<V, u32>) {
		let val = value.map_ref(|v| v.as_ref());
		self.push_extra(val, &[])
	}

	//fn pop(&mut self) -> Option<HistoriedValue<&'a[u8], u32>> {
	fn pop(&mut self) -> Option<HistoriedValue<V, u32>> {
		let len = self.len();
		if len == 0 {
			return None;
		}
		let start_ix = self.index_element(len - 1);
		let end_ix = self.index_start();
		let state = self.read_le_u32(start_ix);
		let value = V::from_slice(&self.0[start_ix + SIZE_BYTE_LEN..end_ix]);
		if len - 1 == 0 {
			self.clear();
			return Some(HistoriedValue { value, state })	
		} else {
			self.write_le_usize(self.0.len() - (SIZE_BYTE_LEN * 2), len - 1);
		};
		let ix_size = (len * SIZE_BYTE_LEN) - SIZE_BYTE_LEN;
		self.slice_copy(end_ix, start_ix, ix_size);
		self.0.to_mut().truncate(start_ix + ix_size);
		Some(HistoriedValue { value, state })
	}

	fn clear(&mut self) {
		self.write_le_usize(F::version_len(), 0);
		self.0.to_mut().truncate(F::version_len() + SIZE_BYTE_LEN);
	}

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

	fn emplace(&mut self, index: Self::Index, value: HistoriedValue<V, u32>) {
		let len = self.len();
		debug_assert!(len > index);
		let elt_start = self.index_element(index);
		let start_ix = self.index_start();
		let elt_end = if len == index + 1{
			start_ix
		} else {
			self.index_element(index + 1) 
		};
		let previous_size = elt_end - elt_start - SIZE_BYTE_LEN;
		if previous_size == value.value.as_ref().len() {
			self.write_le_u32(elt_start, value.state);
			self.0[elt_start + SIZE_BYTE_LEN..elt_end].copy_from_slice(value.value.as_ref());
			return;
		}

		let end_ix = self.0.len();
		if previous_size > value.value.as_ref().len() {
			let delete_size = previous_size - value.value.as_ref().len();
			let new_elt_end = elt_end - delete_size; // TODO this var is awkward
			self.write_le_u32(elt_start, value.state);
			self.0[elt_start + SIZE_BYTE_LEN..new_elt_end].copy_from_slice(value.value.as_ref());
			for _ in 0..delete_size {
				let _ = self.0.to_mut().remove(new_elt_end);
			}
			let start_ix = start_ix - delete_size;
			for pos in index..len - 1 {
				let old_value = self.read_le_usize(start_ix + pos * SIZE_BYTE_LEN);
				self.write_le_usize(start_ix + pos * SIZE_BYTE_LEN, old_value - delete_size);
			}
		} else {
			let additional_size = value.value.as_ref().len() - previous_size;
			let new_len = end_ix + additional_size;
			self.0.to_mut().resize(new_len, 0);
			let new_elt_end = elt_end + additional_size;
			self.0.copy_within(elt_end..end_ix, new_elt_end);
			self.write_le_u32(elt_start, value.state);
			self.0[elt_start + SIZE_BYTE_LEN..new_elt_end].copy_from_slice(value.value.as_ref());
			let start_ix = start_ix + additional_size;
			for pos in index..len - 1 {
				let old_value = self.read_le_usize(start_ix + pos * SIZE_BYTE_LEN);
				self.write_le_usize(start_ix + pos * SIZE_BYTE_LEN, old_value + additional_size);
			}
		}
	}

	fn insert(&mut self, index: usize, value: HistoriedValue<V, u32>) {
		let len = self.len();
		debug_assert!(len >= index);
		let end_ix = self.0.len();
		let start_ix = self.index_start();
		let elt_start = self.index_element(index);
		let additional_size = value.value.as_ref().len() + SIZE_BYTE_LEN;
		let elt_end = elt_start + additional_size;

		let new_len = end_ix + additional_size + if len != 0 { SIZE_BYTE_LEN } else { 0 };
		self.0.to_mut().resize(new_len, 0);
		self.0.copy_within(elt_start..end_ix, elt_end);
		self.write_le_u32(elt_start, value.state);
		self.0[elt_start + SIZE_BYTE_LEN..elt_end].copy_from_slice(value.value.as_ref());
		let start_ix = start_ix + additional_size;
		let mut old_value = elt_end;
		for pos in index..len {
			let tmp = self.read_le_usize(start_ix + pos * SIZE_BYTE_LEN);
			self.write_le_usize(start_ix + pos * SIZE_BYTE_LEN, old_value);
			old_value = tmp + additional_size;
		}
		self.write_le_usize(self.0.len() - SIZE_BYTE_LEN, len + 1);
	}
	fn remove(&mut self, index: Self::Index) {
		self.remove_range(index, index + 1);
	}
}

impl<'a, F: EncodedArrayConfig, V> LinearStorageSlice<V, u32> for EncodedArray<'a, V, F>
	where V: EncodedArrayValue,
{
	fn get_slice(&self, index: Self::Index) -> HistoriedValue<&[u8], u32> {
		self.get_state(index)
	}
	fn get_slice_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut [u8], u32> {
		self.get_state_mut(index)
	}
}

impl<'a, F: EncodedArrayConfig, V> LinearStorageRange<V, u32> for EncodedArray<'a, V, F>
	where V: EncodedArrayValue,
{
	fn get_range(&self, index: Self::Index) -> HistoriedValue<Range<usize>, u32> {
		let (start, end, state) = self.get_range(index);
		HistoriedValue {
			state,
			value: start..end,
		}
	}
	fn from_slice(slice: &[u8]) -> Option<Self> {
		Some(<Self as EncodedArrayValue>::from_slice(slice))
	}
}

#[cfg(test)]
mod test {
	use super::*;

	fn test_serialized_basis<F: EncodedArrayConfig>(mut ser: EncodedArray<Vec<u8>, F>) {
		// test basis unsafe function similar to a simple vec
		// without index checking.
		let v1ref = &b"val1"[..];
		let v2ref = &b"value_2"[..];
		let v3ref = &b"a third value 3"[..];
		let v1 = b"val1".to_vec();
		let v2 = b"value_2".to_vec();
		let v3 = b"a third value 3".to_vec();



		assert_eq!(ser.len(), 0);
		assert_eq!(ser.pop(), None);
		ser.push((v1.clone(), 1).into());
		assert_eq!(ser.get_state(0), (v1ref, 1).into());
		assert_eq!(ser.pop(), Some((v1.clone().to_vec(), 1).into()));
		assert_eq!(ser.len(), 0);
		ser.push((v1.clone(), 1).into());
		ser.push((v2.clone(), 2).into());
		ser.push((v3.clone(), 3).into());
		assert_eq!(ser.get_state(0), (v1ref, 1).into());
		assert_eq!(ser.get_state(1), (v2ref, 2).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		assert_eq!(ser.pop(), Some((v3ref.to_vec(), 3).into()));
		assert_eq!(ser.len(), 2);
		ser.push((v3.clone(), 3).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		ser.remove(0);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
		assert_eq!(ser.get_state(1), (v3ref, 3).into());
		ser.push((v1.clone(), 1).into());
		ser.remove(1);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
		assert_eq!(ser.get_state(1), (v1ref, 1).into());
		ser.push((v1.clone(), 1).into());
		ser.truncate(1);
		assert_eq!(ser.len(), 1);
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
		ser.push((v1.clone(), 1).into());
		ser.push((v3.clone(), 3).into());
		ser.truncate_until(1);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v1ref, 1).into());
		assert_eq!(ser.get_state(1), (v3ref, 3).into());
		ser.push((v2.clone(), 2).into());
		ser.truncate_until(2);
		assert_eq!(ser.len(), 1);
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
	}

	fn test_serialized_emplace<F: EncodedArrayConfig>(mut ser: EncodedArray<Vec<u8>, F>) {
		// test basis unsafe function similar to a simple vec
		// without index checking.
		let v1ref = &b"val1"[..];
		let v2ref = &b"value_2"[..];
		let v3ref = &b"a third value 3"[..];
		let v1 = b"val1".to_vec();
		let v2 = b"value_2".to_vec();
		let v3 = b"a third value 3".to_vec();

		ser.push((v1.clone(), 1).into());
		ser.push((v2.clone(), 2).into());
		ser.push((v3.clone(), 3).into());
		
		ser.emplace_lookup(0, (v3.clone(), 4).into());
		assert_eq!(ser.get_state(0), (v3ref, 4).into());
		assert_eq!(ser.get_state(1), (v2ref, 2).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		ser.emplace_lookup(0, (v2.clone(), 5).into());
		assert_eq!(ser.get_state(0), (v2ref, 5).into());
		assert_eq!(ser.get_state(1), (v2ref, 2).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		ser.emplace_lookup(1, (v3.clone(), 6).into());
		assert_eq!(ser.get_state(0), (v2ref, 5).into());
		assert_eq!(ser.get_state(1), (v3ref, 6).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		ser.emplace_lookup(1, (v1.clone(), 7).into());
		assert_eq!(ser.get_state(0), (v2ref, 5).into());
		assert_eq!(ser.get_state(1), (v1ref, 7).into());
		assert_eq!(ser.get_state(2), (v3ref, 3).into());
		ser.emplace_lookup(2, (v1.clone(), 8).into());
		assert_eq!(ser.get_state(0), (v2ref, 5).into());
		assert_eq!(ser.get_state(1), (v1ref, 7).into());
		assert_eq!(ser.get_state(2), (v1ref, 8).into());
		ser.emplace_lookup(2, (v2.clone(), 9).into());
		assert_eq!(ser.get_state(0), (v2ref, 5).into());
		assert_eq!(ser.get_state(1), (v1ref, 7).into());
		assert_eq!(ser.get_state(2), (v2ref, 9).into());
	}

	fn test_serialized_insert_remove<F: EncodedArrayConfig>(mut ser: EncodedArray<Vec<u8>, F>) {
		// test basis unsafe function similar to a simple vec
		// without index checking.
		let v1ref = &b"val1"[..];
		let v2ref = &b"value_2"[..];
		let v3ref = &b"a third value 3"[..];
		let v1 = b"val1".to_vec();
		let v2 = b"value_2".to_vec();
		let v3 = b"a third value 3".to_vec();

		ser.insert_lookup(0, (v1.clone(), 1).into());
		ser.insert_lookup(0, (v2.clone(), 2).into());
		ser.insert_lookup(1, (v3.clone(), 3).into());
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
		assert_eq!(ser.get_state(1), (v3ref, 3).into());
		assert_eq!(ser.get_state(2), (v1ref, 1).into());
		assert_eq!(ser.len(), 3);
		ser.remove(1);
		ser.insert_lookup(1, (v2.clone(), 1).into());
		assert_eq!(ser.get_state(0), (v2ref, 2).into());
		assert_eq!(ser.get_state(1), (v2ref, 1).into());
		assert_eq!(ser.get_state(2), (v1ref, 1).into());
		assert_eq!(ser.len(), 3);
		ser.remove(0);
		assert_eq!(ser.get_state(0), (v2ref, 1).into());
		assert_eq!(ser.get_state(1), (v1ref, 1).into());
		assert_eq!(ser.len(), 2);
		ser.remove(1);
		assert_eq!(ser.get_state(0), (v2ref, 1).into());
		assert_eq!(ser.len(), 1);
		ser.remove(0);
		assert_eq!(ser.len(), 0);
	}

	#[test]
	fn serialized_basis() {
		let ser1: EncodedArray<Vec<u8>, NoVersion> = Default::default();
		let ser2: EncodedArray<Vec<u8>, DefaultVersion> = Default::default();
		test_serialized_basis(ser1);
		test_serialized_basis(ser2);
	}

	#[test]
	fn serialized_emplpace() {
		let ser1: EncodedArray<Vec<u8>, NoVersion> = Default::default();
		let ser2: EncodedArray<Vec<u8>, DefaultVersion> = Default::default();
		test_serialized_emplace(ser1);
		test_serialized_emplace(ser2);
	}

	#[test]
	fn serialized_insert_remove() {
		let ser1: EncodedArray<Vec<u8>, NoVersion> = Default::default();
		let ser2: EncodedArray<Vec<u8>, DefaultVersion> = Default::default();
		test_serialized_insert_remove(ser1);
		test_serialized_insert_remove(ser2);
	}

	#[test]
	fn test_linear_storage() {
		let mut ser1: EncodedArray<Vec<u8>, NoVersion> = Default::default();
		crate::backend::test::test_linear_storage(&mut ser1);
		let mut ser2: EncodedArray<Vec<u8>, DefaultVersion> = Default::default();
		crate::backend::test::test_linear_storage(&mut ser2);
	}

/*
	// TODO rename to gc and activate when implementation
	// similar to in memory in linear.rs is added to EncodedArray. 
	#[test]
	fn test_prune() {
		let mut item: EncodedArray<NoVersion> = Default::default();
		// setting value respecting branch build order
		for i in 1..6 {
			item.push(i, Some(&[i as u8]));
		}

		for a in 1..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}
		item.prune(1);
		assert_eq!(item.get(1), None);
		for a in 2..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}

		item.prune(4);
		for a in 1..5 {
			assert_eq!(item.get(a), None);
		}
		for a in 5..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}

		item.prune(80);
		for a in 1..4 {
			assert_eq!(item.get(a), None);
		}
		// pruning preserve last valid value
		for a in 5..11 {
			assert_eq!(item.get(a), Some(Some(&[5 as u8][..])));
		}

		// prune skip unrelevant delete
		let mut item: EncodedArray<NoVersion> = Default::default();
		item.push(1, Some(&[1 as u8]));
		item.push(2, None);
		item.push(3, Some(&[3 as u8]));
		assert_eq!(item.get(1), Some(Some(&[1][..])));
		assert_eq!(item.get(2), Some(None));
		assert_eq!(item.get(3), Some(Some(&[3][..])));
		assert_eq!(item.0.len(), 3);
		item.prune(1);
		assert_eq!(item.0.len(), 1);
		assert_eq!(item.get(1), None);
		assert_eq!(item.get(2), None);
		assert_eq!(item.get(3), Some(Some(&[3][..])));

		// prune skip unrelevant delete
		let mut item: EncodedArray<NoVersion> = Default::default();
		item.push(1, Some(&[1 as u8]));
		item.push(3, None);
		item.push(4, Some(&[4 as u8]));
		assert_eq!(item.get(1), Some(Some(&[1][..])));
		assert_eq!(item.get(2), Some(Some(&[1][..])));
		assert_eq!(item.get(3), Some(None));
		assert_eq!(item.get(4), Some(Some(&[4][..])));
		assert_eq!(item.0.len(), 3);
		// 1 needed for state two
		assert_eq!(PruneResult::Unchanged, item.prune(1));
		// 3 unneeded
		item.prune(2);
		assert_eq!(item.0.len(), 1);
		assert_eq!(item.get(1), None);
		assert_eq!(item.get(2), None);
		assert_eq!(item.get(3), None);
		assert_eq!(item.get(4), Some(Some(&[4][..])));

		// prune delete at block
		let mut item: EncodedArray<DefaultVersion> = Default::default();
		item.push(0, Some(&[0 as u8]));
		item.push(1, None);
		assert_eq!(item.get(0), Some(Some(&[0][..])));
		assert_eq!(item.get(1), Some(None));
		item.prune(0);
		assert_eq!(item.get(0), None);
		assert_eq!(item.get(1), None);
		assert_eq!(item.0.len(), 0);
	}
*/
}
