// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{BoundedBTreeMap, BoundedBTreeSet, BoundedVec, WeakBoundedVec};
use sp_std::vec::Vec;

pub trait ScaleContainerType: private::Sealed {
	type Stored: codec::Decode;
}

impl<T: codec::Decode> ScaleContainerType for Vec<T> {
	type Stored = T;
}

impl<T: codec::Decode> ScaleContainerType for sp_std::collections::btree_set::BTreeSet<T> {
	type Stored = T;
}

impl<K: codec::Decode, V: codec::Decode> ScaleContainerType
	for sp_std::collections::btree_map::BTreeMap<K, V>
{
	type Stored = (K, V);
}

impl<T: codec::Decode, S> ScaleContainerType for BoundedVec<T, S> {
	type Stored = T;
}

impl<T: codec::Decode, S> ScaleContainerType for WeakBoundedVec<T, S> {
	type Stored = T;
}

impl<K: codec::Decode, V: codec::Decode, S> ScaleContainerType for BoundedBTreeMap<K, V, S> {
	type Stored = (K, V);
}

impl<T: codec::Decode, S> ScaleContainerType for BoundedBTreeSet<T, S> {
	type Stored = T;
}

mod private {
	use super::*;

	pub trait Sealed {}

	impl<T: codec::Decode> Sealed for Vec<T> {}
	impl<T: codec::Decode> Sealed for sp_std::collections::btree_set::BTreeSet<T> {}
	impl<K: codec::Decode, V: codec::Decode> Sealed for sp_std::collections::btree_map::BTreeMap<K, V> {}

	impl<T: codec::Decode, S> Sealed for BoundedVec<T, S> {}
	impl<T: codec::Decode, S> Sealed for WeakBoundedVec<T, S> {}
	impl<K: codec::Decode, V: codec::Decode, S> Sealed for BoundedBTreeMap<K, V, S> {}
	impl<T: codec::Decode, S> Sealed for BoundedBTreeSet<T, S> {}
}

pub trait StreamIter {
	type Iterator: sp_std::iter::Iterator;

	fn stream_iter() -> Self::Iterator;
}

impl<T: ScaleContainerType, StorageValue: super::generator::StorageValue<T>> StreamIter
	for StorageValue
{
	type Iterator = ScaleContainerStreamIter<T::Stored>;

	fn stream_iter() -> Self::Iterator {
		ScaleContainerStreamIter::new(Self::storage_value_final_key().into()).unwrap()
	}
}

pub struct ScaleContainerStreamIter<T> {
	marker: sp_std::marker::PhantomData<T>,
	input: StorageInput,
	length: u32,
	read: u32,
}

impl<T> ScaleContainerStreamIter<T> {
	pub fn new(key: Vec<u8>) -> Result<Self, codec::Error> {
		let mut input = StorageInput::new(key)?;
		let length = if input.exists { codec::Compact::<u32>::decode(&mut input)?.0 } else { 0 };

		Ok(Self { marker: sp_std::marker::PhantomData, input, length, read: 0 })
	}
}

impl<T: codec::Decode> sp_std::iter::Iterator for ScaleContainerStreamIter<T> {
	type Item = T;

	fn next(&mut self) -> Option<T> {
		if self.read >= self.length {
			None
		} else {
			self.read += 1;

			codec::Decode::decode(&mut self.input).ok()
		}
	}
}

impl<T: codec::Decode> StreamIter for Vec<T> {
	type Iterator = ScaleContainerStreamIter<T>;

	fn stream_iter(key: Vec<u8>) -> Self::Iterator {
		ScaleContainerStreamIter::new(key).unwrap()
	}
}

const STORAGE_INPUT_BUFFER_CAPACITY: usize = 16 * 1024;

pub struct StorageInput {
	key: Vec<u8>,
	offset: u32,
	total_length: u32,
	exists: bool,
	buffer: Vec<u8>,
	buffer_pos: usize,
}

impl StorageInput {
	pub fn new(key: Vec<u8>) -> Result<Self, codec::Error> {
		let mut buffer = Vec::with_capacity(STORAGE_INPUT_BUFFER_CAPACITY);
		unsafe {
			buffer.set_len(buffer.capacity());
		}

		let (total_length, exists) =
			if let Some(total_length) = sp_io::storage::read(&key, &mut buffer, 0) {
				(total_length, true)
			} else {
				(0, false)
			};

		if total_length < buffer.len() {
			unsafe {
				buffer.set_len(total_length as usize);
			}
		}

		Ok(Self { total_length, offset: 0, key, exists, buffer, buffer_pos: 0 })
	}

	fn fill_buffer(&mut self) -> Result<(), codec::Error> {
		self.buffer.copy_within(self.buffer_pos.., 0);
		self.buffer_pos = self.buffer.len() - self.buffer_pos;
		unsafe {
			self.buffer.set_len(self.buffer.capacity());
		}

		if let Some(after_offset) =
			sp_io::storage::read(&self.key, &mut self.buffer[self.buffer_pos..], self.offset)
		{
			let buffer_len = if (after_offset as usize) < self.buffer.len() - self.buffer_pos {
				after_offset as usize
			} else {
				self.buffer.len()
			};

			unsafe {
				self.buffer.set_len(buffer_len);
			}

			self.offset += buffer_len as u32;
			self.buffer_pos = 0;

			Ok(())
		} else {
			Err("Value doesn't exist in the state?".into())
		}
	}

	pub fn exists(&self) -> bool {
		self.exists
	}
}

impl codec::Input for StorageInput {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		Ok(Some(self.total_length.saturating_sub(self.buffer_pos as u32) as usize))
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		if into.len() > self.buffer.capacity() {
			let remaining_to_read = self.buffer.len() - self.buffer_pos;

			into[..remaining_to_read].copy_from_slice(&self.buffer[self.buffer_pos..]);
			unsafe {
				self.buffer.set_len(0);
			}
			self.buffer_pos = 0;

			if let Some(after_offset) =
				sp_io::storage::read(&self.key, &mut into[remaining_to_read..], self.offset)
			{
				let required_to_read = (into.len() - remaining_to_read) as u32;

				if after_offset < required_to_read {
					return Err("not enough data to fill the buffer".into())
				}

				self.offset += required_to_read;
				return Ok(())
			} else {
				return Err("Value doesn't exist in the state?".into())
			}
		} else if self.buffer_pos + into.len() >= self.buffer.len() &&
			self.offset < self.total_length
		{
			self.fill_buffer()?;
		} else if into.len() + self.buffer_pos > self.buffer.len() {
			return Err("not enough data to fill the buffer".into())
		}

		let end = self.buffer_pos + into.len();
		into.copy_from_slice(&self.buffer[self.buffer_pos..end]);
		self.buffer_pos = end;

		Ok(())
	}
}

#[test]
fn stream_read_test() {
	#[crate::storage_alias]
	pub type StreamReadTest = StorageValue<Test, Vec<u32>>;

	#[crate::storage_alias]
	pub type StreamReadTest2 = StorageValue<Test, Vec<Vec<u8>>>;

	sp_io::TestExternalities::default().execute_with(|| {
		let data: Vec<u32> = vec![1, 2, 3, 4, 5];
		StreamReadTest::put(&data);

		assert_eq!(data, StreamReadTest::stream().collect::<Vec<_>>());

		let data: Vec<Vec<u8>> = vec![vec![0; 3000], vec![1; 2500]];
		StreamReadTest2::put(&data);

		assert_eq!(data, StreamReadTest2::stream().collect::<Vec<_>>());
	})
}
