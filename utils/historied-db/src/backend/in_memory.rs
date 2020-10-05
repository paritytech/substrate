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

//! In memory backend structure.

use crate::historied::HistoriedValue;
use codec::{Encode, Decode, Input as CodecInput};
use super::{LinearStorage, LinearStorageMem};
use sp_std::mem::replace;
use crate::{Init, InitFrom};
use sp_std::vec::Vec;
use crate::backend::nodes::DecodeWithInit;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
const ALLOCATED_HISTORY: usize = 2;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MemoryOnly<V, S>(pub(crate) smallvec::SmallVec<[HistoriedValue<V, S>; ALLOCATED_HISTORY]>);


impl<V: Encode, S: Encode> Encode for MemoryOnly<V, S> {

	fn size_hint(&self) -> usize {
		self.0.as_slice().size_hint()
	}

	fn encode(&self) -> Vec<u8> {
		self.0.as_slice().encode()
	}

/*	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.0)
	}*/
}

impl<V: Decode, S: Decode> Decode for MemoryOnly<V, S> {
	fn decode<I: CodecInput>(value: &mut I) -> Result<Self, codec::Error> {
		// TODO make a variant when len < ALLOCATED_HISTORY
		let v = Vec::decode(value)?;
		Ok(MemoryOnly(smallvec::SmallVec::from_vec(v)))
	}
}

impl<V, S> DecodeWithInit for MemoryOnly<V, S>
	where
		V: DecodeWithInit,
		S: Decode,
{
	fn decode_with_init(mut input: &[u8], init: &Self::Init) -> Option<Self> {
		let input = &mut input;
		// this align on scale codec inner implementation (DecodeWithInit trait
		// could be a scale trait).
		<codec::Compact<u32>>::decode(input).ok().and_then(|len| {
			// TODO allocate with capacity
			let len = len.0 as usize;
			let mut result = smallvec::SmallVec::new();
			for _ in 0..len {
				if let Some(value) = HistoriedValue::decode_with_init(*input, init) {
					result.push(value);
				} else {
					return None;
				}
			}
			Some(MemoryOnly(result))
		})
	}
}

impl<V, S> Default for MemoryOnly<V, S> {
	fn default() -> Self {
		MemoryOnly(smallvec::SmallVec::default())
	}
}

impl<V: Clone, S: Clone> LinearStorageMem<V, S> for MemoryOnly<V, S> {
	fn get_ref(&self, index: Self::Index) -> HistoriedValue<&V, S> {
		let HistoriedValue { value, state } = &self.0[index];
		HistoriedValue { value: &value, state: state.clone() }
	}
	fn get_ref_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut V, S> {
		let state = self.0[index].state.clone();
		HistoriedValue { value: &mut self.0[index].value, state }
	}
}

impl<V: Init, S> Init for MemoryOnly<V, S> {
	type Init = V::Init;
}
impl<V, S> InitFrom for MemoryOnly<V, S> {
	fn init_from(_init: Self::Init) -> Self {
		Self::default()
	}
}

impl<V: Clone, S: Clone> LinearStorage<V, S> for MemoryOnly<V, S> {
	// Index position in array.
	type Index = usize;
	fn last(&self) -> Option<Self::Index> {
		if self.0.len() == 0 {
			None
		} else {
			Some(self.0.len() - 1)
		}
	}
	fn previous_index(&self, mut index: Self::Index) -> Option<Self::Index> {
		if index == 0 {
			None
		} else {
			index -= 1;
			Some(index)
		}
	}
	fn lookup(&self, index: usize) -> Option<Self::Index> {
		if index >= self.0.len() {
			None
		} else {
			Some(index)
		}
	}
	fn truncate_until(&mut self, split_off: usize) {
		if self.0.spilled() {
			let new = replace(&mut self.0, Default::default());
			self.0 = smallvec::SmallVec::from_vec(new.into_vec().split_off(split_off));
		} else {
			for i in 0..sp_std::cmp::min(split_off, self.0.len()) {
				self.0.remove(i);
			}
		}
	}
	fn len(&self) -> usize {
		self.0.len()
	}
	fn get(&self, index: Self::Index) -> HistoriedValue<V, S> {
		self.0[index].clone()
	}
	fn get_state(&self, index: Self::Index) -> S {
		self.0[index].state.clone()
	}
	fn push(&mut self, value: HistoriedValue<V, S>) {
		self.0.push(value)
	}
	fn insert(&mut self, index: Self::Index, value: HistoriedValue<V, S>) {
		self.0.insert(index, value)
	}
	fn remove(&mut self, index: Self::Index) {
		self.0.remove(index);
	}
	fn pop(&mut self) -> Option<HistoriedValue<V, S>> {
		self.0.pop()
	}
	fn clear(&mut self) {
		self.0.clear()
	}
	fn truncate(&mut self, at: usize) {
		self.0.truncate(at)
	}
	fn emplace(&mut self, index: Self::Index, value: HistoriedValue<V, S>) {
		self.0[index] = value;
	}
}

#[cfg(test)]
mod test {
	use crate::backend::test::{Value, State};
	use super::MemoryOnly;

	#[test]
	fn test_linear_storage() {
		let mut storage = MemoryOnly::<Value, State>::default();
		crate::backend::test::test_linear_storage(&mut storage);
	}
}
