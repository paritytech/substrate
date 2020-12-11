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
use codec::{Encode, Decode, Input as Input};
use super::{LinearStorage, LinearStorageMem};
use sp_std::mem::replace;
use crate::{Context, InitFrom, DecodeWithContext, Trigger};
use sp_std::vec::Vec;

macro_rules! memory_only_stack_size {
	($memory_only: ident, $allocated_history: expr) => {

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct $memory_only<V, S>(pub(crate) smallvec::SmallVec<[HistoriedValue<V, S>; $allocated_history]>);


impl<V: Encode, S: Encode> Encode for $memory_only<V, S> {
	fn size_hint(&self) -> usize {
		self.0.as_slice().size_hint()
	}

	fn encode(&self) -> Vec<u8> {
		self.0.as_slice().encode()
	}
}

impl<V: Decode, S: Decode> Decode for $memory_only<V, S> {
	fn decode<I: Input>(value: &mut I) -> Result<Self, codec::Error> {
		// Note that we always decode on heap.
		let v = Vec::decode(value)?;
		Ok($memory_only(smallvec::SmallVec::from_vec(v)))
	}
}

impl<V, S> DecodeWithContext for $memory_only<V, S>
	where
		V: DecodeWithContext,
		S: Decode,
{
	fn decode_with_context<I: Input>(input: &mut I, init: &Self::Context) -> Option<Self> {
		// this align on scale codec inner implementation (DecodeWithContext trait
		// could be a scale trait).
		<codec::Compact<u32>>::decode(input).ok().and_then(|len| {
			let len = len.0 as usize;
			let mut result = smallvec::SmallVec::with_capacity(len);
			for _ in 0..len {
				if let Some(value) = HistoriedValue::decode_with_context(input, init) {
					result.push(value);
				} else {
					return None;
				}
			}
			Some($memory_only(result))
		})
	}
}

impl<V, S> Default for $memory_only<V, S> {
	fn default() -> Self {
		$memory_only(smallvec::SmallVec::default())
	}
}

impl<V: Clone + Context, S: Clone> LinearStorageMem<V, S> for $memory_only<V, S> {
	fn get_ref(&self, index: Self::Index) -> HistoriedValue<&V, S> {
		let HistoriedValue { value, state } = &self.0[index as usize];
		HistoriedValue { value: &value, state: state.clone() }
	}
	fn get_ref_mut(&mut self, index: Self::Index) -> HistoriedValue<&mut V, S> {
		let state = self.0[index as usize].state.clone();
		HistoriedValue { value: &mut self.0[index as usize].value, state }
	}
}

impl<V: Clone + Context + Trigger, S: Clone> Trigger for $memory_only<V, S> {
	const TRIGGER: bool = <V as Trigger>::TRIGGER;

	fn trigger_flush(&mut self) {
		if Self::TRIGGER {
			for i in 0 .. self.len() {
				self.get_ref_mut(i as u64).as_mut().value.trigger_flush()
			}
		}
	}
}

impl<V: Context, S> Context for $memory_only<V, S> {
	type Context = V::Context;
}

impl<V: Context, S> InitFrom for $memory_only<V, S> {
	fn init_from(_init: Self::Context) -> Self {
		Self::default()
	}
}

impl<V: Clone + Context, S: Clone> LinearStorage<V, S> for $memory_only<V, S> {
	// Index position in array.
	type Index = u64;
	fn last(&self) -> Option<Self::Index> {
		if self.0.len() == 0 {
			None
		} else {
			Some((self.0.len() - 1) as u64)
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
			Some(index as u64)
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
		self.0[index as usize].clone()
	}
	fn get_state(&self, index: Self::Index) -> S {
		self.0[index as usize].state.clone()
	}
	fn push(&mut self, value: HistoriedValue<V, S>) {
		self.0.push(value)
	}
	fn insert(&mut self, index: Self::Index, value: HistoriedValue<V, S>) {
		self.0.insert(index as usize, value)
	}
	fn remove(&mut self, index: Self::Index) {
		self.0.remove(index as usize);
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
		self.0[index as usize] = value;
	}
}

}}

memory_only_stack_size!(MemoryOnly, 2);
memory_only_stack_size!(MemoryOnly4, 4);
memory_only_stack_size!(MemoryOnly8, 8);
memory_only_stack_size!(MemoryOnly16, 16);
memory_only_stack_size!(MemoryOnly32, 32);
memory_only_stack_size!(MemoryOnly64, 64);

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
