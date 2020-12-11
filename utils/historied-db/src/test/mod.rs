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

//! Test module.

use codec::{Encode, Decode};


#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Encode, Decode)]
/// State Input (aka hash).
pub struct StateInput(pub u32);

pub type InMemoryMgmt = crate::management::tree::TreeManagement<StateInput, u32, u32, ()>;
pub type InMemoryMgmtSer = crate::management::tree::TreeManagement<StateInput, u32, u32, MappingTests>;

#[derive(Default)]
/// Mapping for test.
pub struct MappingTests;

mod bindings {
	macro_rules! static_instance {
		($name: ident, $col: expr) => {

		#[derive(Default, Clone)]
		pub struct $name;
		impl crate::mapped_db::MapInfo for $name {
			const STATIC_COL: &'static [u8] = $col;
		}
		
	}}
	macro_rules! static_instance_variable {
		($name: ident, $col: expr, $path: expr, $lazy: expr) => {
			static_instance!($name, $col);
			impl crate::mapped_db::VariableInfo for $name {
				const PATH: &'static [u8] = $path;
				const LAZY: bool = $lazy;
			}
	}}

	static_instance!(Mapping, &[0u8, 0, 0, 0]);
	static_instance!(TreeState, &[1u8, 0, 0, 0]);
	const CST: &'static[u8] = &[2u8, 0, 0, 0];
	static_instance!(JournalDelete, &[3u8, 0, 0, 0]);
	static_instance_variable!(LastIndex, CST, b"tree_mgmt/last_index", false);
	static_instance_variable!(NeutralElt,CST, b"tree_mgmt/neutral_elt", false);
	static_instance_variable!(TreeMeta, CST, b"tree_mgmt/tree_meta", true);
}

impl crate::management::tree::TreeManagementStorage for MappingTests {
	const JOURNAL_CHANGES: bool = true;
	type Storage = crate::test::InMemorySimpleDB5;
	type Mapping = bindings::Mapping;
	type JournalDelete = bindings::JournalDelete;
	type LastIndex = bindings::LastIndex;
	type NeutralElt = bindings::NeutralElt;
	type TreeMeta = bindings::TreeMeta;
	type TreeState = bindings::TreeState;
}

macro_rules! InMemSimpleDB {
	($name: ident, $size: expr, $inner_module: ident) => {

	pub use $inner_module::InMemory as $name;
	mod $inner_module {
		use crate::mapped_db::MappedDB;
		use sp_std::collections::btree_map::BTreeMap;
		const NB_COL: usize = $size;

		#[derive(Clone, Debug, Eq, PartialEq)]
		pub struct InMemory([BTreeMap<Vec<u8>, Vec<u8>>; NB_COL]);

		impl Default for InMemory {
			fn default() -> Self {
				InMemory::new()
			}
		}

		impl InMemory {
			pub fn new() -> Self {
				use core::mem::MaybeUninit;

				let mut inner: [MaybeUninit<BTreeMap<Vec<u8>, Vec<u8>>>; NB_COL] = unsafe {
					MaybeUninit::uninit().assume_init()
				};
				for elem in &mut inner[..] {
					*elem = MaybeUninit::new(BTreeMap::new());
				}
				let inner = unsafe { sp_std::mem::transmute(inner) };
				InMemory(inner)
			}

			pub fn resolve_collection(c: &'static [u8]) -> Option<usize> {
				if c.len() != 4 {
					return None;
				}
				let index = Self::resolve_collection_inner(c);
				if index < NB_COL {
					return Some(index);
				}
				None
			}
			// 0 is is invalid collection
			const fn resolve_collection_inner(c: &'static [u8]) -> usize {
				let mut buf = [0u8; 4];
				buf[0] = c[0];
				buf[1] = c[1];
				buf[2] = c[2];
				buf[3] = c[3];
				let index = u32::from_le_bytes(buf);
				index as usize
			}
		}

		impl MappedDB for InMemory {
			#[inline(always)]
			fn is_active(&self) -> bool {
				true
			}

			fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
				Self::resolve_collection(c).map(|ix| {
					self.0[ix].insert(k.to_vec(), v.to_vec())
				});
			}
			fn clear(&mut self, c: &'static [u8]) {
				Self::resolve_collection(c).map(|ix| {
					self.0[ix].clear();
				});
			}
			fn remove(&mut self, c: &'static [u8], k: &[u8]) {
				Self::resolve_collection(c).map(|ix| {
					self.0[ix].remove(k)
				});
			}
			fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
				Self::resolve_collection(c).and_then(|ix| {
					self.0[ix].get(k).cloned()
				})
			}

			fn iter<'a>(&'a self, c: &'static [u8]) -> crate::mapped_db::MappedDBIter<'a> {
				Box::new(if let Some(ix) = Self::resolve_collection(c) {
					self.0[ix].clone().into_iter()
				} else {
					BTreeMap::new().into_iter()
				})
			}

			fn contains_collection(&self, collection: &'static [u8]) -> bool {
				Self::resolve_collection(collection).is_some()
			}
		}
	}

	}
}

InMemSimpleDB!(InMemorySimpleDB5, 5, in_mem_5);
