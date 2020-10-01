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

//! Fuzz code for external fuzzer. Managing it in the
//! project allow to run non regression test over previously
//! problematic fuzzer inputs.

use crate::{
	Management, StateDB, ForkableManagement, ManagementRef, StateDBRef,
	historied::Value,
};
use crate::test::simple_impl::StateInput;

pub type InMemoryMgmt = crate::management::tree::TreeManagement<StateInput, u32, u32, u16, ()>;
pub type InMemoryMgmtSer = crate::management::tree::TreeManagement<StateInput, u32, u32, u16, SerFuzz>;

/// Serialize for fuzzer.
pub struct SerFuzz;

mod bindings {
	macro_rules! static_instance {
		($name: ident, $col: expr) => {

		#[derive(Default, Clone)]
		pub struct $name;
		impl crate::simple_db::SerializeInstanceMap for $name {
			const STATIC_COL: &'static [u8] = $col;
		}
		
	}}
	macro_rules! static_instance_variable {
		($name: ident, $col: expr, $path: expr, $lazy: expr) => {
			static_instance!($name, $col);
			impl crate::simple_db::SerializeInstanceVariable for $name {
				const PATH: &'static [u8] = $path;
				const LAZY: bool = $lazy;
			}
	}}

	static_instance!(Mapping, &[0u8, 0, 0, 0]);
	static_instance!(TreeState, &[1u8, 0, 0, 0]);
	const CST: &'static[u8] = &[2u8, 0, 0, 0];
	static_instance!(JournalDelete, &[3u8, 0, 0, 0]);
	static_instance_variable!(TouchedGC, CST, b"tree_mgmt/touched_gc", false);
	static_instance_variable!(CurrentGC, CST, b"tree_mgmt/current_gc", false);
	static_instance_variable!(LastIndex, CST, b"tree_mgmt/last_index", false);
	static_instance_variable!(NeutralElt,CST, b"tree_mgmt/neutral_elt", false);
	static_instance_variable!(TreeMeta, CST, b"tree_mgmt/tree_meta", true);
}

impl crate::management::tree::TreeManagementStorage for SerFuzz {
	const JOURNAL_DELETE: bool = true;
	type Storage = crate::test::InMemorySimpleDB5;
	type Mapping = bindings::Mapping;
	type JournalDelete = bindings::JournalDelete;
	type TouchedGC = bindings::TouchedGC;
	type CurrentGC = bindings::CurrentGC;
	type LastIndex = bindings::LastIndex;
	type NeutralElt = bindings::NeutralElt;
	type TreeMeta = bindings::TreeMeta;
	type TreeState = bindings::TreeState;

	fn init() -> Self::Storage {
		crate::test::InMemorySimpleDB5::new()
	}
}

type LinearBackend = crate::backend::in_memory::MemoryOnly<u16, u32>;
type TreeBackend = crate::backend::in_memory::MemoryOnly<
	crate::historied::linear::Linear<u16, u32, LinearBackend>,
	u32,
>;
struct FuzzerState {
	/// in memory historied datas to test
	in_memory_db: crate::historied::BTreeMap<
		Vec<u8>, u16,
		crate::historied::tree::Tree<u32, u32, u16, TreeBackend, LinearBackend>,
	>,
	/// in memory state management
	in_memory_mgmt: InMemoryMgmt,
	/// in memory state management with serialize
	in_memory_mgmt_ser: InMemoryMgmtSer,
	/// shall we test serialize
	with_ser: bool,
	/// simple reference
	simple: crate::test::simple_impl::Db<Vec<u8>, u16>, 
	/// limit of state to u8, hash from 1 to 255 are valid.
	next_hash: u8, // TODO rename next state
}

impl FuzzerState {
	fn new() -> Self {
		let mut in_memory_mgmt = InMemoryMgmt::default();
		let mut in_memory_mgmt_ser = InMemoryMgmtSer::default();
		in_memory_mgmt.map_root_state(StateInput(0));
		in_memory_mgmt_ser.map_root_state(StateInput(0));
		FuzzerState {
			in_memory_db: crate::historied::BTreeMap::new(((), ())),
			in_memory_mgmt,
			in_memory_mgmt_ser,
			with_ser: false,
			simple: crate::test::simple_impl::Db::init().0,
			next_hash: 1,
		}
	}

	fn apply(&mut self, action: FuzzerAction) {
		match action {
			FuzzerAction::SetValueLatest(key, value) => self.set_value_latest(key, value),
			FuzzerAction::SetValueAt(key, value, at) => self.set_value_at(key, value, at),
			FuzzerAction::AppendLatest => self.append_latest(),
			FuzzerAction::AppendAt(at) => self.append_at(at),
			FuzzerAction::DropLatest => self.drop_latest(),
			FuzzerAction::DropAt(at) => self.drop_at(at),
		}
	}

	fn set_value_latest(&mut self, key: u8, value: u16) {
		let at_simple = self.simple.latest_state();
		// we only allow insert at terminal.
		if self.simple.is_latest(at_simple.latest()) {
			self.simple.emplace(vec![key], value, &at_simple);
			let at = self.in_memory_mgmt.latest_state();
			self.in_memory_db.emplace(vec![key], value, &at);
		}
	}

	fn set_value_at(&mut self, key: u8, value: u16, at: u8) {
		let at = (at % self.next_hash) as u32;
		// we only allow insert at terminal.
		if self.simple.is_latest(&at) {
			let state = StateInput(at);
			let at_simple = self.simple.get_db_state_mut(&state);
			let at = self.in_memory_mgmt.get_db_state_mut(&state);
			if self.with_ser {
				let at_ser = self.in_memory_mgmt_ser.get_db_state_mut(&state);
				assert_eq!(at, at_ser);
			}
			assert_eq!(at.is_some(), at_simple.is_some());
			at_simple.map(|at_simple|
				self.simple.emplace(vec![key], value, &at_simple)
			);
			at.map(|at|
				self.in_memory_db.emplace(vec![key], value, &at)
			);
		}
	}

	fn append_latest(&mut self) {
		if self.next_hash < NUMBER_POSSIBLE_STATES {
			let new_state = StateInput(self.next_hash as u32);
			let at_simple = self.simple.latest_state_fork();
			let s_simple = self.simple.append_external_state(new_state.clone(), &at_simple);
			let at = self.in_memory_mgmt.latest_state_fork();
			if self.with_ser {
				let ser_at = self.in_memory_mgmt_ser.latest_state_fork();
				assert_eq!(at, ser_at); 
				self.in_memory_mgmt_ser.append_external_state(new_state.clone(), &at);
			}
			let s = self.in_memory_mgmt.append_external_state(new_state, &at);
			if s.is_some() {
				self.next_hash += 1;
			}
			assert_eq!(s.is_some(), s_simple.is_some());
		}
	}

	fn append_at(&mut self, at: u8) {
		if self.next_hash < NUMBER_POSSIBLE_STATES {
			let new_state = StateInput(self.next_hash as u32);
			// keep in range
			let at_input = StateInput((at % self.next_hash) as u32);
			let at_simple = self.simple.get_db_state_for_fork(&at_input);
			let at = self.in_memory_mgmt.get_db_state_for_fork(&at_input);
			if self.with_ser {
				let ser_at = self.in_memory_mgmt_ser.get_db_state_for_fork(&at_input);
				assert_eq!(at, ser_at); 
			}
			assert_eq!(at.is_some(), at_simple.is_some());
			let s_simple = at_simple.and_then(|at| self.simple.append_external_state(new_state.clone(), &at));
			let s = at.and_then(|at| {
				if self.with_ser {
					self.in_memory_mgmt_ser.append_external_state(new_state.clone(), &at);
				}
				self.in_memory_mgmt.append_external_state(new_state, &at)
			});
			if s.is_some() {
				self.next_hash += 1;
			}
			assert_eq!(s.is_some(), s_simple.is_some());
		}
	}

	fn drop_latest(&mut self) {
		let at_simple = self.simple.latest_state_fork();
		let mut dropped_simple = self.simple.drop_state(&at_simple, true);
		let at = self.in_memory_mgmt.latest_state_fork();
		let mut dropped = self.in_memory_mgmt.drop_state(&at, true);
		if self.with_ser {
			self.in_memory_mgmt_ser.drop_state(&at, true);
		}
		dropped_simple.as_mut().map(|d| d.sort());
		dropped.as_mut().map(|d| d.sort());
		assert_eq!(dropped, dropped_simple)
	}

	fn drop_at(&mut self, at: u8) {
		let at = StateInput((at % self.next_hash) as u32);
		let at_simple = self.simple.get_db_state_for_fork(&at);
		let at = self.in_memory_mgmt.get_db_state_for_fork(&at);
		assert_eq!(at.is_some(), at_simple.is_some());
		let mut dropped_simple = at_simple.and_then(|at| self.simple.drop_state(&at, true));
		let mut dropped = at.and_then(|at| {
			if self.with_ser {
				self.in_memory_mgmt_ser.drop_state(&at, true);
			}
			self.in_memory_mgmt.drop_state(&at, true)
		});
		dropped_simple.as_mut().map(|d| d.sort());
		dropped.as_mut().map(|d| d.sort());
		assert_eq!(dropped, dropped_simple)
	}

	fn compare(&mut self) {
		if self.with_ser {
			let old = std::mem::replace(&mut self.in_memory_mgmt_ser, Default::default());
			let inner = old.extract_ser();
			let restore = InMemoryMgmtSer::from_ser(inner);
			let _ = std::mem::replace(&mut self.in_memory_mgmt_ser, restore);
		}
		for state in 0..self.next_hash {
			let state = StateInput(state as u32);
			let query_simple = self.simple.get_db_state(&state);
			let query = self.in_memory_mgmt.get_db_state(&state);
			if self.with_ser {
				let query_ser = self.in_memory_mgmt_ser.get_db_state(&state);
				assert_eq!(query, query_ser);
			}

			assert_eq!(query.is_some(), query_simple.is_some());
			if query.is_some() {
				let query = query.unwrap();
				let query_simple = query_simple.unwrap();
				for key in 0..NUMBER_POSSIBLE_KEYS {
					let value_simple = self.simple.get(&vec![key], &query_simple);
					let value = self.in_memory_db.get(&vec![key], &query);
					assert_eq!(value, value_simple);
				}
			}
		}
	}
}

const NUMBER_POSSIBLE_STATES: u8 = 255;
const NUMBER_POSSIBLE_KEYS: u8 = 4;
const NUMBER_POSSIBLE_VALUES: u8 = 16;

#[derive(Debug)]
enum FuzzerAction {
	/// Key is u8 but it.
	SetValueLatest(u8, u16),
	/// Key is u8 but it.
	SetValueAt(u8, u16, u8),
	/// append state at latest.
	AppendLatest,
	/// append state at given state.
	AppendAt(u8),
	/// drop latest.
	DropLatest,
	/// drop from.
	DropAt(u8),
}

impl FuzzerAction {
	fn next_action(data: &mut &[u8]) -> Option<Self> {
		if data.len() == 0 {
			return None;
		}
		match data[0] % 6 {
			0 => {
				if data.len() < 3 {
					return None;
				}
				let result = FuzzerAction::SetValueLatest(
					data[1] % NUMBER_POSSIBLE_KEYS,
					(data[2] % NUMBER_POSSIBLE_VALUES) as u16,
				);
				*data = &data[3..];
				Some(result)
			},
			1 => {
				if data.len() < 4 {
					return None;
				}
				let result = FuzzerAction::SetValueAt(
					data[1] % NUMBER_POSSIBLE_KEYS,
					(data[2] % NUMBER_POSSIBLE_VALUES) as u16,
					data[3],
				);
				*data = &data[4..];
				Some(result)
			},
			2 => {
				*data = &data[1..];
				Some(FuzzerAction::AppendLatest)
			},
			3 => {
				if data.len() < 2 {
					return None;
				}
				let result = FuzzerAction::AppendAt(data[1]);
				*data = &data[2..];
				Some(result)
			},
			4 => {
				*data = &data[1..];
				Some(FuzzerAction::DropLatest)
			},
			5 => {
				if data.len() < 2 {
					return None;
				}
				let result = FuzzerAction::DropAt(data[1]);
				*data = &data[2..];
				Some(result)
			},
			_ => unreachable!("modulo above"),
		}
	}

	#[cfg(test)]
	/// For debugging purpose.
	fn into_actions(data: &[u8]) -> Vec<FuzzerAction> {
		let data = &mut &data[..];
		let mut actions = Vec::new();
		while let Some(action) = FuzzerAction::next_action(data) {
			actions.push(action);
		}
		actions
	}
}

/// Entry point for fuzzing in memory forkable scenario.
pub fn inmemory_forkable(data: &[u8], with_ser: bool, with_gc: bool) {
	let mut fuzz_state = FuzzerState::new();
	fuzz_state.with_ser = with_ser;
	let data = &mut &data[..];
	while let Some(action) = FuzzerAction::next_action(data) {
		fuzz_state.apply(action);
	}
	fuzz_state.compare();
	if with_gc {
		let gc_journal = fuzz_state.in_memory_mgmt.get_gc();
		let gc_state = fuzz_state.in_memory_mgmt.get_gc().unwrap();
		for key in 0..NUMBER_POSSIBLE_KEYS {
			if let Some(value) = fuzz_state.in_memory_db.0.get_mut(&vec![key]) {
				let mut value2 = value.clone();
				value2.gc(gc_state.as_ref());
				if let Some(gc_journal) = gc_journal.as_ref() {
					value.gc(gc_journal.as_ref());
				}
				assert_eq!(value, &value2);
			}
		}
		fuzz_state.compare();
	}
}

#[test]
fn inmemory_forkable_no_regression() {
	let inputs = [
		&[][..],
		&[32, 50, 244, 0][..],
		&[32, 5, 0, 65][..],
		&[30, 65, 161][..],
		&[181, 226, 244, 157][..],
		&[219, 50, 32, 50][..],
		&[242, 7, 4, 2, 117, 125][..],
		&[122, 244, 1, 0, 0, 0][..],
		&[122, 244, 244, 6, 116, 122][..],
		&[242, 32, 122, 250, 16, 4][..],
		&[122, 122, 255, 117, 255, 1, 179, 122][..],
		&[255, 255, 254, 255, 1, 1, 0, 32, 122][..],
		&[255, 255, 152, 116, 255, 133, 217, 162, 253, 14, 14, 116, 255, 122, 24, 122, 255][..],
		&[0x26,0x5c,0x60,0x26,0x26,0xfa][..],
	];
	for input in inputs.iter() {
		println!("{:?}", FuzzerAction::into_actions(input));
		inmemory_forkable(input, true, true);
	}
}

#[test]
fn management() {
	let mut in_memory_mgmt_ser = InMemoryMgmtSer::default();
	assert!(in_memory_mgmt_ser.get_db_state_for_fork(&StateInput(199u32)).is_none());
	assert!(in_memory_mgmt_ser.get_db_state_for_fork(&StateInput(0u32)).is_none());
}
