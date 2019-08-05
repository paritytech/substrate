// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Substrate state machine fuzzing implementations.
use substrate_state_machine::{
	OverlayedChanges,
};
use std::collections::HashMap;

/// Size of key, max 255
const KEY_SPACE: u8 = 20;

/// Size of key, max 255
const VALUE_SPACE: u8 = 50;

fn fuzz_transactions_inner(input: &[u8], check_gc: bool) {
	let mut input_index: usize = 0;
	let mut overlayed = OverlayedChanges::default();
	let mut ref_overlayed = RefOverlayedChanges::default();

	let mut actions = Vec::new();
	let mut values = Vec::new();
	loop {
		let action: Actions = if let Some(v) = input.get(input_index) {
			input_index += 1;
			(*v).into()
		} else { break };

		actions.push(action);
		match action {
			Actions::CommitProspective => {
				overlayed.commit_prospective();
				ref_overlayed.commit_prospective();
			},
			Actions::DropProspective => {
				overlayed.discard_prospective();
				ref_overlayed.discard_prospective();
			},
			Actions::NewTransaction => {
				overlayed.start_transaction();
				ref_overlayed.start_transaction();
			},
			Actions::CommitTransaction => {
				overlayed.commit_transaction();
				ref_overlayed.commit_transaction();
			},
			Actions::DropTransaction => {
				overlayed.discard_transaction();
				ref_overlayed.discard_transaction();
			},
			Actions::Insert => {
				let key = if let Some(v) = input.get(input_index) {
					input_index += 1;
					v % KEY_SPACE
				} else { break };
				let value = if let Some(v) = input.get(input_index) {
					input_index += 1;
					v % VALUE_SPACE
				} else { break };
				values.push((key, value));
				overlayed.set_storage(vec![key], Some(vec![value]));
				ref_overlayed.set_storage(vec![key], Some(vec![value]));
			}
		}

	}

	let mut success = true;

	let (check_value, len) = check_values(&overlayed, &ref_overlayed);
	success &= check_value;

	if check_gc {
		let reference_size = ref_overlayed.total_length();
		overlayed.gc(true);
		let size = overlayed.top_count_keyvalue_pair();
		if reference_size != size {
			println!("inconsistent gc {} {}", size, reference_size);
			success = false;
		}
		let (check_value, len_gc) = check_values(&overlayed, &ref_overlayed);
		success &= check_value;
		success &= len_gc == len;
	}
	ref_overlayed.commit_prospective();
	let ref_len = ref_overlayed.committed.len();
	if len != ref_len {
		println!("inconsistent length {} {}", len, ref_len);
		success = false;
	}
	if !success {
		println!("fuzzing: \n {:x?}", (&actions, &values));
		println!("input: \n {:?}", &input);
	}


	assert!(success);
}

fn check_values(overlayed: &OverlayedChanges, ref_overlayed: &RefOverlayedChanges) -> (bool, usize) {
	let mut len = 0;
	let mut success = true;
	for (key, value) in overlayed.top_iter() {

		let ref_value = ref_overlayed.storage(key);
		if Some(value) != ref_value {
			println!("at {:x?} different values {:x?} {:x?}", key, Some(value), ref_value);
			success = false;
		}
		len += 1;
	}
	(success, len)
}

pub fn fuzz_transactions(input: &[u8]) {
	fuzz_transactions_inner(input, false);
}

pub fn fuzz_transactions_then_gc(input: &[u8]) {
	fuzz_transactions_inner(input, true);
}

#[derive(Clone, Copy, Debug)]
pub enum Actions {
	Insert,
	// Delete, same as an insert do not test.
	CommitProspective,
	DropProspective,
	NewTransaction,
	CommitTransaction,
	DropTransaction,
}

impl From<u8> for Actions {
	fn from(v: u8) -> Self {
		match (v as usize) * 100 / 255 {
			v if v <= 5 => Actions::CommitProspective,
			v if v <= 10 => Actions::DropProspective,
			v if v <= 20 => Actions::NewTransaction,
			v if v <= 30 => Actions::CommitTransaction,
			v if v <= 40 => Actions::DropTransaction,
			_ => Actions::Insert,
		}
	}
}

/// A simple implementation of overlayed change
/// to use as a comparision.
/// It is partly incomplete (no child trie support, no change trie).
#[derive(Debug, Clone, Default)]
pub struct RefOverlayedChanges {
	committed: HashMap<Vec<u8>, Vec<u8>>,
	prospective: HashMap<Vec<u8>, Vec<u8>>,
	transactions: Vec<HashMap<Vec<u8>, Vec<u8>>>,
}

impl RefOverlayedChanges {
	pub fn discard_prospective(&mut self) {
		self.transactions.clear();
		self.prospective.clear();
	}

	pub fn commit_prospective(&mut self) {
		for _ in 0 .. self.transactions.len() {
			self.commit_transaction();
		}
		self.committed.extend(self.prospective.drain());
	}

	pub fn start_transaction(&mut self) {
		self.transactions.push(Default::default());
	}

	pub fn discard_transaction(&mut self) {
		if self.transactions.len() == 0 {
			// clear prospective on no transaction started.
			self.prospective.clear();
		} else {
			let _ = self.transactions.pop();
		}
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		match self.transactions.len() {
			0 => (),
			1 => self.prospective.extend(
				self.transactions.pop().expect("length just checked").into_iter()
			),
			_ => {
				let t = self.transactions.pop().expect("length just checked");
				self.transactions.last_mut().expect("length just checked")
					.extend(t.into_iter());
			}
		}
	}

	pub fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		if self.transactions.len() > 0 {
			self.transactions.last_mut().expect("length just checked")
				.insert(key, val.expect("fuzzer do not delete"));
		} else {
			self.prospective.insert(key, val.expect("fuzzer do not delete"));
		}
	}

	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		for t in self.transactions.iter().rev() {
			if let Some(v) = t.get(key) {
				return Some(Some(v));
			}
		}
		if let Some(v) = self.prospective.get(key) {
			return Some(Some(v));
		}
		if let Some(v) = self.committed.get(key) {
			return Some(Some(v));
		}
		None
	}

	pub fn total_length(&self) -> usize {
		let tr_len: usize = self.transactions.iter()
			.map(|l| l.len()).sum();
		self.committed.len() + self.prospective.len() + tr_len
	}
}

#[test]
fn debug_that() {
//50, 208, 50, 38, 46, 58, 209, 50, 216, 255, 255

//238, 0, 36, 43, 50, 46, 38, 211, 0, 0, 61

//50, 255, 38, 38, 186, 35, 46, 43, 46, 35, 255, 255, 102, 67

//0x6e,0xff,0xf7,0x0,0x6e,0xff,0xff,0x2d,0xff,0xff,0xff,0xe

	let input = vec![
	];
	fuzz_transactions_inner(&input[..], true);
}
