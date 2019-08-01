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
/// Size of key, max 255
const KEY_SPACE: u8 = 20;

/// Size of key, max 255
const VALUE_SPACE: u8 = 50;

pub fn fuzz_transactions(input: &[u8]) {
	let mut input_index: usize = 0;
	let mut overlayed = OverlayedChanges::default();
	loop {
		let action = if let Some(v) = input.get(input_index) {
			input_index += 1;
			(*v).into()
		} else { break };

		match action {
			Actions::CommitProspective => overlayed.commit_prospective(),
			Actions::DropProspective => overlayed.discard_prospective(),
			Actions::NewTransaction => overlayed.start_transaction(),
			Actions::CommitTransaction => overlayed.commit_transaction(),
			Actions::DropTransaction => overlayed.discard_transaction(),
			Actions::Insert => {
				let key = if let Some(v) = input.get(input_index) {
					input_index += 1;
					v % KEY_SPACE
				} else { break };
				let value = if let Some(v) = input.get(input_index) {
					input_index += 1;
					v % VALUE_SPACE
				} else { break };
				overlayed.set_storage(vec![key], Some(vec![value]));
			}
		}

	}
}

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

