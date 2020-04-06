// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Usage statistics for state db

use core::cell::RefCell;

/// Accumulated usage statistics specific to state machine
/// crate.
#[derive(Debug, Default, Clone)]
pub struct StateMachineStats {
	/// Number of read query from runtime
	/// that hit a modified value (in state
	/// machine overlay).
	pub reads_modified: RefCell<u64>,
	/// Size in byte of read queries that
	/// hit a modified value.
	pub bytes_read_modified: RefCell<u64>,
	/// Number of time a write operation
	/// occurs into the state machine overlay.
	pub writes_overlay: RefCell<u64>,
	/// Size in bytes of the writes overlay
	/// operation.
	pub bytes_writes_overlay: RefCell<u64>,
}

impl StateMachineStats {
	/// Accumulates some registered stats.
	pub fn add(&self, other: &StateMachineStats) {
		*self.reads_modified.borrow_mut() += *other.reads_modified.borrow();
		*self.bytes_read_modified.borrow_mut() += *other.bytes_read_modified.borrow();
		*self.writes_overlay.borrow_mut() += *other.writes_overlay.borrow();
		*self.bytes_writes_overlay.borrow_mut() += *other.bytes_writes_overlay.borrow();
	}

	pub fn take(&self) -> Self {
		let stats = self.clone();
		*self.reads_modified.borrow_mut() = 0;
		*self.bytes_read_modified.borrow_mut() = 0;
		*self.writes_overlay.borrow_mut() = 0;
		*self.bytes_writes_overlay.borrow_mut() = 0;
		stats
	}
}


impl StateMachineStats {
	/// Tally one read modified operation, of some length.
	pub fn tally_read_modified(&self, data_bytes: u64) {
		*self.reads_modified.borrow_mut() += 1;
		*self.bytes_read_modified.borrow_mut() += data_bytes;
	}
	/// Tally one write overlay operation, of some length.
	pub fn tally_write_overlay(&self, data_bytes: u64) {
		*self.writes_overlay.borrow_mut() += 1;
		*self.bytes_writes_overlay.borrow_mut() += data_bytes;
	}
}
