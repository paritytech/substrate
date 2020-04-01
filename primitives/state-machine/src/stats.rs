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

use std::time::{Instant, Duration};
use std::cell::RefCell;

/// Measured count of operations and total bytes.
#[derive(Clone, Debug, Default)]
pub struct UsageUnit {
	/// Number of operations.
	pub ops: u64,
	/// Number of bytes.
	pub bytes: u64,
}

/// Usage statistics for state backend.
#[derive(Clone, Debug)]
pub struct UsageInfo {
	/// Read statistics (total).
	pub reads: UsageUnit,
	/// Write statistics (total).
	pub writes: UsageUnit,
	/// Write trie nodes statistics.
	pub nodes_writes: UsageUnit,
	/// Write into cached state machine
	/// change overlay.
	pub overlay_writes: UsageUnit,
	/// Removed trie nodes statistics.
	pub removed_nodes: UsageUnit,
	/// Cache read statistics.
	pub cache_reads: UsageUnit,
	/// Modified value read statistics.
	pub modified_reads: UsageUnit,
	/// Memory used.
	pub memory: usize,

	/// Moment at which current statistics has been started being collected.
	pub started: Instant,
	/// Timespan of the statistics.
	pub span: Duration,
}

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
}

impl UsageInfo {
	/// Empty statistics.
	///
	/// Means no data was collected.
	pub fn empty() -> Self {
		Self {
			reads: UsageUnit::default(),
			writes: UsageUnit::default(),
			overlay_writes: UsageUnit::default(),
			nodes_writes: UsageUnit::default(),
			removed_nodes: UsageUnit::default(),
			cache_reads: UsageUnit::default(),
			modified_reads: UsageUnit::default(),
			memory: 0,
			started: Instant::now(),
			span: Default::default(),
		}
	}
	/// Add collected state machine to this state.
	pub fn include_state_machine_states(&mut self, count: &StateMachineStats) {
		self.modified_reads.ops += *count.reads_modified.borrow();
		self.modified_reads.bytes += *count.bytes_read_modified.borrow();
		self.overlay_writes.ops += *count.writes_overlay.borrow();
		self.overlay_writes.bytes += *count.bytes_writes_overlay.borrow();
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
