// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Usage statistics for state db

use sp_std::cell::RefCell;
#[cfg(feature = "std")]
use std::time::{Duration, Instant};

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

	#[cfg(feature = "std")]
	/// Moment at which current statistics has been started being collected.
	pub started: Instant,
	#[cfg(feature = "std")]
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
			#[cfg(feature = "std")]
			started: Instant::now(),
			#[cfg(feature = "std")]
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
