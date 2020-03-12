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

//! Usage statistics

use core::time::{Duration};
use codec::{Encode, Decode};
use crate::StateMachineStats;

/// Measured count of operations and total bytes.
#[derive(Clone, Debug, Default, Encode, Decode)]
pub struct UsageUnit {
	/// Number of operations.
	pub ops: u64,
	/// Number of bytes.
	pub bytes: u64,
}

/// Usage statistics for state backend.
#[derive(Clone, Debug, Encode, Decode)]
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
	// Encoded as u32 because wasm's usize is u32.
	pub memory: u32,

	/// Moment at which current statistics has been started being collected.
	#[codec(skip)]
	pub started: Duration,
	/// Timespan of the statistics.
	// TODO: this can be encoded/decoded once https://github.com/paritytech/parity-scale-codec releases 1.3
	// with this PR https://github.com/paritytech/parity-scale-codec/pull/188 .
	#[codec(skip)]
	pub span: Duration,
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
			started: Default::default(),
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