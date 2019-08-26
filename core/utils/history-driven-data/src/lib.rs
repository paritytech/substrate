// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! History driven data storage.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod linear;

#[derive(Debug, Clone, PartialEq, Copy)]
/// State of a transaction, the states are stored
/// in a linear indexed history.
pub enum State {
	/// Overlay is under change and can still be dropped.
	Pending,
	/// Overlay is under change and can still be dropped.
	/// This also mark the start of a transaction.
	TxPending,
	/// Information is committed, but can still be dropped
	/// using `discard_prospective` or `discard_transaction`
	/// of a parent transaction.
	Prospective,
	/// Committed is information that cannot be dropped.
	Committed,
	/// Information pointing to this indexed historic state should
	/// not be returned and can be removed.
	Dropped,
}

pub const DEFAULT_GC_CONF: GCConfiguration = GCConfiguration {
	trigger_transaction_gc: 100_000,
	trigger_commit_gc: 10_000,
	add_content_size_unit: 64,
};

pub struct GCConfiguration {
	/// Treshold in number of operation before running a garbage colletion.
	///
	/// Should be same as `TRIGGER_COMMIT_GC` or higher
	/// (we most likely do not want lower as transaction are
	/// possibly more frequent than commit).
	trigger_transaction_gc: usize,

	/// Treshold in number of operation before running a garbage colletion
	/// on a commit operation.
	///
	/// We may want a lower value than for a transaction, even
	/// a 1 if we want to do it between every operation.
	trigger_commit_gc: usize,

	/// Used to count big content as multiple operations.
	/// This is a number of octet.
	/// Set to 0 to ignore.
	add_content_size_unit: usize,
}
