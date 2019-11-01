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

//! Data storage containing multiple state for a value.
//! Should be use to store historical information for an item.
//!
//! # Design
//!
//! Two elements are used, a global state and multiple historical
//! values.
//! Multiple states for an historical value only make sense if the states
//! got a common basis, that is using partial reference (subsets of a
//! unique global set).
//!
//! ## state operation
//!
//! The state is an historic of state and can be seen as an index
//! for querying or updated the value.
//! State operations, are only changing the state, but not the
//! related stored value (allowing low cost update).
//! If the state cannot modify the existing values, it means that
//! the state cannot change its indexing, it can change a state for
//! an index but cannot remove it, thus it is an append only structure.
//!
//! An operation on a value relates to the state by the last index of the state
//! for the value operation (field `index` of `HistoricalValue`).
//!
//! Therefore the state can be used trimed from its latest index to query a
//! previous state.
//!
//! It should be possible to mutably reduce the state under the assumption 
//! that all linked values where pruned accordingly (or by executing an
//! index adjustment on all values atomically).
//! Generally this is not a good idea, as it defeats the purpose of this crate:
//! state size is marginal in comparison of values size.
//! Additionally values query should be very moderatly impacted by the state size
//! (for linear state it is not, but for a tree state the indexing between two branches
//! involves a small additional cost to jump between branch).
//!
//! ## value operation
//! 
//! We said before that state operations do not update values, so the value operations
//! will always use the state (or part of the state) as a parameter in order
//! return a different value depending on this state parameter.
//! Operation are simply update of value and queries, but to allow query at different
//! historic state, the values (`HistoricalValue`) do keep reference to all possible values.
//!
//! The crate favors light state operation that do not force update of values,
//! but sometime limited updates on values mutable access can be done (if the cost is
//! close to query cost).
//! To avoid memory exhaustion, a costy manual pruning for value corresponding to dead state
//! is provided (usually call `get_mut_pruning`).
//! It can be use to set in place a garbage collection.


#![cfg_attr(not(feature = "std"), no_std)]

pub mod linear;

/// A default sample configuration to manage garbage collection
/// triggering.
pub const DEFAULT_GC_CONF: GCConfiguration = GCConfiguration {
	trigger_transaction_gc: 100_000,
	trigger_commit_gc: 10_000,
	add_content_size_unit: 64,
};

/// Garbage collection configuration.
/// It is designed to listen on two different operation, transaction
/// and commit.
/// It match transcational semantic with transaction for transaction
/// operation and commit for prospective operation.
pub struct GCConfiguration {
	/// Treshold in number of operation before running a garbage collection.
	///
	/// Should be same as `TRIGGER_COMMIT_GC` or higher
	/// (we most likely do not want lower as transaction are
	/// possibly more frequent than commit).
	pub trigger_transaction_gc: usize,

	/// Treshold in number of operation before running a garbage colletion
	/// on a commit operation.
	///
	/// We may want a lower value than for a transaction, even
	/// a 1 if we want to do it between every operation.
	pub trigger_commit_gc: usize,

	/// Used to count big content as multiple operations.
	/// This is a number of octet.
	/// Set to 0 to ignore.
	pub add_content_size_unit: usize,
}

impl GCConfiguration {
	/// Cost depending on value if any.
	pub fn operation_cost(&self, val: Option<&rstd::vec::Vec<u8>>) -> usize {
		let additional_cost = if self.add_content_size_unit > 0 {
			if let Some(s) = val.as_ref() {
				s.len() / self.add_content_size_unit
			} else {
				0
			}
		} else { 0 };
		1 + additional_cost
	}

}
