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
//! This is use to store historical information for an item,
//! and does have to include any proof.


#![cfg_attr(not(feature = "std"), no_std)]

pub mod synch_linear_transaction;

/// An entry at a given history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test-helpers"), derive(PartialEq))]
pub struct HistoricalValue<V, I> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: I,
}

impl<V, I> From<(V, I)> for HistoricalValue<V, I> {
	fn from(input: (V, I)) -> HistoricalValue<V, I> {
		HistoricalValue { value: input.0, index: input.1 }
	}
}

impl<V, I: Clone> HistoricalValue<V, I> {
	fn as_mut(&mut self) -> HistoricalValue<&mut V, I> {
		HistoricalValue { value: &mut self.value, index: self.index.clone() }
	}
}

#[derive(PartialEq)]
#[cfg_attr(any(test, feature = "test"), derive(Debug))]
/// Prunning result to be able to proceed
/// with further update if the value needs it.
pub enum PruneResult {
	Unchanged,
	Changed,
	Cleared,
}
