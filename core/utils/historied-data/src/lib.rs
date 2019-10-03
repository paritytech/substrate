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
//! Useful to store information with history
//! on a per item basis.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::convert::{TryFrom, TryInto};

pub mod tree;
pub mod linear;

/// An entry at a given history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoriedValue<V, I> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: I,
}

impl<V, I> From<(V, I)> for HistoriedValue<V, I> {
	fn from(input: (V, I)) -> HistoriedValue<V, I> {
		HistoriedValue { value: input.0, index: input.1 }
	}
}

impl<V, I: Copy> HistoriedValue<V, I> {
	pub fn as_ref(&self) -> HistoriedValue<&V, I> {
		HistoriedValue {
			value: &self.value,
			index: self.index,
		}
	}

	pub fn as_mut(&mut self) -> HistoriedValue<&mut V, I> {
		HistoriedValue {
			value: &mut self.value,
			index: self.index,
		}
	}

	pub fn map<R, F: FnOnce(V) -> R>(self, f: F) -> HistoriedValue<R, I> {
		HistoriedValue {
			value: f(self.value),
			index: self.index,
		}
	}

}

// utility function for panicking cast (similar to a `as` cast for number).
fn as_usize<I: TryInto<usize>>(i: I) -> usize {
	match i.try_into() {
		Ok(index) => index,
		Err(_) => panic!("historied value index overflow"),
	}
}

// utility function for panicking cast (similar to a `as` cast for number).
fn as_i<I: TryFrom<usize>>(i: usize) -> I {
	match i.try_into() {
		Ok(index) => index,
		Err(_) => panic!("historied value index underflow"),
	}
}

/// Prunning result to be able to proceed
/// with further update if the value needs it.
pub enum PruneResult {
	Unchanged,
	Changed,
	Cleared,
}
