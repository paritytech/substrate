// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.	If not, see <http://www.gnu.org/licenses/>.

use crate::linear::{
	Serialized as SerializedInner,
	SerializedConfig,
};
use crate::HistoricalValue;
use crate::PruneResult;
use crate::saturating_into;
use rstd::vec::Vec;
use rstd::convert::{TryFrom, TryInto};
use num_traits::Bounded;

/// Trait defining a state for querying or modifying a tree.
/// This is a collection of branches index, corresponding
/// to a tree path.
pub trait BranchesStateTrait<S, I, BI> {
	type Branch: BranchStateTrait<S, BI>;
	type Iter: Iterator<Item = (Self::Branch, I)>;

	/// Get branch state for node at a given index.
	fn get_branch(self, index: I) -> Option<Self::Branch>;

	/// Get the last index for the state, inclusive.
	fn last_index(self) -> I;

	/// Iterator over the branch states.
	fn iter(self) -> Self::Iter;
}

/// Trait defining a state for querying or modifying a branch.
/// This is therefore the representation of a branch state.
pub trait BranchStateTrait<S, I> {

	/// Get state for node at a given index.
	fn get_node(&self, i: I) -> S;

	/// Get the last index for the state, inclusive.
	fn last_index(&self) -> I;
}

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRange {
	pub start: u64,
	pub end: u64,
}

impl<'a> BranchStateTrait<bool, u64> for &'a BranchRange {

	fn get_node(&self, i: u64) -> bool {
		i >= self.start && i < self.end
	}

	fn last_index(&self) -> u64 {
		// underflow should not happen as long as branchstateref are not allowed to be empty.
		self.end - 1
	}

}

/// u64 is use a a state target so it is implemented as
/// a upper bound.
impl<'a> BranchStateTrait<bool, u64> for u64 {

	fn get_node(&self, i: u64) -> bool {
		&i <= self
	}

	fn last_index(&self) -> u64 {
		*self
	}

}

impl BranchRange {
	/// Return true if the state exists, false otherwhise.
	pub fn get_state(&self, index: u64) -> bool {
		index < self.end && index >= self.start
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchState {
	pub branch_index: u64,
	pub range: BranchRange,
}


impl<'a, F: SerializedConfig> Serialized<'a, F> {

	pub fn into_vec(self) -> Vec<u8> {
		self.0.into_vec()
	}

	pub fn get<I, S> (&self, state: S) -> Option<Option<&[u8]>> 
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64> + Bounded,
	{
		let mut index = self.0.len();
		if index == 0 {
			return None;
		}
		while index > 0 {
			index -= 1;
			let HistoricalValue { value, index: state_index } = self.0.get_state(index);
			let state_index = saturating_into(state_index);
			if state.get_node(state_index) {
				// Note this extra byte is note optimal, should be part of index encoding
				if value.len() > 0 {
					return Some(Some(&value[..value.len() - 1]));
				} else {
					return Some(None);
				}
			}
		}
		None
	}

	/// This append the value, and can only be use in an
	/// orderly fashion.
	pub fn push<S, I>(&mut self, state: S, value: Option<&[u8]>) 
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64>,
	{
		let target_state_index = saturating_into(state.last_index());
		let index = self.0.len();
		if index > 0 {
			let last = self.0.get_state(index - 1);
			debug_assert!(target_state_index >= last.index); 
			if target_state_index == last.index {
				self.0.pop();
			}
		}
		match value {
			Some(value) =>
				self.0.push_extra(HistoricalValue {value, index: target_state_index}, &[0][..]),
			None =>
				self.0.push(HistoricalValue {value: &[], index: target_state_index}),
		}
	}

	/// Prune value that are before the index if they are
	/// not needed afterward.
	pub fn prune<I>(&mut self, index: I) -> PruneResult
		where
			I: Copy + Eq + TryFrom<u64> + TryInto<u64>,
	{
		let from = saturating_into(index);
		let len = self.0.len();
		let mut last_index_with_value = None;
		let mut index = 0;
		while index < len {
			let history = self.0.get_state(index);
			if history.index == from + 1 {
				// new first content
				if history.value.len() != 0 {
					// start value over a value drop until here
					last_index_with_value = Some(index);
					break;
				}
			} else if history.index > from {
				if history.value.len() == 0 
					&& last_index_with_value.is_none() {
						// delete on delete, continue
				} else {
					if last_index_with_value.is_none() {
						// first value, use this index
						last_index_with_value = Some(index);
					}
					break;
				}
			}
			if history.value.len() > 0 {
				last_index_with_value = Some(index);
			} else {
				last_index_with_value = None;
			}
			index += 1;
		}

		if let Some(last_index_with_value) = last_index_with_value {
			if last_index_with_value > 0 {
				self.0.truncate_until(last_index_with_value);
				return PruneResult::Changed;
			}
		} else {
			self.0.clear();
			return PruneResult::Cleared;
		}

		PruneResult::Unchanged
	}
	
}

#[derive(Debug, Clone)]
/// Serialized implementation when transaction support is not
/// needed.
pub struct Serialized<'a, F>(SerializedInner<'a, F>);

impl<'a, 'b, F> PartialEq<Serialized<'b, F>> for Serialized<'a, F> {
  fn eq(&self, other: &Serialized<'b, F>) -> bool {
		self.0.eq(&other.0)
	}
}

impl<'a, F> Eq for Serialized<'a, F> { }

impl<'a, F> Serialized<'a, F> {
	pub fn from_slice(s: &'a [u8]) -> Serialized<'a, F> {
		Serialized(s.into())
	}

	pub fn from_vec(s: Vec<u8>) -> Serialized<'static, F> {
		Serialized(s.into())
	}
}

impl<'a, F> Into<Serialized<'a, F>> for &'a [u8] {
	fn into(self) -> Serialized<'a, F> {
		Serialized(self.into())
	}
}

impl<F> Into<Serialized<'static, F>> for Vec<u8> {
	fn into(self) -> Serialized<'static, F> {
		Serialized(self.into())
	}
}

impl<'a, F: SerializedConfig> Default for Serialized<'a, F> {
	fn default() -> Self {
		Serialized(SerializedInner::<'a, F>::default())
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_prune() {
		let mut item: Serialized<crate::linear::NoVersion> = Default::default();
		// setting value respecting branch build order
		for i in 1..6 {
			item.push(i, Some(&[i as u8]));
		}

		for a in 1..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}
		item.prune(1);
		assert_eq!(item.get(1), None);
		for a in 2..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}

		item.prune(4);
		for a in 1..5 {
			assert_eq!(item.get(a), None);
		}
		for a in 5..6 {
			assert_eq!(item.get(a), Some(Some(&[a as u8][..])));
		}

		item.prune(80);
		for a in 1..4 {
			assert_eq!(item.get(a), None);
		}
		// pruning preserve last valid value
		for a in 5..11 {
			assert_eq!(item.get(a), Some(Some(&[5 as u8][..])));
		}

		// prune skip unrelevant delete
		let mut item: Serialized<crate::linear::NoVersion> = Default::default();
		item.push(1, Some(&[1 as u8]));
		item.push(2, None);
		item.push(3, Some(&[3 as u8]));
		assert_eq!(item.get(1), Some(Some(&[1][..])));
		assert_eq!(item.get(2), Some(None));
		assert_eq!(item.get(3), Some(Some(&[3][..])));
		assert_eq!(item.0.len(), 3);
		item.prune(1);
		assert_eq!(item.0.len(), 1);
		assert_eq!(item.get(1), None);
		assert_eq!(item.get(2), None);
		assert_eq!(item.get(3), Some(Some(&[3][..])));

		// prune skip unrelevant delete
		let mut item: Serialized<crate::linear::NoVersion> = Default::default();
		item.push(1, Some(&[1 as u8]));
		item.push(3, None);
		item.push(4, Some(&[4 as u8]));
		assert_eq!(item.get(1), Some(Some(&[1][..])));
		assert_eq!(item.get(2), Some(Some(&[1][..])));
		assert_eq!(item.get(3), Some(None));
		assert_eq!(item.get(4), Some(Some(&[4][..])));
		assert_eq!(item.0.len(), 3);
		// 1 needed for state two
		assert_eq!(PruneResult::Unchanged, item.prune(1));
		// 3 unneeded
		item.prune(2);
		assert_eq!(item.0.len(), 1);
		assert_eq!(item.get(1), None);
		assert_eq!(item.get(2), None);
		assert_eq!(item.get(3), None);
		assert_eq!(item.get(4), Some(Some(&[4][..])));

		// prune delete at block
		let mut item: Serialized<crate::linear::DefaultVersion> = Default::default();
		item.push(0, Some(&[0 as u8]));
		item.push(1, None);
		assert_eq!(item.get(0), Some(Some(&[0][..])));
		assert_eq!(item.get(1), Some(None));
		item.prune(0);
		assert_eq!(item.get(0), None);
		assert_eq!(item.get(1), None);
		assert_eq!(item.0.len(), 0);

	}

}
