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

//! Data state is an acyclic directed graph (tree).
//!
//! General structure for the global state is an array of branch,
//! each branch originating from another branch at designated index.
//!
//! Data structure for data is an indexed collection of linear storages
//! for each of those branches.

use crate::linear::{
	InMemory as BranchBackend,
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


/// First field is the actual history against which we run
/// the state.
/// Second field is an optional value for the no match case.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(Vec<HistoryBranch<V>>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Vec::new())
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoryBranch<V> {
	branch_index: u64,
	history: BranchBackend<V, u64>,
}

impl<V> History<V> {

	/// Set or update value for a given state.
	pub fn set<S, I, BI>(&mut self, state: S, value: V) 
		where
			S: BranchesStateTrait<bool, I, BI>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64>,
			BI: Copy + Eq + TryFrom<u64> + TryInto<u64>,
	{
		if let Some((state_branch, state_index)) = state.iter().next() {
			let state_index_u64 = saturating_into(state_index);
			let mut i = self.0.len();
			let (branch_position, new_branch) = loop {
				if i == 0 {
					break (0, true);
				}
				let branch_index = self.0[i - 1].branch_index;
				if branch_index == state_index_u64 {
					break (i - 1, false);
					} else if branch_index < state_index_u64 {
					break (i, true);
				}
				i -= 1;
			};
			if new_branch {
				let index = saturating_into(state_branch.last_index());
				let mut history = BranchBackend::<V, u64>::default();
				history.push(HistoricalValue {
					value,
					index,
				});
				let h_value = HistoryBranch {
					branch_index: state_index_u64,
					history,
				};
				if branch_position == self.0.len() {
					self.0.push(h_value);
				} else {
					self.0.insert(branch_position, h_value);
				}
			} else {
				self.node_set(branch_position, &state_branch, value)
			}
		}
	}

	fn node_set<S, I>(&mut self, branch_index: usize, state: &S, value: V)
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64>,
	{
		let node_index_u64 = saturating_into(state.last_index());
		let history = &mut self.0[branch_index];
		let mut index = history.history.len();
		debug_assert!(index > 0);
		loop {
			if index == 0 || history.history[index - 1].index < node_index_u64 {
				let h_value = HistoricalValue {
					value,
					index: node_index_u64
				};
				if index == history.history.len() {
					history.history.push(h_value);
				} else {
					history.history.insert(index, h_value);
				}
				break;
			} else if history.history[index - 1].index == node_index_u64 {
				history.history[index - 1].value = value;
				break;
			}
			index -= 1;
		}
	}

	/// Access to last valid value (non dropped state in history).
	/// When possible please use `get_mut` as it can free some memory.
	pub fn get<I, BI, S> (&self, state: S) -> Option<&V> 
		where
			S: BranchesStateTrait<bool, I, BI>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64>,
			BI: Copy + Eq + TryFrom<u64> + TryInto<u64> + Bounded,
	{
		let mut index = self.0.len();
		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		if index == 0 {
			return None;
		}

		for (state_branch, state_index) in state.iter() {
			let state_index = saturating_into(state_index);
			while index > 0 {
				let branch_index = saturating_into(self.0[index - 1].branch_index);
				if state_index == branch_index {
					if let Some(result) = self.branch_get(index - 1, &state_branch) {
						return Some(result)
					}
					break;
				} else if state_index > branch_index {
					break;
				} else {
					index -= 1;
				}
			}
			if index == 0 {
				break;
			}
		}
		None
	}

	fn branch_get<S, I>(&self, index: usize, state: &S) -> Option<&V>
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64> + Bounded,
	{
		let history = &self.0[index];
		let mut index = history.history.len();
		while index > 0 {
			index -= 1;
			if let Some(&v) = history.history.get(index).as_ref() {
				let i = saturating_into(v.index);
				if state.get_node(i) {
					return Some(&v.value);
				}
			}
		}
		None
	}

	/// Gc an historical value other its possible values.
	/// Iterator need to be reversed ordered by branch index.
	pub fn gc<IT, S, I>(&mut self, mut states: IT) -> PruneResult
		where
			IT: Iterator<Item = (S, I)>,
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<u64> + TryInto<u64> + Bounded,
	{
		let mut changed = false;
		// state is likely bigger than history.
		let mut current_state = states.next();
		for branch_index in (0..self.0.len()).rev() {
			let history_branch = self.0[branch_index].branch_index;
			loop {
				if let Some(state) = current_state.as_ref() {
					let state_index_u64 = saturating_into(state.1);
					if history_branch < state_index_u64 {
						current_state = states.next();
					} else if history_branch == state_index_u64 {
						let len = self.0[branch_index].history.len();
						for history_index in (0..len).rev() {
							let node_index = saturating_into(self.0[branch_index].history[history_index].index);
							if !state.0.get_node(node_index) {
								if history_index == len - 1 {
									changed = self.0[branch_index]
										.history.pop().is_some() || changed;
								} else {
									self.0[branch_index]
										.history.remove(history_index);
									changed = true;
								}
							}
						}
						if self.0[branch_index].history.len() == 0 {
							self.0.remove(branch_index);
							changed = true;
						}
						break;
					} else {
						self.0.remove(branch_index);
						changed = true;
						break;
					}
				} else {
					self.0.remove(branch_index);
					changed = true;
					break;
				}
			}
		}
		if changed {
			if self.0.len() == 0 {
				PruneResult::Cleared
			} else {
				PruneResult::Changed
			}
		} else {
			PruneResult::Unchanged
		}
	}

}

impl<'a, F: SerializedConfig> Serialized<'a, F> {

	pub fn into_owned(self) -> Serialized<'static, F> {
		Serialized(self.0.into_owned())
	}

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

	use rstd::collections::btree_map::BTreeMap;
	use rstd::rc::Rc;

	/// At this point this is only use for testing and as an example
	/// implementation.
	/// It keeps trace of dropped value, and have some costy recursive
	/// deletion.
	#[derive(Debug, Clone)]
	#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
	struct TestStates {
		branches: BTreeMap<u64, BranchStateFull>,
		last_branch_index: u64,
		/// a lower treshold under which every branch are seen
		/// as containing only valid values.
		/// This can only be updated after a full garbage collection.
		valid_treshold: u64,
	}

	#[derive(Debug, Clone)]
	#[cfg_attr(any(test, feature = "test"), derive(PartialEq, Eq))]
	struct BranchStateFull {
		// this is the key (need to growth unless full gc (can still have
		// content pointing to it even if it seems safe to reuse a previously
		// use ix).
		branch_index: u64,
		
		origin_branch_index: u64,
		origin_node_index: u64,

		state: ModifiableBranchRange,
	}

	#[derive(Debug, Clone)]
	#[cfg_attr(any(test, feature = "test"), derive(PartialEq, Eq))]
	struct ModifiableBranchRange {
		range: BranchRange,
		can_append: bool,
	}

	#[derive(Clone)]
	/// Reference to state to use for query updates.
	/// It is a single brannch path with branches ordered by branch_index.
	/// It uses a Rc to be sharable between multiple state, in practice
	/// this is not very useful when node get appended.
	struct BranchRanges {
		/// Oredered by branch index linear branch states.
		history: Rc<Vec<BranchState>>,
		/// Index is included, acts as length of history.
		upper_branch_index: Option<u64>,
		/// Index is included, acts as a branch ref end value.
		upper_node_index: Option<u64>,
	}

	impl Default for TestStates {
		fn default() -> Self {
			TestStates {
				branches: Default::default(),
				last_branch_index: 0,
				valid_treshold: 0,
			}
		}
	}

	impl TestStates {

		/// warning it should be the index of the leaf, otherwhise the ref will be incomplete.
		/// (which is fine as long as we use this state to query something that refer to this state.
		pub fn state(&self, mut branch_index: u64) -> BranchRanges {
			let mut result = Vec::new();
			let mut previous_origin_node_index = u64::max_value() - 1;
			while branch_index > self.valid_treshold {
				if let Some(branch) = self.branches.get(&branch_index) {
					let mut branch_range = branch.state();
					if branch_range.range.end > previous_origin_node_index + 1 {
						branch_range.range.end = previous_origin_node_index + 1;
					}
					previous_origin_node_index = branch.origin_node_index;
					// vecdeque would be better suited
					result.insert(0, branch_range);
					branch_index = branch.origin_branch_index;
				} else {
					break;
				}
			}
			BranchRanges { history: Rc::new(result), upper_branch_index: None, upper_node_index: None }
		}

		// create a branches. End current branch.
		// Return first created index (next branch are sequential indexed)
		// or None if origin branch does not allow branch creation (commited branch or non existing).
		pub fn create_branch(
			&mut self,
			nb_branch: usize,
			branch_index: u64,
			node_index: Option<u64>,
		) -> Option<u64> {
			if nb_branch == 0 {
				return None;
			}

			// for 0 is the first branch creation case
			let node_index = if branch_index == 0 {
				debug_assert!(node_index.is_none());
				0
			} else {
				if let Some(node_index) = self.get_node(branch_index, node_index) {
					node_index
				} else {
					return None;
				}
			};

			let result_ix = self.last_branch_index + 1;
			for i in result_ix .. result_ix + (nb_branch as u64) {
				self.branches.insert(i, BranchStateFull {
					branch_index: i,
					origin_branch_index: branch_index,
					origin_node_index: node_index,
					state: Default::default(),
				});
			}
			self.last_branch_index += nb_branch as u64;

			Some(result_ix)
		}

		/// check if node is valid for given index.
		/// return node_index.
		pub fn get_node(
			&self,
			branch_index: u64,
			node_index: Option<u64>,
		) -> Option<u64> {
			if let Some(branch) = self.branches.get(&branch_index) {
				if let Some(node_index) = node_index {
					if branch.state.get_state(node_index) {
						Some(node_index)
					} else {
						None
					}
				} else {
					branch.state.latest_ix()
				}
			} else {
				None
			}
		}

		/// Do node exist (return state (being true or false only)).
		pub fn get(&self, branch_index: u64, node_index: u64) -> bool {
			self.get_node(branch_index, Some(node_index)).is_some()
		}

		pub fn branch_range_mut(&mut self, branch_index: u64) -> Option<&mut ModifiableBranchRange> {
			self.branches.get_mut(&branch_index)
				.map(|b| &mut b.state)
		}

		/// this function can go into deep recursion with full scan, it indicates
		/// that the tree model use here should only be use for small data or
		/// tests.
		pub fn apply_drop_state(&mut self, branch_index: u64, node_index: u64) {
			let mut to_delete = Vec::new();
			for (i, s) in self.branches.iter() {
				if s.origin_branch_index == branch_index && s.origin_node_index == node_index {
					to_delete.push(*i);
				}
			}
			for i in to_delete.into_iter() {
				loop {
					match self.branch_range_mut(i).map(|ls| ls.drop_state()) {
						Some(Some(li)) => self.apply_drop_state(i, li),
						Some(None) => break, // we keep empty branch
						None => break,
					}
				}
			}
		}
	}

	impl BranchStateFull {
		pub fn state(&self) -> BranchState {
			BranchState {
				branch_index: self.branch_index,
				range: self.state.range(),
			}
		}
	}

	impl<'a> BranchesStateTrait<bool, u64, u64> for &'a BranchRanges {
		type Branch = (&'a BranchRange, Option<u64>);
		type Iter = BranchRangesIter<'a>;

		fn get_branch(self, i: u64) -> Option<Self::Branch> {
			for (b, bi) in self.iter() {
				if bi == i {
					return Some(b);
				} else if bi < i {
					break;
				}
			}
			None
		}

		fn last_index(self) -> u64 {
			let l = self.history.len();
			let l = if l > 0 {
				self.history[l - 1].branch_index
			} else {
				0
			};
			self.upper_branch_index.map(|u| rstd::cmp::min(u, l)).unwrap_or(l)
		}

		fn iter(self) -> Self::Iter {
			let mut end = self.history.len();
			let last_index = self.last_index();
			let upper_node_index = if Some(last_index) == self.upper_branch_index {
				self.upper_node_index
			} else { None };
			while end > 0 {
				if self.history[end - 1].branch_index <= last_index {
					break;
				}
				end -= 1;
			}

			BranchRangesIter(self, end, upper_node_index)
		}
	}

	impl<'a> BranchStateTrait<bool, u64> for (&'a BranchRange, Option<u64>) {

		fn get_node(&self, i: u64) -> bool {
			let l = self.0.end;
			let upper = self.1.map(|u| rstd::cmp::min(u + 1, l)).unwrap_or(l);
			i >= self.0.start && i < upper
		}

		fn last_index(&self) -> u64 {
			// underflow should not happen as long as branchstateref are not allowed to be empty.
			let state_end = self.0.end - 1;
			self.1.map(|bound| rstd::cmp::min(state_end, bound)).unwrap_or(state_end)
		}

	}

	impl Default for ModifiableBranchRange {
		// initialize with one element
		fn default() -> Self {
			Self::new_from(0)
		}
	}

	impl ModifiableBranchRange {
		pub fn new_from(offset: u64) -> Self {
			ModifiableBranchRange {
				range: BranchRange {
					start: offset,
					end: offset + 1,
				},
				can_append: true,
			}
		}

		pub fn range(&self) -> BranchRange {
			self.range.clone()
		}

		pub fn add_state(&mut self) -> bool {
			if self.can_append {
				self.range.end += 1;
				true
			} else {
				false
			}
		}

		pub fn drop_state(&mut self) -> Option<u64> {
			if self.range.end > self.range.start {
				self.range.end -= 1;
				self.can_append = false;
				Some(self.range.end)
			} else {
				None
			}
		}

		pub fn get_state(&self, index: u64) -> bool {
			self.range.get_state(index)
		}

		pub fn latest_ix(&self) -> Option<u64> {
			if self.range.end > self.range.start {
				Some(self.range.end - 1)
			} else {
				None
			}
		}

	}

	/// Iterator, contains index of last inner struct.
	pub struct BranchRangesIter<'a>(&'a BranchRanges, usize, Option<u64>);

	impl<'a> Iterator for BranchRangesIter<'a> {
		type Item = ((&'a BranchRange, Option<u64>), u64);

		fn next(&mut self) -> Option<Self::Item> {
			if self.1 > 0 {
				self.1 -= 1;
				let upper_node_index = self.2.take();
				Some((
					(&self.0.history[self.1].range, upper_node_index),
					self.0.history[self.1].branch_index,
				))
			} else {
				None
			}
		}
	}

	impl BranchRanges {
		/// limit to a given branch (included).
		/// Optionally limiting branch to a linear index (included).
		pub fn limit_branch(&mut self, branch_index: u64, node_index: Option<u64>) {
			debug_assert!(branch_index > 0);
			self.upper_branch_index = Some(branch_index);
			self.upper_node_index = node_index;
		}

	}


	fn test_states() -> TestStates {
		let mut states = TestStates::default();
		assert_eq!(states.create_branch(1, 0, None), Some(1));
		// root branching.
		assert_eq!(states.create_branch(1, 0, None), Some(2));
		assert_eq!(Some(true), states.branch_range_mut(1).map(|ls| ls.add_state()));
		assert_eq!(states.create_branch(2, 1, None), Some(3));
		assert_eq!(states.create_branch(1, 1, Some(0)), Some(5));
		assert_eq!(states.create_branch(1, 1, Some(2)), None);
		assert_eq!(Some(true), states.branch_range_mut(1).map(|ls| ls.add_state()));
		assert_eq!(Some(Some(2)), states.branch_range_mut(1).map(|ls| ls.drop_state()));
		// cannot create when dropped happen on branch
		assert_eq!(Some(false), states.branch_range_mut(1).map(|ls| ls.add_state()));

		assert!(states.get(1, 1));
		// 0> 1: _ _ X
		// |       |> 3: 1
		// |       |> 4: 1
		// |     |> 5: 1
		// |> 2: _

		states
	}

	#[test]
	fn test_remove_attached() {
		let mut states = test_states();
		assert_eq!(Some(Some(1)), states.branch_range_mut(1).map(|ls| ls.drop_state()));
		assert!(states.get(3, 0));
		assert!(states.get(4, 0));
		states.apply_drop_state(1, 1);
		assert!(!states.get(3, 0));
		assert!(!states.get(4, 0));
	}

	#[test]
	fn test_state() {
		let states = test_states();
		let ref_3 = vec![
			BranchState {
				branch_index: 1,
				range: BranchRange { start: 0, end: 2 },
			},
			BranchState {
				branch_index: 3,
				range: BranchRange { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state(3).history, ref_3);

		let mut states = states;

		assert_eq!(states.create_branch(1, 1, Some(0)), Some(6));
		let ref_6 = vec![
			BranchState {
				branch_index: 1,
				range: BranchRange { start: 0, end: 1 },
			},
			BranchState {
				branch_index: 6,
				range: BranchRange { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state(6).history, ref_6);

		states.valid_treshold = 3;
		let mut ref_6 = ref_6;
		ref_6.remove(0);
		assert_eq!(*states.state(6).history, ref_6);
	}

	#[test]
	fn test_set_get() {
		let states = test_states();
		let mut item: History<u64> = Default::default();
		let mut ref_1 = states.state(3);
		ref_1.limit_branch(1, Some(1));
		item.set(&states.state(1), 4);
		assert_eq!(item.get(&states.state(1)), Some(&4));
		assert_eq!(item.get(&states.state(4)), Some(&4));

		let mut item: History<u64> = Default::default();

		for i in 0..6 {
			assert_eq!(item.get(&states.state(i)), None);
		}

		// setting value respecting branch build order
		for i in 1..6 {
			item.set(&states.state(i), i);
		}

		for i in 1..6 {
			assert_eq!(item.get(&states.state(i)), Some(&i));
		}

		let mut ref_3 = states.state(3);
		ref_3.limit_branch(1, None);
		assert_eq!(item.get(&ref_3), Some(&1));

		let mut ref_1 = states.state(1);
		ref_1.limit_branch(1, Some(0));
		assert_eq!(item.get(&ref_1), None);
		item.set(&ref_1, 11);
		assert_eq!(item.get(&ref_1), Some(&11));

		item = Default::default();

		// could rand shuffle if rand get imported later.
		let disordered = [
			[1,2,3,5,4],
			[2,5,1,3,4],
			[5,3,2,4,1],
		];
		for r in disordered.iter() {
			for i in r {
				item.set(&states.state(*i), *i);
			}
			for i in r {
				assert_eq!(item.get(&states.state(*i)), Some(i));
			}
		}

	}


	#[test]
	fn test_gc() {
		let states = test_states();
		let mut item: History<u64> = Default::default();
		// setting value respecting branch build order
		for i in 1..6 {
			item.set(&states.state(i), i);
		}

		let mut states1 = states.branches.clone();
		let action = [(1, true), (2, false), (3, false), (4, true), (5, false)];
		for a in action.iter() {
			if !a.1 {
				states1.remove(&a.0);
			}
		}
		// makes invalid tree (detaches 4)
		states1.get_mut(&1).map(|br| br.state.range.end -= 1);
		let states1: BTreeMap<_, _> = states1.iter().map(|(k,v)| (k, v.state())).collect();
		let mut item1 = item.clone();
		item1.gc(states1.iter().map(|(k, v)| ((&v.range, None), **k)).rev());
		assert_eq!(item1.get(&states.state(1)), None);
		for a in action.iter().skip(1) {
			if a.1 {
				assert_eq!(item1.get(&states.state(a.0)), Some(&a.0));
			} else {
				assert_eq!(item1.get(&states.state(a.0)), None);
			}
		}
	}

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
