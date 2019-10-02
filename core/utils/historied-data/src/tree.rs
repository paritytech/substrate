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

//! Data store acyclic directed graph as tree.
//!
//! General structure is an array of branch, each branch originates
//! from another branch at designated index.
//!
//! No particular state (just present or missing).

use crate::linear::{
	MemoryOnly as BranchBackend,
	Serialized as SerializedInner,
	SerializedConfig,
};
use crate::HistoriedValue;
use crate::{as_usize, as_i};
use rstd::rc::Rc;
use rstd::vec::Vec;
use rstd::collections::btree_map::BTreeMap;
use rstd::convert::{TryFrom, TryInto};

/// Trait defining a state for querying or modifying a tree.
/// This is therefore the representation of a branch.
/// TODO EMCH rename to BranchesStateTrait?
pub trait TreeStateTrait<S, I, BI> {
	type Branch: BranchStateTrait<S, BI>;
	type Iter: Iterator<Item = (Self::Branch, I)>;

	fn get_branch(self, index: I) -> Option<Self::Branch>;

	/// Inclusive.
	fn last_index(self) -> I;

	/// Iterator.
	fn iter(self) -> Self::Iter;
}

/// Trait defining a state for querying or modifying a branch.
/// This is therefore the representation of a branch state.
pub trait BranchStateTrait<S, I> {

	fn get_node(&self, i: I) -> S;

	/// Inclusive.
	fn last_index(&self) -> I;
}

impl<'a> TreeStateTrait<bool, u64, u64> for &'a StatesRef {
	type Branch = (&'a BranchStateRef, Option<u64>);
	type Iter = StatesRefIter<'a>;

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

		StatesRefIter(self, end, upper_node_index)
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq, Eq))]
pub struct BranchState {
	/// Index of first element (only use for indexed access).
	/// Element before offset are not in state.
	offset: u64,
	/// number of elements: all elements equal or bellow
	/// this index are valid, over this index they are not.
	len: u64,
	/// Maximum index before first deletion, it indicates
	/// if the state is modifiable (when an element is dropped
	/// we cannot append and need to create a new branch).
	max_len_ix: u64,
}

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchStateRef {
	pub start: u64,
	pub end: u64,
}

impl<'a> BranchStateTrait<bool, u64> for (&'a BranchStateRef, Option<u64>) {

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

impl<'a> BranchStateTrait<bool, u64> for &'a BranchStateRef {

	fn get_node(&self, i: u64) -> bool {
		i >= self.start && i < self.end
	}

	fn last_index(&self) -> u64 {
		// underflow should not happen as long as branchstateref are not allowed to be empty.
		self.end - 1
	}

}



impl Default for BranchState {
	// initialize with one element
	fn default() -> Self {
		Self::new_from(0)
	}
}

impl BranchState {
	pub fn new_from(offset: u64) -> Self {
		BranchState {
			offset,
			len: 1,
			max_len_ix: offset,
		}
	}

	pub fn state_ref(&self) -> BranchStateRef {
		BranchStateRef {
			start: self.offset,
			end: self.offset + self.len,
		}
	}

	pub fn has_deleted_index(&self) -> bool {
		self.max_len_ix >= self.offset + self.len
	}

	pub fn add_state(&mut self) -> bool {
		if !self.has_deleted_index() {
			self.len += 1;
			self.max_len_ix += 1;
			true
		} else {
			false
		}
	}

	/// return possible dropped state
	pub fn drop_state(&mut self) -> Option<u64> {
		if self.len > 0 {
			self.len -= 1;
			Some(self.offset + self.len)
		} else {
			None
		}
	}

	/// Return true if state exists.
	pub fn get_state(&self, index: u64) -> bool {
		if index < self.offset {
			return false;
		}
		self.len > index + self.offset
	}

	pub fn latest_ix(&self) -> Option<u64> {
		if self.len > 0 {
			Some(self.offset + self.len - 1)
		} else {
			None
		}
	}

}

impl BranchStateRef {
	/// Return true if the state exists, false otherwhise.
	pub fn get_state(&self, index: u64) -> bool {
		index < self.end && index >= self.start
	}
}

/// At this point this is only use for testing and as an example
/// implementation.
/// It keeps trace of dropped value, and have some costy recursive
/// deletion.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct TestStates {
	branches: BTreeMap<u64, StatesBranch>,
	last_branch_index: u64,
	/// a lower treshold under which every branch are seen
	/// as containing only valid values.
	/// This can only be updated after a full garbage collection.
	valid_treshold: u64,
}

impl StatesBranch {
	pub fn branch_ref(&self) -> StatesBranchRef {
		StatesBranchRef {
			branch_index: self.branch_index,
			state: self.state.state_ref(),
		}
	}
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

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq, Eq))]
pub struct StatesBranch {
	// this is the key (need to growth unless full gc (can still have
	// content pointing to it even if it seems safe to reuse a previously
	// use ix).
	branch_index: u64,
	
	origin_branch_index: u64,
	origin_node_index: u64,

	state: BranchState,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatesBranchRef {
	pub branch_index: u64,
	pub state: BranchStateRef,
}


#[derive(Clone)]
/// Reference to state to use for query updates.
/// It is a single brannch path with branches ordered by branch_index.
///
/// Note that an alternative representation could be a pointer to full
/// tree state with a defined branch index implementing an iterator.
pub struct StatesRef {
	/// Oredered by branch index linear branch states.
	history: Rc<Vec<StatesBranchRef>>,
	/// Index is included, acts as length of history.
	upper_branch_index: Option<u64>,
	/// Index is included, acts as a branch ref end value.
	upper_node_index: Option<u64>,
}

/// Iterator, contains index of last inner struct.
pub struct StatesRefIter<'a>(&'a StatesRef, usize, Option<u64>);

impl<'a> Iterator for StatesRefIter<'a> {
	type Item = ((&'a BranchStateRef, Option<u64>), u64);

	fn next(&mut self) -> Option<Self::Item> {
		if self.1 > 0 {
			let upper_node_index = self.2.take();
			Some((
				(&self.0.history[self.1 - 1].state, upper_node_index),
				self.0.history[self.1 - 1].branch_index,
			))
		} else {
			None
		}
	}
}

impl StatesRef {
	/// limit to a given branch (included).
	/// Optionally limiting branch to a linear index (included).
	pub fn limit_branch(&mut self, branch_index: u64, node_index: Option<u64>) {
		debug_assert!(branch_index > 0);
		self.upper_branch_index = Some(branch_index);
		self.upper_node_index = node_index;
	}

	/// remove any limit.
	pub fn clear_limit(&mut self) {
		self.upper_branch_index = None;
		self.upper_node_index = None;
	}

}

impl TestStates {

	/// clear state but keep existing branch values (can be call after a full gc:
	/// enforcing no commited containing dropped values).
	pub fn unsafe_clear(&mut self) {
		self.branches.clear();
		self.last_branch_index = 0;
	}

	/// warning it should be the index of the leaf, otherwhise the ref will be incomplete.
	/// (which is fine as long as we use this state to query something that refer to this state.
	pub fn state_ref(&self, mut branch_index: u64) -> StatesRef {
		let mut result = Vec::new();
		let mut previous_origin_node_index = u64::max_value() - 1;
		while branch_index > self.valid_treshold {
			if let Some(branch) = self.branches.get(&branch_index) {
				let mut branch_ref = branch.branch_ref();
				if branch_ref.state.end > previous_origin_node_index + 1 {
					branch_ref.state.end = previous_origin_node_index + 1;
				}
				previous_origin_node_index = branch.origin_node_index;
				// vecdeque would be better suited
				result.insert(0, branch_ref);
				branch_index = branch.origin_branch_index;
			} else {
				break;
			}
		}
		StatesRef { history: Rc::new(result), upper_branch_index: None, upper_node_index: None }
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
			self.branches.insert(i, StatesBranch {
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

	pub fn branch_state(&self, branch_index: u64) -> Option<&BranchState> {
		self.branches.get(&branch_index)
			.map(|b| &b.state)
	}

	pub fn branch_state_mut(&mut self, branch_index: u64) -> Option<&mut BranchState> {
		self.branches.get_mut(&branch_index)
			.map(|b| &mut b.state)
	}

	/// this function can go into deep recursion with full scan, it indicates
	/// that the in memory model use here should only be use for small data or
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
				match self.branch_state_mut(i).map(|ls| ls.drop_state()) {
					Some(Some(li)) => self.apply_drop_state(i, li),
					Some(None) => break, // we keep empty branch
					None => break,
				}
			}
		}
	}
}

/// First field is the actual history against which we run
/// the state.
/// Second field is an optional value for the no match case.
/// TODO EMCH consider removing second field (not use out of test)
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(Vec<HistoryBranch<V>>, Option<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Vec::new(), None)
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
			S: TreeStateTrait<bool, I, BI>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
			BI: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		// TODO EMCH it does not seem stricly needed to pass
		// a full state, double index looks enough.
		// but this api can help using consistent state.
		if let Some((state_branch, state_index)) = state.iter().next() {
			if let Ok(state_index_usize) = state_index.try_into() {
				let state_index_u64 = state_index_usize as u64;
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
					if let Ok(index_usize) = state_branch.last_index().try_into() {
						let index = index_usize as u64;
						let mut history = BranchBackend::<V, u64>::default();
						history.push(HistoriedValue {
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
					}
				} else {
					self.node_set(branch_position, &state_branch, value)
				}
			}
		}
	}

	fn node_set<S, I>(&mut self, branch_index: usize, state: &S, value: V)
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		if let Ok(node_index_usize) = state.last_index().try_into() {
			let node_index_u64 = node_index_usize as u64;
			let history = &mut self.0[branch_index];
			let mut index = history.history.len();
			debug_assert!(index > 0);
			loop {
				if index == 0 || history.history[index - 1].index < node_index_u64 {
					let h_value = HistoriedValue {
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
	}

	/// Access to last valid value (non dropped state in history).
	/// When possible please use `get_mut` as it can free some memory.
	pub fn get<I, BI, S> (&self, state: S) -> Option<&V> 
		where
			S: TreeStateTrait<bool, I, BI>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
			BI: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let mut index = self.0.len();
		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		if index == 0 {
			return self.1.as_ref();
		}

		// TODO EMCH switch loops ? probably.
		for (state_branch, state_index) in state.iter() {
			while index > 0 {
				index -= 1;
				if let Ok(branch_index) = self.0[index].branch_index.try_into() {
					if let Ok(state_index) = state_index.try_into() {
						if state_index == branch_index {
							if let Some(result) = self.branch_get(index, &state_branch) {
								return Some(result)
							}
						}
					}
				}
			}
			if index == 0 {
				break;
			}
		}
		self.1.as_ref()
	}

	fn branch_get<S, I>(&self, index: usize, state: &S) -> Option<&V>
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let history = &self.0[index];
		let mut index = history.history.len();
		while index > 0 {
			index -= 1;
			if let Some(&v) = history.history.get(index).as_ref() {
				if let Ok(i) = (v.index as usize).try_into() {
					if state.get_node(i) {
						return Some(&v.value);
					}
				}
			}
		}
		None
	}

	/// Gc an historied value other its possible values.
	/// Iterator need to be reversed ordered by branch index.
	pub fn gc<IT, S, I>(&mut self, mut states: IT) 
		where
			IT: Iterator<Item = (S, I)>,
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		// state is likely bigger than history.
		let mut current_state = states.next();
		for branch_index in (0..self.0.len()).rev() {
			let history_branch = self.0[branch_index].branch_index;
			loop {
				if let Some(state) = current_state.as_ref() {
					if let Ok(state_index_usize) = state.1.try_into() {
						let state_index_u64 = state_index_usize as u64;
						if history_branch < state_index_u64 {
							current_state = states.next();
						} else if history_branch == state_index_u64 {
							let len = self.0[branch_index].history.len();
							for history_index in (0..len).rev() {
									
								let node_index = self.0[branch_index].history[history_index].index as usize;
								if let Ok(node_index) = node_index.try_into() {
									if !state.0.get_node(node_index) {
										if history_index == len - 1 {
											let _ = self.0[branch_index].history.pop();
										} else {
											let _ = self.0[branch_index].history.remove(history_index);
										}
									}
								}
							}
							if self.0[branch_index].history.len() == 0 {
								let _ = self.0.remove(branch_index);
							}
							break;
						} else {
							let _ = self.0.remove(branch_index);
							break;
						}
					}
					self.0.remove(branch_index);
					break;
				} else {
					break;
				}
			}
		}
	}
	
/*
	/// Access to last valid value (non dropped state in history).
	/// When possible please use `get_mut` as it can free some memory.
	pub fn get_mut(&mut self, state: &StatesRef) -> Option<&mut V> {
		let mut index = self.0.len();
		let mut index_state = state.history.len() - 1;

		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		if index == 0 || index_state == 0 {
			return self.1.as_mut();
		}
		while index > 0 && index_state > 0 {
			index -= 1;
			let branch_index = self.0[index].branch_index;

			while index_state > 0 && state.history[index_state].branch_index > branch_index {
				index_state -= 1;
			}
			if state.history[index_state].branch_index == branch_index {
				if let Some(result) = self.branch_get_unchecked_mut(branch_index, &state.history[index_state]) {
					return Some(result)
				}
			}
		}
		self.1.as_mut()
	}

	fn branch_get_unchecked_mut(&mut self, branch_index: u64, state: &StatesBranchRef) -> Option<&mut V> {
		let history = &mut self.0[branch_index as usize];
		let mut index = history.history.len();
		if index == 0 {
			return None;
		}
		while index > 0 {
			index -= 1;
			if let Some(&mut v) = history.history.get_mut(index).as_mut() {
				if v.index < state.state.end {
					return Some(&mut v.value);
				}
			}
		}
		None
	}
*/
}

impl<'a, F: SerializedConfig> Serialized<'a, F> {
	pub fn get<I, S> (&self, state: S) -> Option<&[u8]> 
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let mut index = self.0.len();
		if index == 0 {
			return None;
		}
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: state_index } = self.0.get_state(index);
			if state.get_node(as_i(state_index as usize)) {
				return Some(value)
			}
		}
		None
	}

	/// This append the value, and can only be use in an
	/// orderly fashion.
	pub fn push<S, I, BI>(&mut self, state: S, value: &[u8]) 
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let target_state_index = as_usize(state.last_index()) as u64;
		let index = self.0.len();
		if index > 0 {
			let last = self.0.get_state(index);
			debug_assert!(target_state_index >= last.index); 
			if target_state_index == last.index {
				self.0.pop();
			}
		}
		self.0.push(HistoriedValue {value, index: target_state_index});
	}

	/// keep an single history before the state.
	pub fn prune<S, I, BI>(&mut self, index: I) 
		where
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let from = as_usize(index) as u64;
		let len = self.0.len();
		for index in 0..len {
			let history = self.0.get_state(index);
			if history.index >= from {
				// delete all index up to index 
				self.0.truncate_start(index);
				break;
			}
		}
	}
	
}


#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
/// Serialized implementation when transaction support is not
/// needed.
pub struct Serialized<'a, F>(SerializedInner<'a, F>);

impl<'a, F> Into<Serialized<'a, F>> for SerializedInner<'a, F> {
	fn into(self) -> Serialized<'a, F> {
		Serialized(self)
	}
}

impl<'a, F> Into<SerializedInner<'a, F>> for Serialized<'a, F> {
	fn into(self) -> SerializedInner<'a, F> {
		self.0
	}
}

impl<'a, F: SerializedConfig> Default for Serialized<'a, F> {
	fn default() -> Self {
		SerializedInner::<'a, F>::default().into()
	}
}


#[cfg(test)]
mod test {
	use super::*;

	fn test_states() -> TestStates {
		let mut states = TestStates::default();
		assert_eq!(states.create_branch(1, 0, None), Some(1));
		// root branching.
		assert_eq!(states.create_branch(1, 0, None), Some(2));
		assert_eq!(Some(true), states.branch_state_mut(1).map(|ls| ls.add_state()));
		assert_eq!(states.create_branch(2, 1, None), Some(3));
		assert_eq!(states.create_branch(1, 1, Some(0)), Some(5));
		assert_eq!(states.create_branch(1, 1, Some(2)), None);
		assert_eq!(Some(true), states.branch_state_mut(1).map(|ls| ls.add_state()));
		assert_eq!(Some(Some(2)), states.branch_state_mut(1).map(|ls| ls.drop_state()));
		// cannot create when dropped happen on branch
		assert_eq!(Some(false), states.branch_state_mut(1).map(|ls| ls.add_state()));

		assert!(states.get(1, 1));
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _

		states
	}

	#[test]
	fn test_remove_attached() {
		let mut states = test_states();
		assert_eq!(Some(Some(1)), states.branch_state_mut(1).map(|ls| ls.drop_state()));
		assert!(states.get(3, 0));
		assert!(states.get(4, 0));
		states.apply_drop_state(1, 1);
		assert!(!states.get(3, 0));
		assert!(!states.get(4, 0));
	}

	#[test]
	fn test_state_refs() {
		let states = test_states();
		let ref_3 = vec![
			StatesBranchRef {
				branch_index: 1,
				state: BranchStateRef { start: 0, end: 2 },
			},
			StatesBranchRef {
				branch_index: 3,
				state: BranchStateRef { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state_ref(3).history, ref_3);

		let mut states = states;

		assert_eq!(states.create_branch(1, 1, Some(0)), Some(6));
		let ref_6 = vec![
			StatesBranchRef {
				branch_index: 1,
				state: BranchStateRef { start: 0, end: 1 },
			},
			StatesBranchRef {
				branch_index: 6,
				state: BranchStateRef { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state_ref(6).history, ref_6);

		states.valid_treshold = 3;
		let mut ref_6 = ref_6;
		ref_6.remove(0);
		assert_eq!(*states.state_ref(6).history, ref_6);
	}

	#[test]
	fn test_set_get() {
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let states = test_states();
		let mut item: History<u64> = Default::default();

		for i in 0..6 {
			assert_eq!(item.get(&states.state_ref(i)), None);
		}

		// setting value respecting branch build order
		for i in 1..6 {
			item.set(&states.state_ref(i), i);
		}

		for i in 1..6 {
			assert_eq!(item.get(&states.state_ref(i)), Some(&i));
		}

		let mut ref_3 = states.state_ref(3);
		ref_3.limit_branch(1, None);
		assert_eq!(item.get(&ref_3), Some(&1));

		let mut ref_1 = states.state_ref(1);
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
				item.set(&states.state_ref(*i), *i);
			}
			for i in r {
				assert_eq!(item.get(&states.state_ref(*i)), Some(i));
			}
		}

	}


	#[test]
	fn test_gc() {
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let states = test_states();
		let mut item: History<u64> = Default::default();
		// setting value respecting branch build order
		for i in 1..6 {
			item.set(&states.state_ref(i), i);
		}

		let mut states1 = states.branches.clone();
		let action = [(1, true), (2, false), (3, false), (4, true), (5, false)];
		for a in action.iter() {
			if !a.1 {
				states1.remove(&a.0);
			}
		}
		// makes invalid tree (detaches 4)
		states1.get_mut(&1).map(|br| br.state.len = 1);
		let states1: BTreeMap<_, _> = states1.iter().map(|(k,v)| (k, v.branch_ref())).collect();
		let mut item1 = item.clone();
		item1.gc(states1.iter().map(|(k, v)| ((&v.state, None), **k)).rev());
		assert_eq!(item1.get(&states.state_ref(1)), None);
		for a in action.iter().skip(1) {
			if a.1 {
				assert_eq!(item1.get(&states.state_ref(a.0)), Some(&a.0));
			} else {
				assert_eq!(item1.get(&states.state_ref(a.0)), None);
			}
		}

	}

}
