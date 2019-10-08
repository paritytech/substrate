
// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Helper for managing the set of indexed available branches.

use std::collections::{BTreeMap};
use crate::Error;
use historied_data::tree::{BranchesStateTrait, BranchStatesRef, BranchStateRef};

#[derive(Clone, Default, Debug)]
/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to a full state
/// branch for a given branch index, here we use an in memory
/// copied representation in relation to an actual use case.
pub struct BranchRanges(Vec<BranchStatesRef>);

impl<'a> BranchesStateTrait<bool, u64, u64> for &'a BranchRanges {
	type Branch = &'a BranchStateRef;
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
		let l = self.0.len();
		if l > 0 {
			self.0[l - 1].branch_index
		} else {
			0
		}
	}

	fn iter(self) -> Self::Iter {
		BranchRangesIter(self, self.0.len())
	}

}

/// Iterator, contains index of last inner struct.
pub struct BranchRangesIter<'a>(&'a BranchRanges, usize);

impl<'a> Iterator for BranchRangesIter<'a> {
	type Item = (&'a BranchStateRef, u64);

	fn next(&mut self) -> Option<Self::Item> {
		if self.1 > 0 {
			Some((
				&(self.0).0[self.1 - 1].state,
				(self.0).0[self.1 - 1].branch_index,
			))
		} else {
			None
		}
	}
}

/// current branches range definition, indexed by branch
/// numbers.
///
/// New branches index are using `last_index`.
///
/// Also acts as a cache, storage can store
/// unknown db value as `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeSet {
	// TODO EMCH using a option value makes not sense when all in memory
	storage: BTreeMap<u64, Option<BranchStates>>,
	// TODO EMCH remove this?
	last_index: u64,
	/// treshold for possible node value, correspond
	/// roughly to last cannonical block branch index.
	treshold: u64,
}

const DEFAULT_START_TRESHOLD: u64 = 1;

impl Default for RangeSet {
	fn default() -> Self {
		RangeSet {
			storage: BTreeMap::new(),
			last_index: 0,
			treshold: DEFAULT_START_TRESHOLD,
		}
	}
}

impl RangeSet {

	#[cfg(test)]
	/// test access to treshold.
	pub fn range_treshold(&self) -> u64 {
		self.treshold
	}

	/// Iterator over all its range sets.
	pub fn reverse_iter_ranges(&self) -> impl Iterator<Item = (&BranchStateRef, u64)> {
		self.storage.iter().rev().filter_map(|(k, v)| v.as_ref().map(|v| (&v.state, *k)))
	}

	// TODO EMCH can rw lock over the latest accessed range (lru) and
	// return an clone of it (arc of the value so it will be fine). this is call by state_at that is call a lot!!!
	pub fn branch_ranges_from_cache(
		&self,
		mut branch_index: u64,
		block: Option<u64>,
	) -> BranchRanges {
		// TODO EMCH transform this method to an iterator!!!
		// (avoid some intermediatory Vec (eg when building Hashset)
		let mut result = Vec::new();
		if branch_index < self.treshold {
			return BranchRanges(result);
		}
		let mut previous_start = block.map(|b| b + 1).unwrap_or(u64::max_value());
		loop {
			if let Some(Some(BranchStates{
				state,
				parent_branch_index,
				..
			})) = self.storage.get(&branch_index) {
				// TODO EMCH consider vecdeque ??
				let state = if state.end > previous_start {
					if state.start >= previous_start {
						// empty branch stop here
						break;
					}
					BranchStateRef {
						start: state.start,
						end: previous_start,
					}
				} else { state.clone() };

				previous_start = state.start;

				result.insert(0, BranchStatesRef {
					state,
					branch_index,
				});

				branch_index = *parent_branch_index;
				if branch_index < self.treshold {
					break;
				}
			} else {
				debug_assert!(false, "inconsistent branch range cache");
				break;
			}
		}
		BranchRanges(result)
	}


	/// Return anchor index for this branch history:
	/// - same index as input if branch is not empty
	/// - parent index if branch is empty
	pub fn drop_state(
		&mut self,
		branch_index: u64,
	) -> Result<u64, Error<()>> {
		let mut do_remove = None;
		match self.storage.get_mut(&branch_index) {
			Some(Some(branch_state)) => {
				if let Some(drop_index) = branch_state.drop_state() {
					if drop_index == 0 {
						do_remove = Some(branch_state.parent_branch_index);
					} else {
						branch_state.can_append = false;
					}
				} else {
					// deleted branch, do nothing
				}
			},
			Some(None) => (), // already dropped.
			None => // TODO not sure keeping this error (we may want to clear storage)
				return Err(Error::InvalidRange),
		}

		if let Some(parent_index) = do_remove {
			self.storage.remove(&branch_index);
			Ok(parent_index)
		} else {
			Ok(branch_index)
		}
	}

	/// Return anchor index for this branch history:
	/// - same index as input if the branch was modifiable
	/// - new index in case of branch range creation
	pub fn add_state(
		&mut self,
		branch_index: u64,
		number: u64,
	) -> Result<u64, Error<()>> {
		let mut create_new = false;
		if branch_index == 0 || branch_index < self.treshold {
			create_new = true;
		} else { match self.storage.get_mut(&branch_index) {
			Some(Some(branch_state)) => {
				if branch_state.can_append && branch_state.can_add(number) {
					branch_state.add_state();
				} else {
					create_new = true;
				}
			},
			Some(None) => 
				return Err(Error::InvalidRange),
			None => // TODO not sure keeping this error (we may want to clear storage)
				return Err(Error::InvalidRange),
		}}

		if create_new {
			self.last_index += 1;


			let state = BranchStates::new(number, branch_index);
			self.storage.insert(self.last_index, Some(state));
			Ok(self.last_index)
		} else {
			Ok(branch_index)
		}
	}

	// TODO EMCH this access can be optimize at multiple places (by returning ref
	// instead of an anchor_id).
	pub fn state_ref(&self, branch_index: u64) -> Option<BranchStatesRef> {
		self.storage.get(&branch_index).and_then(|v| v.as_ref().map(|v| v.state_ref()))
			.map(|state| BranchStatesRef {
				branch_index,
				state,
			})
	}

	/// update the range set on import. returns a displaced leaf if there was one.
	pub fn import(
		&mut self,
		number: u64,
		parent_branch_index: u64,
		parent_branch_range: Option<BranchRanges>,
	) -> (BranchRanges, u64) {

		if let Some(mut branch_ranges) = parent_branch_range {
			let anchor_index = self.add_state(parent_branch_index, number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			if anchor_index == parent_branch_index {
				branch_ranges.0.pop();
			}
			branch_ranges.0.push(self.state_ref(anchor_index).expect("added just above"));
			(branch_ranges, anchor_index)
		} else {
			let anchor_index = self.add_state(parent_branch_index, number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			(
				BranchRanges(vec![self.state_ref(anchor_index).expect("added just above")]),
				anchor_index,
			)
		}
	}

	/// Apply a post finalize update of treshold: requires
	/// that values before new treshold are all clear (since
	/// we stop maintaining branches for them).
	pub fn update_finalize_treshold(
		&mut self,
		branch_index: u64,
		linear_index: u64,
		full: bool,
	) {

		if branch_index < self.treshold {
			return;
		}
		// we do not finalize current branch cause it
		// can contains other blocks
		self.treshold = branch_index;
		if !full {
			// remove cached value under treshold only
			let new_storage = self.storage.split_off(&(self.treshold));
			self.storage = new_storage;
			// set this branch as non appendable (ensure it get gc
			// at some point even if there is no branching).
			// Also if gc and treshold happen after this call,
			// ensure this branch can get remove.
			// TODO EMCH this can also make sense for full
			self.storage.get_mut(&branch_index)
				.map(|state| state.as_mut().map(|state| state.can_append = false));
		} else {
			let new_storage = self.storage.split_off(&(self.treshold));
			self.storage = new_storage;
			self.finalize_full(branch_index, linear_index);
		};
	}

	/// Apply a post finalize without considering treshold.
	/// TODO EMCH rename as it is also use to prepare a gc
	/// without moving the treshold first.
	///
	pub fn finalize_full(
		&mut self,
		branch_index: u64,
		linear_index: u64,
	) {
		if let Some(Some(state)) = self.storage.remove(&branch_index) {
			let mut child_anchor: BranchStates = state.clone();
			child_anchor.state.start = linear_index;
			let old_storage = std::mem::replace(&mut self.storage, BTreeMap::new());
			// insert anchor
			self.storage.insert(branch_index, Some(child_anchor.clone()));
			for (index, state) in old_storage.into_iter().filter_map(|(k, v)| v.map(|v| (k, v))) {
				// ordered property of branch index allows to skip in depth branch search
				if let Some(Some(parent_state)) = self.storage.get(&state.parent_branch_index) {
					// first state is splitted
					// use property that start of a branch - 1 is origin of parent
					// this is obvious for parent is first branch (truncated), but also
					// true for case where we revert some state.
					let linear_index_parent = state.state.start - 1;
					if linear_index_parent < parent_state.state.end
						&& linear_index_parent >= parent_state.state.start {
						self.storage.insert(index, Some(state));
					}
				}
			}
			// remove anchor block
			child_anchor.state.start += 1;
			if child_anchor.state.start < child_anchor.state.end {
				self.storage.insert(branch_index, Some(child_anchor.clone()));
			} else {
				self.storage.remove(&branch_index);
			}
		}
	
	}

	/// Revert some ranges, without any way to revert.
	/// Returning ranges for the parent index.
	/// TODO EMCH can remove ??
	pub fn revert(&mut self, branch_ix: u64) -> BranchRanges {
		let parent_branch_index = if branch_ix != 0 {
			self.drop_state(branch_ix)
				// silenced error
				.unwrap_or(0)
		} else {
			0
		};

		self.branch_ranges_from_cache(parent_branch_index, None)
	}

	#[cfg(test)]
	pub fn contains_range(&self, branch_index: u64, size: u64) -> bool {
		if let Some(Some(s)) = self.storage.get(&branch_index) {
			(s.state_ref().end - s.state_ref().start) == size
		} else {
			false
		}
	}

}

/// Stored states for a branch, it contains branch reference information,
/// structural information (index of parent branch) and fork tree building
/// information (is branch appendable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchStates {
	state: BranchStateRef,
	can_append: bool,
	parent_branch_index: u64,
}

impl Default for BranchStates {
	// initialize with one element
	fn default() -> Self {
		Self::new(0, 0)
	}
}

impl BranchStates {
	pub fn new(offset: u64, parent_branch_index: u64) -> Self {
		let offset = offset as u64;
		BranchStates {
			state: BranchStateRef {
				start: offset,
				end: offset + 1,
			},
			can_append: true,
			parent_branch_index,
		}
	}

	pub fn state_ref(&self) -> BranchStateRef {
		self.state.clone()
	}

	pub fn has_deleted_index(&self) -> bool {
		!self.can_append
	}

	pub fn add_state(&mut self) -> bool {
		if !self.has_deleted_index() {
			self.state.end += 1;
			true
		} else {
			false
		}
	}

	/// return possible dropped state
	pub fn drop_state(&mut self) -> Option<u64> {
		if self.state.end - self.state.start > 0 {
			self.state.end -= 1;
			Some(self.state.end)
		} else {
			None
		}
	}

	/// Return true if you can add this index.
	pub fn can_add(&self, index: u64) -> bool {
		index == self.state.end
	}

}

// TODO EMCH end from historied - data
#[cfg(test)]
mod test {
	use super::*;

	// set:
	// 0
	// |> 1: [10,1]
	// |> 2: [10,2] [11,1]
	//       |> 3:  [11,2] [12, 2]
	//		          | > 5: [12,1]
	//       |> 4:  [11,123] [12,1]
	// full finalize: 3
	// 0
	// |> 2: [10,2]
	//       |> 3:  [11,2]
	fn build_finalize_set() ->  (RangeSet, (u64, u64)) {
		let mut set = RangeSet::default();
		set.import(10, 0, None);
		let (b1, anchor_1) = set.import(10, 0, None);
		set.import(11, anchor_1, Some(b1.clone()));
		let (bf, finalize) = set.import(11, anchor_1, Some(b1.clone()));
		let (b2, anchor_2) = set.import(11, anchor_1, Some(b1));
		set.import(12, anchor_2, Some(b2));
		set.import(12, finalize, Some(bf.clone()));
		set.import(12, finalize, Some(bf));

		(set, (finalize, 11))
	}

	#[test]
	fn branch_range_finalize() {
		let with_full_finalize = |
			full: bool,
			ranges_valid: &[(u64, u64)],
			not_ranges: &[(u64, u64)],
		| {
			let (mut ranges, finalize) = build_finalize_set();

			let _ = ranges.update_finalize_treshold(finalize.0, finalize.1, full);

			assert!(ranges.range_treshold() == 3);

			for (range, size) in ranges_valid {
				assert!(ranges.contains_range(*range, *size), "contains {:?}", range);
			}
			for (range, size) in not_ranges {
				assert!(!ranges.contains_range(*range, *size), "contains {:?}", range);
			}
	
		};

		with_full_finalize(false,
			&[(3, 2), (4, 2), (5, 1)][..],
			&[(1, 1), (2, 2)][..],
		);
		with_full_finalize(true,
			// (3, 1) because finalized block is removed
			&[(3, 1), (5, 1)][..],
			&[(1, 1), (2, 2), (4, 2)][..],
		);
	}

}
