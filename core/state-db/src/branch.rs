
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
//!
//! This allows managing an index over the multiple block forks
//! in the state db.
//!
//! State db use block hash to address blocks in different branches.
//!
//! These utilities aims at managing for trees of fork and indexed
//! way to address blocks in fork. That is the block number and a
//! branch number.
//! Branch number are not allows to change, once set they are kept.
//! This property is important to avoid any data update for on branch
//! modification.
//! Therefore the tree formed by these branch inexing is not balanced,
//! branch are created sequentially to block addition with a very
//! simple rules: if the block can be added to parent branch (number following
//! the last block and there was no block with this numbering before) it
//! uses the same index, otherwhise a new sequential index is used.
//! It should be noticed that parent branch therefore always have a smaller
//! index than children.

use std::collections::{BTreeMap};
use historied_data::tree::{BranchesStateTrait, BranchState, BranchRange};

#[derive(Clone, Default, Debug)]
/// State needed for queries and updates operations.
/// That is a subset of the full branch ranges set.
///
/// Values are ordered by branch indexes so from the root
/// to the leaf of the fork tree.
/// Only a single tree branch path is present.
///
/// This achieve the same purpose  as a pointer to the full state
/// and a branch index corresponding to the leaf to query, but
/// with memory aligned state.
/// We prefer using an in memory copy of the full fork path because it
/// fits better the model where we do a big number of queries on a single
/// state (a block processing).
pub struct BranchRanges(Vec<BranchState>);

impl<'a> BranchesStateTrait<bool, u64, u64> for &'a BranchRanges {
	type Branch = &'a BranchRange;
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

/// Iterator over a `BranchRanges`, it iterates over
/// every branches from the leaf to the root.
pub struct BranchRangesIter<'a>(&'a BranchRanges, usize);

impl<'a> Iterator for BranchRangesIter<'a> {
	type Item = (&'a BranchRange, u64);

	fn next(&mut self) -> Option<Self::Item> {
		if self.1 > 0 {
			self.1 -= 1;
			Some((
				&(self.0).0[self.1].range,
				(self.0).0[self.1].branch_index,
			))
		} else {
			None
		}
	}
}

/// Current full state for the tree(s).
/// It can contain multiple tries as it only store
/// branch elements indexed by their respective branch
/// index.
///
/// New branches index are sequentially returned by a `last_index`
/// counter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeSet {
	storage: BTreeMap<u64, BranchStateFull>,
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
	/// Access to treshold for tests only.
	pub fn range_treshold(&self) -> u64 {
		self.treshold
	}

	/// Iterator over all its branch range sets.
	/// The iterator order is reversed so it will return branches from leaf to root.
	pub fn reverse_iter_ranges(&self) -> impl Iterator<Item = (&BranchRange, u64)> {
		self.storage.iter().rev().map(|(k, v)| (&v.state, *k))
	}

	/// For a a given branch, returns its tree path.
	/// If block number is undefined, return the path up to the latest block
	/// of the last branch.
	///
	/// Note that this method is a bit costy and a caching could be use,
	/// but it only really need to be call once per block processing.
	pub fn branch_ranges(
		&self,
		mut branch_index: u64,
		block: Option<u64>,
	) -> BranchRanges {
		let mut result = Vec::new();
		if branch_index < self.treshold {
			return BranchRanges(result);
		}
		let mut previous_start = block.map(|b| b + 1).unwrap_or(u64::max_value());
		loop {
			if let Some(BranchStateFull {
				state,
				parent_branch_index,
				..
			}) = self.storage.get(&branch_index) {
				let range = if state.end > previous_start {
					if state.start >= previous_start {
						// empty branch stop here
						break;
					}
					BranchRange {
						start: state.start,
						end: previous_start,
					}
				} else { state.clone() };

				previous_start = state.start;

				result.push(BranchState {
					range,
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
		result.reverse();
		BranchRanges(result)
	}

	/// Drop last block from a branch.
	///
	/// Returns anchor index for this branch history:
	/// - same index as input if branch is not empty
	/// - parent index if branch is empty
	fn drop_state(
		&mut self,
		branch_index: u64,
	) -> u64 {
		let mut do_remove = None;
		match self.storage.get_mut(&branch_index) {
			Some(branch_state) => {
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
			None => (),
		}

		if let Some(parent_index) = do_remove {
			self.storage.remove(&branch_index);
			parent_index
		} else {
			branch_index
		}
	}

	/// Add a new numbered block into a branch.
	///
	/// Return anchor index for this branch history:
	/// - same index as input if the branch was modifiable
	/// - new index in case of branch range creation
	fn add_state(
		&mut self,
		branch_index: u64,
		number: u64,
	) -> u64 {
		let mut create_new = false;
		if branch_index == 0 || branch_index < self.treshold {
			create_new = true;
		} else { 
			let branch_state = self.storage.get_mut(&branch_index)
				.expect("Inconsistent state on new block");
			if branch_state.can_append && branch_state.can_add(number) {
				branch_state.add_state();
			} else {
				create_new = true;
			}
		}

		if create_new {
			self.last_index += 1;

			let state = BranchStateFull::new(number, branch_index);
			self.storage.insert(self.last_index, state);
			self.last_index
		} else {
			branch_index
		}
	}

	/// Get the branch reference for a given branch index if it exists.
	pub fn range(&self, branch_index: u64) -> Option<BranchState> {
		self.storage.get(&branch_index).map(|v| v.range())
			.map(|range| BranchState {
				branch_index,
				range,
			})
	}

	/// Updates the range set on import (defined by its number in branch (block number).
	/// Returns the corresponding branch ranges and the branch index for this block.
	///
	/// This is the same as `add_state` but returning the branch range for the imported
	/// block and with a possible branch ranges as parameter.
	/// This avoids branch ranges query when possible.
	pub fn import(
		&mut self,
		number: u64,
		parent_branch_index: u64,
		parent_branch_range: Option<BranchRanges>,
	) -> (BranchRanges, u64) {

		if let Some(mut branch_ranges) = parent_branch_range {
			let anchor_index = self.add_state(parent_branch_index, number);
			if anchor_index == parent_branch_index {
				branch_ranges.0.pop();
			}
			branch_ranges.0.push(self.range(anchor_index).expect("added just above"));
			(branch_ranges, anchor_index)
		} else {
			let anchor_index = self.add_state(parent_branch_index, number);
			(
				BranchRanges(vec![self.range(anchor_index).expect("added just above")]),
				anchor_index,
			)
		}
	}

	/// Apply a post finalize update of treshold: requires
	/// that values before new treshold are all clear (since
	/// we stop maintaining branches for them).
	/// Clear here means that values for those block gets canonicalized
	/// and either written in the backend db or deleted for non canonical
	/// blocks.
	/// If `full` parameter is not set to true, the operation is
	/// runing only a fast branch index based removal.
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
			self.storage.get_mut(&branch_index)
				.map(|state| state.can_append = false);
		} else {
			let new_storage = self.storage.split_off(&(self.treshold));
			self.storage = new_storage;
			self.finalize_full(branch_index, linear_index);
		};
	}

	/// Apply a post finalize without considering treshold.
	/// Will drop from state all branches that are not attached
	/// to the canonical block in parameter.
	pub fn finalize_full(
		&mut self,
		branch_index: u64,
		linear_index: u64,
	) {
		if let Some(state) = self.storage.remove(&branch_index) {
			let mut child_anchor: BranchStateFull = state.clone();
			child_anchor.state.start = linear_index;
			let old_storage = std::mem::replace(&mut self.storage, BTreeMap::new());
			// insert anchor block
			self.storage.insert(branch_index, child_anchor.clone());
			for (index, state) in old_storage.into_iter() {
				// ordered property of branch index allows to skip in depth branch search
				if let Some(parent_state) = self.storage.get(&state.parent_branch_index) {
					// first state is splitted
					// use property that start of a branch - 1 is origin of parent
					// this is obvious for parent is first branch (truncated), but also
					// true for case where we revert some state.
					let linear_index_parent = state.state.start - 1;
					if linear_index_parent < parent_state.state.end
						&& linear_index_parent >= parent_state.state.start {
						self.storage.insert(index, state);
					}
				}
			}
			// remove anchor block
			child_anchor.state.start += 1;
			if child_anchor.state.start < child_anchor.state.end {
				self.storage.insert(branch_index, child_anchor.clone());
			} else {
				self.storage.remove(&branch_index);
			}
		}
	
	}

	/// Revert a block for a branch index.
	/// Returning new branch index after this removal.
	pub fn revert(&mut self, branch_ix: u64) -> u64 {
		if branch_ix != 0 {
			self.drop_state(branch_ix)
		} else {
			0
		}
	}

	#[cfg(test)]
	pub fn contains_range(&self, branch_index: u64, size: u64) -> bool {
		if let Some(s) = self.storage.get(&branch_index) {
			(s.range().end - s.range().start) == size
		} else {
			false
		}
	}

}

/// Stored state for a branch, it contains branch reference information,
/// structural information (index of parent branch) and fork tree building
/// information (is branch appendable).
#[derive(Debug, Clone, PartialEq, Eq)]
struct BranchStateFull {
	state: BranchRange,
	can_append: bool,
	parent_branch_index: u64,
}

impl Default for BranchStateFull {
	// initialize with one element
	fn default() -> Self {
		Self::new(0, 0)
	}
}

impl BranchStateFull {
	fn new(offset: u64, parent_branch_index: u64) -> Self {
		let offset = offset as u64;
		BranchStateFull {
			state: BranchRange {
				start: offset,
				end: offset + 1,
			},
			can_append: true,
			parent_branch_index,
		}
	}

	fn range(&self) -> BranchRange {
		self.state.clone()
	}

	fn has_deleted_index(&self) -> bool {
		!self.can_append
	}

	fn add_state(&mut self) -> bool {
		if !self.has_deleted_index() {
			self.state.end += 1;
			true
		} else {
			false
		}
	}

	fn drop_state(&mut self) -> Option<u64> {
		if self.state.end - self.state.start > 0 {
			self.state.end -= 1;
			Some(self.state.end)
		} else {
			None
		}
	}

	fn can_add(&self, index: u64) -> bool {
		index == self.state.end
	}

}

#[cfg(test)]
mod test {
	use super::*;

	// set:
	// 0
	// |> 1: [10,1]
	// |> 2: [10,2] [11,1]
	//       |> 3:  [11,2] [12, 2]
	//              | > 5: [12,1]
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
