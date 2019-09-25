
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

use std::collections::{BTreeMap, BTreeSet, HashMap, btree_map::Entry};
use std::cmp::Reverse;
use crate::Error;
use std::hash::Hash as StdHash;
use std::convert::TryInto;


/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to a full state
/// branch for a given branch index, here we use an in memory
/// copied representation in relation to an actual use case.
pub type BranchRanges = Vec<StatesBranchRef>;


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatesBranchRef {
	pub branch_index: u64,
	pub state: LinearStatesRef,
}

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearStatesRef {
	pub start: u64,
	pub end: u64,
}

/// current branches range definition, indexed by branch
/// numbers.
///
/// New branches index are using `last_index`.
/// `treshold` is a branch index under which branches are undefined
/// but data there is seen as finalized.
///
/// Also acts as a cache, storage can store
/// unknown db value as `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeSet {
	storage: BTreeMap<u64, Option<LinearStates>>,
	last_index: u64,
	treshold: u64,
	// change and removed concern both storage and appendable
	changed: BTreeSet<u64>,
	removed: BTreeSet<u64>,
}

const DEFAULT_START_TRESHOLD: u64 = 1;

impl Default for RangeSet {
	fn default() -> Self {
		RangeSet {
			storage: BTreeMap::new(),
			last_index: 0,
			treshold: DEFAULT_START_TRESHOLD,
			changed: BTreeSet::new(),
			removed: BTreeSet::new(),
		}
	}
}

impl RangeSet {

	#[cfg(test)]
	/// test access to treshold.
	pub fn range_treshold(&self) -> u64 {
		self.treshold
	}

	#[cfg(test)]
	/// test access to strage.
	pub fn inner_storage(&self) -> &BTreeMap<u64, Option<LinearStates>> {
		&self.storage
	}


	/// Construct a new range set
	pub fn new(treshold: u64, last_index: u64) -> Self {
		RangeSet {
			storage: BTreeMap::new(),
			last_index,
			treshold,
			changed: BTreeSet::new(),
			removed: BTreeSet::new(),
		}
	}

	// TODO EMCH can rw lock over the latest accessed range (lru) and
	// return an clone of it (arc of the value so it will be fine). this is call by state_at that is call a lot!!!
	pub fn branch_ranges_from_cache(
		&self,
		mut branch_index: u64,
	) -> BranchRanges {
		// TODO EMCH transform this method to an iterator!!!
		// (avoid some intermediatory Vec (eg when building Hashset)
		let mut result = Vec::new();
		if branch_index < self.treshold {
			return result;
		}
		let mut previous_start = u64::max_value();
		loop {
			if let Some(Some(StatesBranch{ state, parent_branch_index, .. })) = self.storage.get(&branch_index) {
				// TODO EMCH consider vecdeque ??
				let state = if state.end > previous_start {
					LinearStatesRef {
						start: state.start,
						end: previous_start,
					}
				} else { state.clone() };

				previous_start = state.start;

				result.insert(0, StatesBranchRef {
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
		result
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
						self.removed.insert(branch_index);
						do_remove = Some(branch_state.parent_branch_index);
					} else {
						branch_state.can_append = false;
						self.changed.insert(branch_index);
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
					self.changed.insert(branch_index);
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


			let state = StatesBranch::new(number, branch_index);
			self.storage.insert(self.last_index, Some(state));
			self.changed.insert(self.last_index);
			Ok(self.last_index)
		} else {
			Ok(branch_index)
		}
	}

	// TODO EMCH this access can be optimize at multiple places (by returning ref
	// instead of an anchor_id).
	pub fn state_ref(&self, branch_index: u64) -> Option<StatesBranchRef> {
		self.storage.get(&branch_index).and_then(|v| v.as_ref().map(|v| v.state_ref()))
			.map(|state| StatesBranchRef {
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
				branch_ranges.pop();
			}
			branch_ranges.push(self.state_ref(anchor_index).expect("added just above"));
			(branch_ranges, anchor_index)
		} else {
			let anchor_index = self.add_state(parent_branch_index, number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			(vec![self.state_ref(anchor_index).expect("added just above")], anchor_index)
		}
	}

	/// Apply a post finalize update of treshold: requires
	/// that values before new treshold are all clear (since
	/// we stop maintaining branches for them).
	pub fn update_finalize_treshold(
		&mut self,
		branch_index: u64,
		full: bool,
	) {

		if branch_index <= self.treshold {
			return;
		}
		// range set update
		let old_treshold = self.treshold;
		// we do not finalize current branch cause it
		// can contains other blocks
		self.treshold = branch_index;
		let removed_ranges = if branch_index == 0 || !full {
			// remove cached value under treshold only
			let new_storage = self.storage.split_off(&(self.treshold));
			std::mem::replace(&mut self.storage, new_storage)
		} else {
			let new_storage = self.storage.split_off(&(self.treshold));
			let mut removed = std::mem::replace(&mut self.storage, new_storage);
			self.finalize_full(&mut removed, branch_index);
			removed
		};
		self.removed.extend(removed_ranges.keys().cloned());
	}

	/// Apply a post finalize without considering treshold.
	fn finalize_full(
		&mut self,
		output: &mut BTreeMap<u64, Option<LinearStates>>,
		branch_index: u64,
	) {
		// TODO EMCH consider working directly on ordered vec (should be fastest in most cases)
		let mut finalize_branches_map: BTreeMap<_, _> = self.branch_ranges_from_cache(branch_index)
			.into_iter().map(|r| (r.branch_index, r.state)).collect();

		for (index, state) in self.storage.iter_mut() {
			if let Some(final_state) = finalize_branches_map.remove(&index) {
				// update for case where end of range differs (see `branch_ranges_from_cache`).
				state.as_mut().map(|state| {
					if state.state != final_state {
						output.insert(*index, Some(state.clone()));
						state.state = final_state;
						state.can_append = false;
					}
				});
			} else {
				output.insert(*index, state.take());
			}
		}
	}

	#[cfg(test)]
	pub fn test_finalize_full(
		&mut self,
		branch_index: u64,
	) {
		let mut removed_ranges = BTreeMap::new();
		self.finalize_full(&mut removed_ranges, branch_index);
		self.removed.extend(removed_ranges.keys().cloned());
	}

	/// Revert some ranges, without any way to revert.
	/// Returning ranges for the parent index.
	pub fn revert(&mut self, branch_ix: u64) -> BranchRanges {
		let parent_branch_index = if branch_ix != 0 {
			self.drop_state(branch_ix)
				// silenced error
				.unwrap_or(0)
		} else {
			0
		};

		self.branch_ranges_from_cache(parent_branch_index)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatesBranch {
	state: LinearStatesRef,
	can_append: bool,
	parent_branch_index: u64,
}


// TODO EMCH temporary structs until merge with historied-data branch.

type LinearStates = StatesBranch;

impl Default for LinearStates {
	// initialize with one element
	fn default() -> Self {
		Self::new(0, 0)
	}
}

impl LinearStates {
	pub fn new(offset: u64, parent_branch_index: u64) -> Self {
		let offset = offset as u64;
		LinearStates {
			state: LinearStatesRef {
				start: offset,
				end: offset + 1,
			},
			can_append: true,
			parent_branch_index,
		}
	}

	pub fn state_ref(&self) -> LinearStatesRef {
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

	/// Return true if state exists.
	pub fn get_state(&self, index: u64) -> bool {
		index < self.state.end && index >= self.state.start
	}

	/// Return true if you can add this index.
	pub fn can_add(&self, index: u64) -> bool {
		index == self.state.end
	}

	pub fn latest_ix(&self) -> Option<u64> {
		if self.state.end - self.state.start > 0 {
			Some(self.state.end - 1)
		} else {
			None
		}
	}

}

// TODO EMCH end from historied - data
//
mod test {
	use super::*;

	// set:
	// 0
	// |> 1: [10,1]
	// |> 2: [10,2] [11,1]
	//       |> 3:  [11,2]
	//       |> 4:  [11,123] [12,1]
	// full finalize: 3
	// 0
	// |> 2: [10,2]
	//       |> 3:  [11,2]
	fn build_finalize_set() ->  (RangeSet, u64) {
		let mut set = RangeSet::default();
		set.import(10, 0, None);
		let (b1, anchor_1) = set.import(10, 0, None);
		set.import(11, anchor_1, Some(b1.clone()));
		let (_, finalize) = set.import(11, anchor_1, Some(b1.clone()));
		let (b2, anchor_2) = set.import(11, anchor_1, Some(b1));
		set.import(12, anchor_2, Some(b2));

		(set, finalize)
	}

	#[test]
	fn branch_range_finalize() {
		const PREFIX: &[u8] = b"prefix";
		const TRESHOLD: &[u8] = b"hijkl";
		const LAST_INDEX: &[u8] = b"mnopq";
		let with_full_finalize = |
			full: bool,
			ranges_valid: &[(u64, u64)],
			not_ranges: &[(u64, u64)],
			ranges2: Option<&[(u64, u64)]>,
		| {
			let (mut ranges, finalize) = build_finalize_set();

			// test ranges changes
			if let Some(range2) = ranges2 {
				let mut ranges2 = ranges.clone();
				let _ = ranges2.test_finalize_full(finalize);
				for (range, size) in range2 {
					assert!(ranges2.contains_range(*range, *size), "{} {}", range, size);
				}
			}

			let _ = ranges.update_finalize_treshold(finalize, full);

			assert!(ranges.range_treshold() == 3);

			for (range, size) in ranges_valid {
				assert!(ranges.contains_range(*range, *size), "contains {:?}", range);
			}
			for (range, size) in not_ranges {
				assert!(!ranges.contains_range(*range, *size), "contains {:?}", range);
			}
	
		};

		with_full_finalize(false,
			&[(3, 1), (4, 2)][..],
			&[(1, 1), (2, 2)][..],
			None,
		);
		with_full_finalize(true,
			&[(3, 1)][..],
			&[(1, 1), (2, 2), (4, 2)][..],
			// here 2, 1 test state removal from finalize branch
			Some(&[(2, 1), (3, 1)][..]),
		);
	}

}
