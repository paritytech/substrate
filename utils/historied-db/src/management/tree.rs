// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Implementation of state management for tree like
//! state.
//!
//! State changes are limited so resulting tree is rather unbalance.
//! This is best when there is not to many branch (fork)

	// TODO some strategie to close a long branch that gets
	// behind multiple fork? This should only be usefull
	// for high number of modification, small number of
	// fork. The purpose is to avoid history where meaningfull
	// value is always in a low number branch behind a few fork.
	// A longest branch pointer per history is also a viable
	// strategy and avoid fragmenting the history to much.


use sp_std::ops::{AddAssign, SubAssign};
use sp_std::collections::btree_map::BTreeMap;
use sp_std::vec::Vec;
use sp_std::boxed::Box;
use sp_std::fmt::Debug;
use num_traits::One;
use crate::historied::linear::LinearGC;
use crate::{StateIndex, Latest};
use crate::management::{ManagementMut, Management, Migrate, ForkableManagement};
use codec::{Codec, Encode, Decode};
use crate::mapped_db::{MappedDB, Map as MappedDbMap, Variable as MappedDbVariable, MapInfo, VariableInfo};
use derivative::Derivative;

/// Base trait to give access to 'crate::mapped_db::MappedDB'
/// storage for `TreeManagement`.
///
/// If no backend storage is needed, a blank implementation
/// is provided for type '()'
pub trait TreeManagementStorage: Sized {
	/// Do we keep trace of changes.
	const JOURNAL_CHANGES: bool;
	type Storage: MappedDB + Send + Sync;
	type Mapping: MapInfo + Send + Sync;
	type JournalDelete: MapInfo + Send + Sync;
	type LastIndex: VariableInfo + Send + Sync;
	type NeutralElt: VariableInfo + Send + Sync;
	type TreeMeta: VariableInfo + Send + Sync;
	type TreeState: MapInfo + Send + Sync;
}

impl TreeManagementStorage for () {
	const JOURNAL_CHANGES: bool = false;
	type Storage = ();
	type Mapping = ();
	type JournalDelete = ();
	type LastIndex = ();
	type NeutralElt = ();
	type TreeMeta = ();
	type TreeState = ();
}

/// States for a branch, it contains branch reference information,
/// structural information (index of parent branch) and fork tree building
/// information (is branch appendable).
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode)]
pub struct BranchState<I, BI> {
	/// Range of branch indexes for this 
	state: BranchRange<BI>,
	/// does a state get rollback.
	can_append: bool,
	/// is the branch latest.
	is_latest: bool,
	/// Branch index for this branch start index minus one.
	parent_branch_index: I,
}

/// This is a simple range of contiguous indexes.
#[derive(Debug, Clone, Default, PartialEq, Eq, Encode, Decode)]
pub struct BranchRange<I> {
	/// Start index, inclusive.
	pub start: I,
	/// End index, exclusive.
	pub end: I,
}

/// Full state of current tree layout.
/// It contains all layout information for branches
/// states.
/// Branches are indexed by a sequential index.
/// Element of branches are indexed by a secondary
/// sequential indexes.
///
/// New branches index are defined by using `last_index`.
///
/// Also acts as a cache, storage can store
/// unknown db value as `None`.
///
/// NOTE that the single element branch at default index
/// containing the default branch index element does always
/// exist by convention.
#[derive(Derivative)]
#[derivative(Debug(bound="I: Debug, BI: Debug, S::Storage: Debug"))]
#[derivative(Clone(bound="I: Clone, BI: Clone, S::Storage: Clone"))]
#[cfg_attr(test, derivative(PartialEq(bound="I: PartialEq, BI: PartialEq, S::Storage: PartialEq")))]
pub struct Tree<I: Ord, BI, S: TreeManagementStorage> {
	/// Maps the different branches with their index.
	pub(crate) storage: MappedDbMap<I, BranchState<I, BI>, S::Storage, S::TreeState>,
	pub(crate) meta: MappedDbVariable<TreeMeta<I, BI>, S::Storage, S::TreeMeta>,
	/// serialization backend.
	pub(crate) serialize: S::Storage,
	/// Journal of changed indexes (only used when 'TreeManagementStorage::JOURNAL_CHANGES' is true).
	/// Indexed by changed branch index, it contains either new end index or delete ('None') and
	/// previous range value.
	///
	/// This will be use to create Gc or Migrate.
	pub(crate) journal_delete: MappedDbMap<I, (Option<BI>, BranchRange<BI>), S::Storage, S::JournalDelete>,
}

#[derive(Derivative, Encode, Decode)]
#[derivative(Debug(bound="I: Debug, BI: Debug"))]
#[derivative(Clone(bound="I: Clone, BI: Clone"))]
#[cfg_attr(test, derivative(PartialEq(bound="I: PartialEq, BI: PartialEq")))]
/// All meta for our tree management, in a single struct for serializing.
pub(crate) struct TreeMeta<I, BI> {
	/// Last branch index added, next new branch will increment it.
	pub(crate) last_index: I,
	/// Treshold for possible node value, correspond
	/// roughly to last cannonical block branch index.
	/// If at default state value, we go through simple storage.
	pub(crate) composite_treshold: (I, BI),
	/// Next value for composite treshold (requires data migration
	/// to switch current treshold but can already be use by gc).
	pub(crate) next_composite_treshold: Option<(I, BI)>,
	/// Pruned history index, all history before this cannot be queried.
	/// Those state can be pruned.
	pub(crate) pruning_treshold: Option<BI>,
	/// Is composite latest, so can we write its last state (only
	/// possible on new or after a migration).
	pub(crate) composite_latest: bool,
}

impl<I: Default, BI: Default> Default for TreeMeta<I, BI> {
	fn default() -> Self {
		TreeMeta {
			last_index: I::default(),
			composite_treshold: Default::default(),
			next_composite_treshold: None,
			pruning_treshold: None,
			composite_latest: true,
		}
	}
}

impl<I, BI, S> Default for Tree<I, BI, S>
	where
		I: Ord + Default,
		BI: Default,
		S: TreeManagementStorage,
		S::Storage: Default,
{
	fn default() -> Self {
		let serialize = S::Storage::default();
		let storage = MappedDbMap::default_from_db(&serialize);
		let journal_delete = MappedDbMap::default_from_db(&serialize);
		Tree {
			storage,
			journal_delete,
			meta: Default::default(),
			serialize,
		}
	}
}

impl<I, BI, S> Tree<I, BI, S>
	where
		I: Ord + Default + Codec,
		BI: Default + Codec,
		S: TreeManagementStorage,
{
	pub fn from_ser(mut serialize: S::Storage) -> Self {
		let storage = MappedDbMap::default_from_db(&serialize);
		let journal_delete = MappedDbMap::default_from_db(&serialize);
		Tree {
			storage,
			journal_delete,
			meta: MappedDbVariable::from_ser(&mut serialize),
			serialize,
		}
	}
}

/// Gc against a current tree state.
/// This requires going through all of a historied value
/// branches and should be use when gc happens rarely.
#[derive(Clone, Debug)]
pub struct TreeStateGc<I, BI> {
	/// see Tree `storage`
	pub(crate) storage: BTreeMap<I, BranchState<I, BI>>,
	/// see TreeMeta `composite_treshold`
	pub(crate) composite_treshold: (I, BI),
	/// All data before this can get pruned for composite non forked part.
	pub(crate) pruning_treshold: Option<BI>,
}

/// Gc against a given set of changes.
/// This should be use when there is few state changes,
/// or frequent migration.
/// Generally if management collect those information (see associated
/// constant `JOURNAL_CHANGES`) this gc should be use.
#[derive(Clone, Debug)]
pub struct DeltaTreeStateGc<I, BI> {
	/// Set of every branch that get reduced (new end stored) or deleted.
	pub(crate) storage: BTreeMap<I, (Option<BI>, BranchRange<BI>)>,
	/// New composite treshold value, this is not strictly needed but
	/// potentially allows skipping some iteration into storage.
	pub(crate) composite_treshold: (I, BI),
	/// All data before this can get pruned for composite non forked part.
	pub(crate) pruning_treshold: Option<BI>,
}

#[derive(Clone, Debug)]
pub enum MultipleGc<I, BI> {
	Journaled(DeltaTreeStateGc<I, BI>),
}

impl<I, BI> MultipleMigrate<I, BI>
	where
		I: Clone,
		BI: Clone + Ord + AddAssign<BI> + One,
{
	/// Return upper limit (all state before it are touched),
	/// and explicit touched state.
	/// Allows targetting journals when migrating.
	pub fn touched_state(&self) -> (Option<BI>, impl Iterator<Item = (I, BI)>) {
		let (pruning, touched) = match self {
			MultipleMigrate::JournalGc(gc) => {
				let iter = Some(
					gc.storage.clone().into_iter()
						.map(|(index, (change, old))| {
							let mut bindex = old.start;
							let end = old.end;
							sp_std::iter::from_fn(move || {
								if bindex < end {
									let result = Some(bindex.clone());
									bindex += BI::one();
									result
								} else {
									None
								}
							}).filter_map(move |branch_index| match change.as_ref() {
								Some(new_end) => if &branch_index >= new_end {
									Some((index.clone(), branch_index))
								} else {
									None
								},
								None => Some((index.clone(), branch_index)),
							})
						}).flatten()
				);
				(gc.pruning_treshold.clone(), iter)
			},
			MultipleMigrate::Noops => {
				(None, None)
			},
		};

		(pruning, touched.into_iter().flatten())
	}
}

impl<I: Ord, BI, S: TreeManagementStorage> Tree<I, BI, S> {
	pub fn ser(&mut self) -> &mut S::Storage {
		&mut self.serialize
	}
}

#[derive(Derivative)]
#[derivative(Debug(bound="H: Debug, I: Debug, BI: Debug, S::Storage: Debug"))]
#[derivative(Clone(bound="H: Clone, I: Clone, BI: Clone, S::Storage: Clone"))]
#[cfg_attr(test, derivative(PartialEq(bound="H: PartialEq, I: PartialEq, BI: PartialEq, S::Storage: PartialEq")))]
pub struct TreeManagement<H: Ord, I: Ord, BI, S: TreeManagementStorage> {
	state: Tree<I, BI, S>,
	/// Map a given tag to its state index.
	ext_states: MappedDbMap<H, (I, BI), S::Storage, S::Mapping>,
	last_added: MappedDbVariable<((I, BI), Option<H>), S::Storage, S::LastIndex>,
}

pub struct RegisteredConsumer<
	H: Ord + 'static,
	I: Ord + 'static,
	BI: 'static,
	S: TreeManagementStorage + 'static,
>(
	Vec<Box<dyn super::ManagementConsumer<H, TreeManagement<H, I, BI, S>>>>,
);

impl<H, I, BI, S> Default for RegisteredConsumer<H, I, BI, S>
	where
		H: Ord,
		I: Ord,
		S: TreeManagementStorage,
{
	fn default() -> Self {
		RegisteredConsumer(Vec::new())
	}
}

impl<H, I, BI, S> Default for TreeManagement<H, I, BI, S>
	where
		H: Ord,
		I: Default + Ord,
		BI: Default,
		S: TreeManagementStorage,
		S::Storage: Default,
{
	fn default() -> Self {
		let tree = Tree::default();
		let ext_states = MappedDbMap::default_from_db(&tree.serialize);
		TreeManagement {
			state: tree,
			ext_states,
			last_added: Default::default(),
		}
	}
}

impl<H, I, BI, S> TreeManagement<H, I, BI, S>
	where
		H: Ord + Codec,
		I: Default + Ord + Codec,
		BI: Default + Codec,
		S: TreeManagementStorage,
{
	/// Initialize from a default serializing backend.
	pub fn from_ser(serialize: S::Storage) -> Self {
		let ext_states = MappedDbMap::default_from_db(&serialize);
		TreeManagement {
			ext_states,
			last_added: MappedDbVariable::from_ser(&serialize),
			state: Tree::from_ser(serialize),
		}
	}

	/// Also should guaranty to flush change (but currently implementation
	/// writes synchronously).
	pub fn extract_ser(self) -> S::Storage {
		self.state.serialize
	}

	/// Access serializing backend.
	pub fn ser(&mut self) -> &mut S::Storage {
		&mut self.state.serialize
	}

	/// Read pointer access to serializing backend.
	pub fn ser_ref(&self) -> &S::Storage {
		&self.state.serialize
	}
}

impl<H, I, BI, S> TreeManagement<H, I, BI, S>
	where
		H: Clone + Ord + Codec,
		I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
		BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
		S: TreeManagementStorage,
{
	/// Associate a state for the initial root (default index).
	pub fn map_root_state(&mut self, root: H) {
		self.ext_states.mapping(self.state.ser()).insert(root, Default::default());
	}

	/// Canonicalize a fork plan up to a given index.
	pub fn canonicalize(&mut self, branch: ForkPlan<I, BI>, switch_index: (I, BI), prune_index: Option<BI>) -> bool {
		// TODO makes last index the end of this canonicalize branch

		let ext_states = &mut self.ext_states;
		let mut collect_dropped = Vec::new();
		let mut remove_tag = move |i: &I, bi: &BI, ser: &mut S::Storage| {
			let mut ext_states = ext_states.mapping(ser);
			let state = (i.clone(), bi.clone());
			let start = collect_dropped.len();
			// TODO again cost of reverse lookup: consider double ext_states
			if let Some(h) = ext_states.iter()
				.find(|(_k, v)| v == &state)
				.map(|(k, _v)| k.clone()) {
				collect_dropped.push(h);
			}
			for h in &collect_dropped[start..] {
				ext_states.remove(h);
			}
		};
	
		let mut filter: BTreeMap<_, _> = Default::default();
		for h in branch.history.into_iter() {
			//if h.state.end > switch_index.1 {
			if h.state.start < switch_index.1 {
				filter.insert(h.index, h.state);
			}
		}
		let mut change = false;
		let mut to_change = Vec::new();
		let mut to_remove = Vec::new();
		for (branch_ix, mut branch) in self.state.storage.mapping(&mut self.state.serialize).iter() {
			if branch.state.start < switch_index.1 {
				if let Some(ref_range) = filter.get(&branch_ix) {
					debug_assert!(ref_range.start == branch.state.start);
					debug_assert!(ref_range.end <= branch.state.end);
					if ref_range.end < branch.state.end {
						let old = branch.state.clone();
						branch.state.end = ref_range.end.clone();
						branch.can_append = false;
						to_change.push((branch_ix, branch, old));
					}
				} else {
					to_remove.push((branch_ix.clone(), branch.state.clone()));
				}
			}
		}
		if to_remove.len() > 0 {
			change = true;
			for to_remove in to_remove {
				let mut index = to_remove.1.start.clone();
				while index < to_remove.1.end {
					remove_tag(&to_remove.0, &index, &mut self.state.serialize);
					index += One::one();
				}
				self.state.register_change(&to_remove.0, to_remove.1, None);
				self.state.storage.mapping(&mut self.state.serialize).remove(&to_remove.0);
			}
		}
		if to_change.len() > 0 {
			change = true;
			for (branch_ix, branch, old_branch) in to_change {
				let mut index = branch.state.end.clone();
				while index < old_branch.end {
					remove_tag(&branch_ix, &index, &mut self.state.serialize);
					index += One::one();
				}
				self.state.register_change(&branch_ix, old_branch, Some(branch.state.end.clone()));
				self.state.storage.mapping(&mut self.state.serialize).insert(branch_ix, branch);
			}
		}

		let mut mapping = self.state.meta.mapping(&mut self.state.serialize);
		let tree_meta = mapping.get();
		if switch_index != tree_meta.composite_treshold || prune_index.is_some() {
			let mut tree_meta = tree_meta.clone();
			tree_meta.next_composite_treshold = Some(switch_index);
			tree_meta.pruning_treshold = prune_index;
			mapping.set(tree_meta);
			change = true;
		}
		change
	}
}

impl<H, I, BI, S> RegisteredConsumer<H, I, BI, S>
	where
		I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
		BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
		H: Clone + Ord + Codec,
		S: TreeManagementStorage,
{
	/// Register a consumer.
	///
	/// There is no check that a consumer is not registered twice.
	pub fn register_consumer(&mut self, consumer: Box<dyn super::ManagementConsumer<H, TreeManagement<H, I, BI, S>>>) {
		self.0.push(consumer);
	}

	/// Do migrate data from the registered consumer.
	/// Apply migrate to the tree management when finished.
	pub fn migrate(&self, mgmt: &mut TreeManagement<H, I, BI, S>) {
		// In this case (register consumer is design to run with sync backends), the management
		// lock is very likely to be ineffective.
		let mut migrate = mgmt.get_migrate();
		let need_migrate = match &migrate.1 {
			MultipleMigrate::Noops => false,
			_ => true,
		};
		if need_migrate {
			for consumer in self.0.iter() {
				consumer.migrate(&mut migrate);
			}
		}
		
		migrate.0.applied_migrate()
	}
}

impl<I, BI, S> Tree<I, BI, S>
	where
		I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
		BI: Ord + Default + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
		S: TreeManagementStorage,
{
	/// Return anchor index for this branch history:
	/// - same index as input if the branch was modifiable
	/// - new index in case of branch range creation
	pub fn add_state(
		&mut self,
		branch_index: I,
		number: BI,
	) -> Option<I> {
		let mut meta = self.meta.mapping(&mut self.serialize).get().clone();
		if number < meta.composite_treshold.1 {
			return None;
		}
		let mut create_new = false;
		if branch_index <= meta.composite_treshold.0 {
			// only allow terminal append
			let mut next = meta.composite_treshold.1.clone();
			next += BI::one();
			if number == next {
				if meta.composite_latest {
					meta.composite_latest = false;
				}
				create_new = true;
			} else {
				return None;
			}
		} else {
			let mut mapping = self.storage.mapping(&mut self.serialize);
			assert!(mapping.get(&branch_index).is_some(),
				"Inconsistent state on new block: {:?} {:?}, {:?}",
				branch_index,
				number,
				meta.composite_treshold,
			);
			let branch_state = mapping.entry(&branch_index);

			let mut can_fork = true;
			branch_state.and_modify(|branch_state| {
				if branch_state.can_append && branch_state.can_add(&number) {
					branch_state.add_state();
				} else {
					if !branch_state.can_fork(&number) {
						can_fork = false;
					} else {
						if branch_state.state.end == number {
							branch_state.is_latest = false;
						}
						create_new = true;
					}
				}
			});
			if !can_fork {
				return None;
			}
		}
		Some(if create_new {
			meta.last_index += I::one();
			let state = BranchState::new(number, branch_index);
			self.storage.mapping(&mut self.serialize).insert(meta.last_index.clone(), state);
			let result = meta.last_index.clone();

			self.meta.mapping(&mut self.serialize).set(meta);
			result
		} else {
			branch_index
		})
	}

	/// Access latest state for a branch.
	/// There is no check that the given branch is a terminal branch.
	#[cfg(test)]
	pub fn unchecked_latest_at(&mut self, branch_index : I) -> Option<Latest<(I, BI)>> {
		{
			let mut mapping = self.meta.mapping(&mut self.serialize);
			let meta = mapping.get();
			if meta.composite_latest {
				// composite
				if branch_index <= meta.composite_treshold.0 {
					return Some(Latest::unchecked_latest(meta.composite_treshold.clone()));
				} else {
					return None;
				}
			}
		}
		self.storage.mapping(&mut self.serialize).get(&branch_index).map(|branch| {
			let mut end = branch.state.end.clone();
			end -= BI::one();
			Latest::unchecked_latest((branch_index, end))
		})
	}
	
	/// Get latest state for a branch and index only if it is a terminal leaf of the tree.
	fn if_latest_at(&mut self, branch_index: I, seq_index: BI) -> Option<Latest<(I, BI)>> {
		{
			let mut mapping = self.meta.mapping(&mut self.serialize);
			let meta = mapping.get();
			if meta.composite_latest {
				// composite is head
				if branch_index <= meta.composite_treshold.0 && seq_index == meta.composite_treshold.1 {
					return Some(Latest::unchecked_latest(meta.composite_treshold.clone()));
				} else {
					return None;
				}
			}
		}
		self.storage.mapping(&mut self.serialize).get(&branch_index).and_then(|branch| {
			if !branch.is_latest {
				None
			} else {
				let mut end = branch.state.end.clone();
				end -= BI::one();
				if seq_index == end {
					Some(Latest::unchecked_latest((branch_index, end)))
				} else {
					None
				}
			}
		})
	}
	
	/// Access read query.
	fn query_plan_at(&mut self, (branch_index, mut index) : (I, BI)) -> ForkPlan<I, BI> {
		// make index exclusive
		index += BI::one();
		self.query_plan_inner(branch_index, Some(index))
	}

	///Access read query for a given branch (latest index of the branch).
	#[cfg(test)]
	pub(crate) fn query_plan(&mut self, branch_index: I) -> ForkPlan<I, BI> {
		self.query_plan_inner(branch_index, None)
	}

	fn query_plan_inner(&mut self, mut branch_index: I, mut parent_fork_branch_index: Option<BI>) -> ForkPlan<I, BI> {
		let composite_treshold = self.meta.mapping(&mut self.serialize).get().composite_treshold.clone();
		let mut history = Vec::new();
		while branch_index >= composite_treshold.0 {
			if let Some(branch) = self.storage.mapping(&mut self.serialize).get(&branch_index) {
				let branch_ref = if let Some(end) = parent_fork_branch_index.take() {
					branch.query_plan_to(end)
				} else {
					branch.query_plan()
				};
				parent_fork_branch_index = Some(branch_ref.start.clone());
				if branch_ref.end > branch_ref.start {
					// vecdeque would be better suited
					history.insert(0, BranchPlan {
						state: branch_ref,
						index: branch_index.clone(),
					});
				}
				branch_index = branch.parent_branch_index.clone();
			} else {
				break;
			}
		}
		ForkPlan {
			history,
			composite_treshold: composite_treshold,
		}
	}

	/// Access to internal branch state.
	#[cfg(test)]
	pub(crate) fn branch_state(&mut self, branch_index: &I) -> Option<BranchState<I, BI>> {
		self.storage.mapping(&mut self.serialize).get(branch_index).cloned()
	}

	/// Mutable access to internal branch state.
	#[cfg(test)]
	pub(crate) fn branch_state_mut<R, F: FnOnce(&mut BranchState<I, BI>) -> R>(&mut self, branch_index: &I, f: F) -> Option<R> {
		let mut result: Option<R> = None;
		self.storage.mapping(&mut self.serialize)
			.entry(branch_index)
			.and_modify(|s: &mut BranchState<I, BI>| {
				result = Some(f(s));
			});
		result
	}

	/// Register a change state in journal.
	fn register_change(&mut self,
		branch_index: &I,
		branch_range: BranchRange<BI>,
		new_node_index: Option<BI>, // if none this is a delete
	) {
		if S::JOURNAL_CHANGES {
			let mut journal_delete = self.journal_delete.mapping(&mut self.serialize);
			if let Some(new_node_index) = new_node_index {
				if let Some((to_insert, old_range)) = match journal_delete.get(branch_index) {
					Some((Some(old), old_range)) => if &new_node_index < old {
						// can use old range because the range gets read only on first
						// change.
						Some((new_node_index, old_range.clone()))
					} else {
						None
					},
					Some((None, _)) => None,
					None => Some((new_node_index, branch_range)),
				} {
					journal_delete.insert(branch_index.clone(), (Some(to_insert), old_range));
				}
			} else {
				journal_delete.insert(branch_index.clone(), (None, branch_range));
			}
		}
	}

	fn clear_journal_delete(&mut self) {
		let mut journal_delete = self.journal_delete.mapping(&mut self.serialize);
		journal_delete.clear()
	}

	fn clear_composite(&mut self) {
		let mut to_remove = Vec::new();
		if let Some(composite_treshold) = self.meta.get().next_composite_treshold.clone() {
			for (ix, branch) in self.storage.iter(&mut self.serialize) {
				if branch.state.start < composite_treshold.1 {
					to_remove.push(ix.clone());
				}
			}
		}

		let mut storage = self.storage.mapping(&mut self.serialize);
		for i in to_remove {
			storage.remove(&i);
		}
	}
}

/// Query plan needed for operation for a given
/// fork.
/// This is a subset of the full branch set definition.
///
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to the full state
/// a branch index corresponding to the leaf for the fork.
/// Here we use an in memory copy of the path because it seems
/// to fit query at a given state with multiple operations
/// (block processing), that way we iterate on a vec rather than
/// hoping over linked branches.
/// TODO small vec that ??
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForkPlan<I, BI> {
	history: Vec<BranchPlan<I, BI>>,
	/// All indexes before this treshold are valid.
	pub composite_treshold: (I, BI),
}

impl<I, BI> StateIndex<(I, BI)> for ForkPlan<I, BI>
	where
		I: Clone,
		BI: Clone + SubAssign<BI> + One,
{
	fn index(&self) -> (I, BI) {
		// Extract latest state index use by the fork plan.
		// In other words latest state index is use to obtain this
		// plan.
		self.latest()
	}

	fn index_ref(&self) -> Option<&(I, BI)> {
		None
	}
}

// Note that this is fairly incorrect (we should bound on I : StateIndex),
// but very convenient.
// Otherwhise, could put SF into a wrapper type.
impl<I: Clone, BI: Clone> StateIndex<(I, BI)> for (I, BI) {
	fn index(&self) -> (I, BI) {
		self.clone()
	}

	fn index_ref(&self) -> Option<&(I, BI)> {
		Some(self)
	}
}

impl<I, BI> ForkPlan<I, BI>
	where
		I: Clone,
		BI: Clone + SubAssign<BI> + One,
{
	fn latest(&self) -> (I, BI) {
		if let Some(branch_plan) = self.history.last() {
			let mut index = branch_plan.state.end.clone();
			index -= BI::one();
			(branch_plan.index.clone(), index)
		} else {
			self.composite_treshold.clone()
		}
	}
}

impl<I, BI: Clone + SubAssign<BI> + One + Default + Ord> ForkPlan<I, BI> {
	/// Calculate forkplan that does not include current state,
	/// very usefull to produce diff of value at a given state
	/// (we make the diff against the previous, not the current).
	pub fn previous_forkplan(mut self) -> Option<ForkPlan<I, BI>> {
		if self.history.len() > 0 {
			debug_assert!(self.history[0].state.start > self.composite_treshold.1);
			if let Some(branch) = self.history.last_mut() {
				branch.state.end -= One::one();
				if branch.state.end != branch.state.start {
					return Some(self);
				}
			}
			self.history.pop();
		} else if self.composite_treshold.1 == Default::default() {
			return None;
		} else {
			self.composite_treshold.1 -= One::one();
		}
		Some(self)
	}
}

impl<I: Default, BI: Default> Default for ForkPlan<I, BI> {
	fn default() -> Self {
		ForkPlan {
			history: Vec::new(),
			composite_treshold: Default::default(),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Query plan element for a single branch.
pub struct BranchPlan<I, BI> {
	index: I,
	 state: BranchRange<BI>,
}

impl<I, BI> ForkPlan<I, BI>
	where
		I: Default + Ord + Clone,
		BI: SubAssign<BI> + Ord + Clone + One,
{
	/// Iterator over the branch states in query order
	/// (more recent first).
	pub fn iter(&self) -> ForkPlanIter<I, BI> {
		ForkPlanIter(self, self.history.len())
	}
}

/// Iterator, contains index of last inner struct.
pub struct ForkPlanIter<'a, I, BI>(&'a ForkPlan<I, BI>, usize);

impl<'a, I: Clone, BI> Iterator for ForkPlanIter<'a, I, BI> {
	type Item = (&'a BranchRange<BI>, I);

	fn next(&mut self) -> Option<Self::Item> {
		if self.1 > 0 {
			self.1 -= 1;
			Some((
				&(self.0).history[self.1].state,
				(self.0).history[self.1].index.clone(),
			))
		} else {
			None
		}
	}
}

impl<I: Ord> BranchRange<I> {
	#[cfg(test)]
	fn exists(&self, i: &I) -> bool {
		i >= &self.start && i < &self.end
	}
}

impl<I: Default, BI: Default + AddAssign<u32>> Default for BranchState<I, BI> {
	// initialize with one element
	fn default() -> Self {
		let mut end = BI::default();
		end += 1;
		BranchState {
			state: BranchRange {
				start: Default::default(),
				end,
			},
			can_append: true,
			is_latest: true,
			parent_branch_index: Default::default(),
		}
	}
}

impl<I, BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + One> BranchState<I, BI> {

	fn query_plan(&self) -> BranchRange<BI> {
		self.state.clone()
	}

	fn query_plan_to(&self, end: BI) -> BranchRange<BI> {
		debug_assert!(self.state.end >= end);
		BranchRange {
			start: self.state.start.clone(),
			end,
		}
	}

	fn new(offset: BI, parent_branch_index: I) -> Self {
		let mut end = offset.clone();
		end += BI::one();
		BranchState {
			state: BranchRange {
				start: offset,
				end,
			},
			can_append: true,
			is_latest: true,
			parent_branch_index,
		}
	}

	/// Return true if you can add this index.
	fn can_add(&self, index: &BI) -> bool {
		index == &self.state.end
	}

 	fn can_fork(&self, index: &BI) -> bool {
		index <= &self.state.end && index > &self.state.start
	}

	fn add_state(&mut self) -> bool {
		if self.can_append {
			self.state.end += BI::one();
			true
		} else {
			false
		}
	}

	/// Return true if resulting branch is empty.
	#[cfg(test)]
	pub(crate) fn drop_state(&mut self) -> bool {
		if self.state.end > self.state.start {
			self.state.end -= BI::one();
			self.can_append = false;
			if self.state.end == self.state.start {
				true
			} else {
				false
			}
		} else {
			true
		}
	}
}

#[derive(Debug, Clone, Encode, Decode)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct BranchGC<I, BI> {
	/// Index of the modified branch.
	pub branch_index: I,
	/// A new start - end limit for the branch or a removed
	/// branch.
	pub new_range: Option<LinearGC<BI>>,
}


/// Same as `DeltaTreeStateGc`, but also
/// indicates the changes journaling can be clean.
/// TODO requires a function returning all H indices.
pub struct TreeMigrateGC<I, BI> {
	pub gc: DeltaTreeStateGc<I, BI>,
	pub changed_composite_treshold: bool,
}

#[derive(Debug, Clone)]
/// A migration that swap some branch indices.
/// Note that we do not touch indices into branch.
pub struct TreeRewrite<I, BI> {
	/// Original branch index (and optionally a treshold) mapped to new branch index or deleted.
	pub rewrite: Vec<((I, Option<BI>), Option<I>)>,
	/// Possible change in composite treshold.
	pub composite_treshold: (I, BI),
	pub changed_composite_treshold: bool,
	/// All data before this can get pruned.
	pub pruning_treshold: Option<BI>,
}

#[derive(Debug, Clone)]
pub enum MultipleMigrate<I, BI> {
	JournalGc(DeltaTreeStateGc<I, BI>),
	Noops,
}

impl<
	H: Ord + Clone + Codec,
	I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
	BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
	S: TreeManagementStorage,
> TreeManagement<H, I, BI, S> {
	fn get_inner_gc(&self) -> Option<MultipleGc<I, BI>> {
		let tree_meta = self.state.meta.get();
		let composite_treshold = tree_meta.next_composite_treshold.clone()
			.unwrap_or(tree_meta.composite_treshold.clone());
		let pruning_treshold = tree_meta.pruning_treshold.clone();
		let gc = if Self::JOURNAL_CHANGES {
			let mut storage = BTreeMap::new();
			for (k, v) in self.state.journal_delete.iter(&self.state.serialize) {
				storage.insert(k, v);
			}

			if pruning_treshold.is_none() && storage.is_empty() {
				return None;
			}

			let gc = DeltaTreeStateGc {
				storage,
				composite_treshold,
				pruning_treshold,
			};

			MultipleGc::Journaled(gc)
		} else {
			unimplemented!("TODO noops");
		};

		Some(gc)
	}
}
	
impl<H, I, BI, S> Management<H> for TreeManagement<H, I, BI, S>
	where
		H: Ord + Clone + Codec,
		I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
		BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
		S: TreeManagementStorage,
{
	type Index = (I, BI);
	type S = ForkPlan<I, BI>;
	/// Garbage collect over current
	/// state or registered changes.
	/// Choice is related to `TreeManagementStorage::JOURNAL_CHANGES`.
	type GC = MultipleGc<I, BI>;

	fn get_internal_index(&mut self, tag: &H) -> Option<Self::Index> {
		self.ext_states.mapping(self.state.ser()).get(tag).cloned()
	}

	fn get_db_state(&mut self, tag: &H) -> Option<Self::S> {
		self.ext_states.mapping(self.state.ser()).get(tag).cloned().map(|i| self.state.query_plan_at(i))
	}

	fn reverse_lookup(&mut self, index: &Self::Index) -> Option<H> {
		// TODO Note, from a forkplan we need to use 'latest' to get same
		// behavior as previous implementation.
		self.ext_states.mapping(self.state.ser()).iter()
			.find(|(_k, v)| v == index)
			.map(|(k, _v)| k.clone())
	}

	fn get_gc(&self) -> Option<crate::Ref<Self::GC>> {
		self.get_inner_gc().map(|gc| crate::Ref::Owned(gc))
	}
}

impl<
	H: Clone + Ord + Codec,
	I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
	BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
	S: TreeManagementStorage,
> ManagementMut<H> for TreeManagement<H, I, BI, S> {
	// TODO we could also attach some gc infos to allow
	// lazy cleanup on set and on get_mut.
	type SE = Latest<(I, BI)>;

	type Migrate = MultipleMigrate<I, BI>;

	fn get_db_state_mut(&mut self, tag: &H) -> Option<Self::SE> {
		self.ext_states.mapping(self.state.ser()).get(tag).cloned().and_then(|(i, bi)| {
			// enforce only latest
			self.state.if_latest_at(i, bi)
		})
	}
	
	fn latest_state(&mut self) -> Self::SE {
		let latest = self.last_added.mapping(self.state.ser()).get().clone();
		Latest::unchecked_latest(latest.0)
	}

	fn latest_external_state(&mut self) -> Option<H> {
		let latest = self.last_added.mapping(self.state.ser()).get().clone();
		latest.1
	}

	fn force_latest_external_state(&mut self, state: H) {
		let mut latest = self.last_added.mapping(self.state.ser()).get().clone();
		latest.1 = Some(state);
		self.last_added.mapping(self.state.ser()).set(latest);
	}

	fn get_migrate(&mut self) -> Migrate<H, Self> {
		let migrate = if S::JOURNAL_CHANGES {
			// initial migrate strategie is gc.
			if let Some(MultipleGc::Journaled(gc)) = self.get_inner_gc() {
				MultipleMigrate::JournalGc(gc)
			} else {
				MultipleMigrate::Noops
			}
		} else {
			unimplemented!();
		};

		Migrate(self, migrate, sp_std::marker::PhantomData)
	}

	fn applied_migrate(&mut self) {
		if S::JOURNAL_CHANGES {
			self.state.clear_journal_delete();
			self.state.clear_composite();
			let mut meta_change = false;
			let mut mapping = self.state.meta.mapping(&mut self.state.serialize);
			let mut tree_meta = mapping.get().clone();
			if let Some(treshold) = tree_meta.next_composite_treshold.take() {
				tree_meta.composite_treshold = treshold;
				meta_change = true;
			}
			if tree_meta.pruning_treshold.take().is_some() {
				meta_change = true;
			}
			if meta_change {
				mapping.set(tree_meta);
			}
		}
	}
}

impl<
	H: Clone + Ord + Codec,
	I: Clone + Default + SubAssign<I> + AddAssign<I> + Ord + Debug + Codec + One,
	BI: Ord + SubAssign<BI> + AddAssign<BI> + Clone + Default + Debug + Codec + One,
	S: TreeManagementStorage,
> ForkableManagement<H> for TreeManagement<H, I, BI, S> {
	const JOURNAL_CHANGES: bool = S::JOURNAL_CHANGES;

	type SF = (I, BI);

	fn from_index(index: (I, BI)) -> Self::SF {
		index
	}

	fn init_state_fork(&mut self) -> Self::SF {
		let se = Latest::unchecked_latest(self.state.meta.get().composite_treshold.clone());
		Self::from_index(se.index())
	}

	fn get_db_state_for_fork(&mut self, state: &H) -> Option<Self::SF> {
		self.ext_states.mapping(self.state.ser()).get(state).cloned()
	}

	// note that se must be valid.
	fn append_external_state(&mut self, state: H, at: &Self::SF) -> Option<Self::SE> {
		let (branch_index, index) = at;
		let mut index = index.clone();
		index += BI::one();
		if let Some(branch_index) = self.state.add_state(branch_index.clone(), index.clone()) {
			let last_added = (branch_index.clone(), index);
			self.last_added.mapping(self.state.ser())
				.set((last_added.clone(), Some(state.clone())));
			self.ext_states.mapping(self.state.ser()).insert(state, last_added.clone());
			Some(Latest::unchecked_latest(last_added))
		} else {
			None
		}
	}
}

#[cfg(test)]
pub(crate) mod test {
	use super::*;

	/// Test state used by management test, no mappings.
	pub(crate) type TestState = Tree<u32, u32, ()>;
	/// Test state used by management test, with test mappings.
	pub(crate) type TestStateMapping = Tree<u32, u32, crate::test::MappingTests>;

	pub(crate) fn test_states() -> TestState {
		test_states_inner()
	}

	pub(crate) fn test_states_st() -> TestStateMapping {
		test_states_inner()
	}
	
	// TODO switch to management function?
	pub(crate) fn test_states_inner<T: TreeManagementStorage>() -> Tree<u32, u32, T>
		where T::Storage: Default,
	{
		let mut states = Tree::default();
		assert_eq!(states.add_state(0, 1), Some(1));
		// root branching.
		assert_eq!(states.add_state(0, 1), Some(2));
		assert_eq!(Some(true), states.branch_state_mut(&1, |ls| ls.add_state()));
		assert_eq!(Some(true), states.branch_state_mut(&1, |ls| ls.add_state()));
		assert_eq!(states.add_state(1, 3), Some(3));
		assert_eq!(states.add_state(1, 3), Some(4));
		assert_eq!(states.add_state(1, 2), Some(5));
		assert_eq!(states.add_state(2, 2), Some(2));
		states.branch_state_mut(&1, |ls| ls.drop_state());
		// cannot create when dropped happen on branch
		assert_eq!(Some(false), states.branch_state_mut(&1, |ls| ls.add_state()));

		assert!(states.branch_state(&1).unwrap().state.exists(&1));
		assert!(states.branch_state(&1).unwrap().state.exists(&2));
		assert!(!states.branch_state(&1).unwrap().state.exists(&3));
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _ _
		states
	}

	#[test]
	fn test_serialize() {
		let states = test_states_st();
		let storage = states.serialize.clone();
		let mut states = TestStateMapping::from_ser(storage);
		// just replaying the three last test of test_states_inner
		assert!(states.branch_state(&1).unwrap().state.exists(&1));
		assert!(states.branch_state(&1).unwrap().state.exists(&2));
		assert!(!states.branch_state(&1).unwrap().state.exists(&3));
	}

	#[test]
	fn test_query_plans() {
		let mut states = test_states();
		let ref_3 = vec![
			BranchPlan {
				index: 1,
				state: BranchRange { start: 1, end: 3 },
			},
			BranchPlan {
				index: 3,
				state: BranchRange { start: 3, end: 4 },
			},
		];
		assert_eq!(states.query_plan(3).history, ref_3);

		let mut states = states;

		assert_eq!(states.add_state(1, 2), Some(6));
		let ref_6 = vec![
			BranchPlan {
				index: 1,
				state: BranchRange { start: 1, end: 2 },
			},
			BranchPlan {
				index: 6,
				state: BranchRange { start: 2, end: 3 },
			},
		];
		assert_eq!(states.query_plan(6).history, ref_6);

		let mut meta = states.meta.mapping(&mut states.serialize).get().clone();
		meta.composite_treshold = (2, 1);
		states.meta.mapping(&mut states.serialize).set(meta);

		let mut ref_6 = ref_6;
		ref_6.remove(0);
		assert_eq!(states.query_plan(6).history, ref_6);
	}
}
