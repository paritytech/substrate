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

//! Filters associated to externalities access.
//! These are used to ensure declarative workers access are correct.
//! It is plugged in the overlay by commodity, but could be at a higher level.

use sp_std::{vec, vec::Vec, fmt::Debug};
use sp_std::collections::btree_map::BTreeMap;
use sp_std::collections::btree_set::BTreeSet;
use super::radix_trees::FilterTree;
use sp_externalities::{TaskId, WorkerResult,
	AccessDeclaration, WorkerDeclaration, DeclarationFailureHandling};
use super::StorageKey;
use sp_core::storage::ChildInfo;
use failure::{FailureHandlers, DeclFailureHandling};

/// Worker declaration assertion failure.
pub const BROKEN_DECLARATION_ACCESS: &'static str = "Key access impossible due to worker access declaration";

/// Main filter state.
#[derive(Debug, Clone)]
pub(super) struct Filters {
	failure_handlers: FailureHandlers,
	allow_read_active: bool,
	allow_write_active: bool,
	filters_allow: FilterTrees<bool>,
	filters_forbid: FilterTrees<FilterOrigin>,
	/// keeping history to remove constraint on join or dismiss.
	/// It contains constraint for the parent (child do not need
	/// to remove contraint), indexed by its relative child id.
	changes: BTreeMap<TaskId, Vec<(Option<StorageKey>, WorkerDeclaration)>>,
}

/// A tree of filter rules.
#[derive(Debug, Clone, Default)]
struct FilterTrees<F: Debug + Clone + Default> {
	top: FilterTree<F>,
	children: BTreeMap<StorageKey, FilterTree<F>>,
}

impl<F: Debug + Clone + Default> FilterTrees<F> {
	fn filter(&self, child_info: Option<&ChildInfo>) -> Option<&FilterTree<F>> {
		if let Some(child_info) = child_info {
			self.children.get(child_info.storage_key())
		} else {
			Some(&self.top)
		}
	}
}

impl Default for Filters {
	fn default() -> Self {
		Filters {
			failure_handlers: FailureHandlers {
				parent_failure_handler: DeclFailureHandling::default(),
				children_failure_handler: BTreeMap::new(),
			},
			allow_read_active: Default::default(),
			allow_write_active: Default::default(),
			filters_allow: Default::default(),
			filters_forbid: Default::default(),
			changes: BTreeMap::new(),
		}
	}
}

impl Filters {
	pub(super) fn set_failure_handler(
		&mut self,
		from_child: Option<TaskId>,
		failure: DeclarationFailureHandling,
	) {
		self.failure_handlers.set_failure_handler(from_child, failure);
	}

	fn remove_filter(
		tree: &mut FilterTrees<FilterOrigin>,
		filter: AccessDeclaration,
		from_child: TaskId,
		write: bool,
	) {
		Self::remove_filter_internal(&mut tree.top, filter, from_child, write);
	}

	fn remove_filter_internal(
		tree: &mut FilterTree<FilterOrigin>,
		filter: AccessDeclaration,
		from_child: TaskId,
		write: bool,
	) {
		for prefix in filter.prefixes_lock {
			if let Some(filter) = tree.get_mut(prefix.as_slice()) {
				if write {
					filter.write_prefix.remove(from_child);
				} else {
					filter.read_only_prefix.remove(from_child);
				};
				if filter.is_empty() {
					tree.remove(prefix.as_slice());
				}
			}
		}
		for key in filter.keys_lock {
			if let Some(filter) = tree.get_mut(key.as_slice()) {
				if write {
					filter.write_key.remove(from_child);
				} else {
					filter.read_only_key.remove(from_child);
				};
				if filter.is_empty() {
					tree.remove(key.as_slice());
				}
			}
		}
	}

	fn set_filter(
		tree: &mut FilterTrees<FilterOrigin>,
		filter: AccessDeclaration,
		from_child: TaskId,
		write: bool,
	) {
		Self::set_filter_internal(&mut tree.top, filter, from_child, write);
	}

	fn set_filter_internal(
		tree: &mut FilterTree<FilterOrigin>,
		filter: AccessDeclaration,
		from_child: TaskId,
		write: bool,
	) {
		for prefix in filter.prefixes_lock {
			if let Some(filter) = tree.get_mut(prefix.as_slice()) {
				if write {
					filter.write_prefix.set(from_child);
				} else {
					filter.read_only_prefix.set(from_child);
				};
			} else {
				// new entry
				let mut filter = Filter::<FilterOrigin>::default();
				if write {
					filter.write_prefix.set(from_child);
				} else {
					filter.read_only_prefix.set(from_child);
				};
				tree.insert(prefix.as_slice(), filter);
			}
		}
		for key in filter.keys_lock {
			if let Some(filter) = tree.get_mut(key.as_slice()) {
				if write {
					filter.write_key.set(from_child);
				} else {
					filter.read_only_key.set(from_child);
				}
			} else {
				// new entry
				let mut filter = Filter::<FilterOrigin>::default();
				if write {
					filter.write_key.set(from_child);
				} else {
					filter.read_only_key.set(from_child);
				};
				tree.insert(key.as_slice(), filter);
			}
		}
	}

	fn set_filter_allow(
		tree: &mut FilterTrees<bool>,
		filter: AccessDeclaration,
		write: bool,
	) {
		Self::set_filter_allow_internal(&mut tree.top, filter, write);
	}

	fn set_filter_allow_internal(
		tree: &mut FilterTree<bool>,
		filter: AccessDeclaration,
		write: bool,
	) {
		for prefix in filter.prefixes_lock {
			if let Some(filter) = tree.get_mut(prefix.as_slice()) {
				if write {
					filter.write_prefix = true;
				} else {
					filter.read_only_prefix = true;
				}
			} else {
				// new entry
				let mut filter = Filter::<bool>::default();
				if write {
					filter.write_prefix = true;
				} else {
					filter.read_only_prefix = true;
				};
				tree.insert(prefix.as_slice(), filter);
			}
		}
		for key in filter.keys_lock {
			if let Some(filter) = tree.get_mut(key.as_slice()) {
				if write {
					filter.write_key = true;
				} else {
					filter.read_only_key = true;
				}
			} else {
				// new entry
				let mut filter = Filter::<bool>::default();
				if write {
					filter.write_key = true;
				} else {
					filter.read_only_key = true;
				}
				tree.insert(key.as_slice(), filter);
			}
		}
	}

	pub(super) fn allow_writes(
		&mut self,
		filter: AccessDeclaration,
	) {
		self.allow_write_active = true;
		Self::set_filter_allow(&mut self.filters_allow, filter, true);
	}

	pub(super) fn allow_reads(
		&mut self,
		filter: AccessDeclaration,
	) {
		self.allow_read_active = true;
		Self::set_filter_allow(&mut self.filters_allow, filter, false);
	}

	pub(super) fn add_change(
		&mut self,
		decl: WorkerDeclaration,
		from_child: TaskId,
	) {
		// TODO is there something else than None variant bellow?
		self.changes.insert(from_child, vec![(None, decl)]);
	}

	pub(super) fn forbid_writes(
		&mut self,
		filter: AccessDeclaration,
		from_child: TaskId,
	) {
		Self::set_filter(&mut self.filters_forbid, filter, from_child, true);
	}

	fn remove_forbid_writes(
		&mut self,
		filter: AccessDeclaration,
		from_child: TaskId,
	) {
		Self::remove_filter(&mut self.filters_forbid, filter, from_child, true);
	}

	pub(super) fn forbid_reads(
		&mut self,
		filter: AccessDeclaration,
		from_child: TaskId,
	) {
		Self::set_filter(&mut self.filters_forbid, filter, from_child, false);
	}

	// Declaring a child read access, we ensure access is allowed in the first place.
	pub(super) fn guard_child_filter_read(&mut self, filter: &AccessDeclaration) {
		for top_prefix in filter.prefixes_lock.iter() {
			self.guard_read_prefix(None, top_prefix);
		}
		for top_key in filter.keys_lock.iter() {
			self.guard_read(None, top_key);
		}
	}

	// Declaring a child write access, we ensure access is allowed in the first place.
	pub(super) fn guard_child_filter_write(&mut self, filter: &AccessDeclaration) {
		for top_prefix in filter.prefixes_lock.iter() {
			self.guard_write_prefix(None, top_prefix);
		}
		for top_key in filter.keys_lock.iter() {
			self.guard_write(None, top_key);
		}
	}

	pub(super) fn on_worker_result(&mut self, result: &WorkerResult) -> bool {
		let did_fail = self.failure_handlers.did_fail();
		match result {
			WorkerResult::CallAt(_result, _delta, marker) => {
				self.remove_worker(*marker);
			},
			WorkerResult::Optimistic(_result, _delta, marker, ..) => {
				// This is actually a noops since optimistic don't
				// use filter.
				self.remove_worker(*marker);
			},
			// When using filter there is no directly valid case.
			WorkerResult::Valid(..) => (),
			// When using filter there is no invalid case.
			WorkerResult::Invalid => (),
			// will panic on resolve so no need to clean filter
			WorkerResult::RuntimePanic
			| WorkerResult::HardPanic => (),
		};
		!did_fail
	}

	// TODO case where we allow all (forbid all on the other side) really need to be tested.
	pub(super) fn guard_read_all(&self) {
		Self::guard_read_all_internal_forbid(&self.failure_handlers, &self.filters_forbid.top);
		for (_storage_key, child) in self.filters_forbid.children.iter() {
			Self::guard_read_all_internal_forbid(&self.failure_handlers, child);
		}
		// Note that we consider there is no full read access (with child trie it is difficult),
		// generally one shall never use full filter: it should be a stand alone mode.
		if self.allow_read_active {
			self.failure_handlers.invalid_allowed_access();
		}
	}

	fn guard_read_all_internal_forbid(
		failure_handlers: &FailureHandlers,
		filters_forbid: &FilterTree<FilterOrigin>,
	) {
		// check not forbid write or forbid read filter.
		// Note that this is very suboptimal, but only is for storage_root call
		// (which is not supported by workers)
		for (_key, filter) in filters_forbid.iter().value_iter() {
			if filter.read_only_prefix.is_defined() {
				failure_handlers.invalid_accesses(&filter.read_only_prefix);
			}
			if filter.read_only_key.is_defined() {
				failure_handlers.invalid_accesses(&filter.read_only_key)
			}
		}
	}
/*
	fn guard_write_inner(filter: &Filter, blocked: &mut bool, key: &[u8], len: usize) {
		match filter.write_prefix {
			FilterState::Forbid => {
				*blocked = true;
			},
			FilterState::Allow => {
				*blocked = false;
			},
			FilterState::None => (),
		}
		match filter.write_key {
			FilterState::Forbid => {
				if len == key.len() {
					*blocked = true;
				}
			},
			FilterState::Allow => {
				if len == key.len() {
					*blocked = false;
				}
			},
			FilterState::None => (),
		}
	}
*/
	/// Guard invalid access for reading a key.
	pub(super) fn guard_read(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		let blocked = Self::key_read_forbid(&self.filters_forbid, child_info, key);
		for origin in blocked {
			self.failure_handlers.invalid_accesses(origin);
		}
		if self.allow_write_active || self.allow_read_active {
			if !Self::guard_read_allow(&self.filters_allow, child_info, key) {
				self.failure_handlers.invalid_allowed_access();
			}
		}
	}

	/// Guard invalid access for writing a key.
	pub(super) fn guard_write(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		let blocked = Self::key_write_forbid(&self.filters_forbid, child_info, key);
		for origin in blocked {
			self.failure_handlers.invalid_accesses(origin);
		}
		if self.allow_write_active {
			if !Self::guard_write_allow(&self.filters_allow, child_info, key) {
				self.failure_handlers.invalid_allowed_access();
			}
		}
	}

	fn key_write_forbid<'a>(
		filters: &'a FilterTrees<FilterOrigin>,
		child_info: Option<&ChildInfo>,
		key: &'a [u8],
	) -> Vec<&'a FilterOrigin> {
		let mut blocked = Vec::new();
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return blocked;
		};
		let len = key.len();
		for (key, value) in filters.seek_iter(key).value_iter() {
			// forbid read implies forbid write.
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if value.write_prefix.is_defined() {
				blocked.push(&value.write_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
				if value.write_key.is_defined() {
					blocked.push(&value.write_key);
				}
			}
		}
		blocked
	}

	fn key_write_forbid_prefix<'a>(
		filters: &'a FilterTrees<FilterOrigin>,
		child_info: Option<&ChildInfo>,
		key: &'a [u8],
	) -> Vec<&'a FilterOrigin> {
		let mut blocked = Vec::new();
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return blocked;
		};
		let len = key.len();
		let mut iter = filters.seek_iter(key).value_iter();
		while let Some((key, value)) = iter.next() {
			// forbid read implies forbid write.
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if value.write_prefix.is_defined() {
				blocked.push(&value.write_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
				if value.write_key.is_defined() {
					blocked.push(&value.write_key);
				}
			}
		}
		for (key, value) in iter.node_iter().iter_prefix().value_iter() {
			// forbid read implies forbid write. TODO push these snippet in a value
			// fn
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if value.write_prefix.is_defined() {
				blocked.push(&value.write_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
				if value.write_key.is_defined() {
					blocked.push(&value.write_key);
				}
			}
		}
		blocked
	}

	fn key_read_forbid_prefix<'a>(
		filters: &'a FilterTrees<FilterOrigin>,
		child_info: Option<&ChildInfo>,
		key: &'a [u8],
	) -> Vec<&'a FilterOrigin> {
		let mut blocked = Vec::new();
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return blocked;
		};
		let len = key.len();
		let mut iter = filters.seek_iter(key).value_iter();
		while let Some((key, value)) = iter.next() {
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
			}
		}
		for (key, value) in iter.node_iter().iter_prefix().value_iter() {
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
			}
		}
		blocked
	}

	// TODO factor with key_write_forbid
	fn key_read_forbid<'a>(
		filters: &'a FilterTrees<FilterOrigin>,
		child_info: Option<&ChildInfo>,
		key: &'a [u8],
	) -> Vec<&'a FilterOrigin> {
		let mut blocked = Vec::new();
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return blocked;
		};
		let len = key.len();
		for (key, value) in filters.seek_iter(key).value_iter() {
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
			}
		}
		blocked
	}

	fn key_read_forbid_interval<'a>(
		filters: &'a FilterTrees<FilterOrigin>,
		child_info: Option<&ChildInfo>,
		key: &'a [u8],
		key_end: Option<&'a [u8]>,
	) -> Vec<&'a FilterOrigin> {
		let mut blocked = Vec::new();
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return blocked;
		};
		let len = key.len();
		let mut iter = filters.seek_iter(key).value_iter();
		while let Some((key, value)) = iter.next() {
			if value.read_only_prefix.is_defined() {
				blocked.push(&value.read_only_prefix);
			}
			if len == key.len() {
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
			}
		}
		for (key, value) in iter.node_iter().iter().value_iter() {
			if key_end.map(|end| key.as_slice() <= end).unwrap_or(true) {
				if value.read_only_prefix.is_defined() {
					blocked.push(&value.read_only_prefix);
				}
				if value.read_only_key.is_defined() {
					blocked.push(&value.read_only_key);
				}
			} else {
				break;
			}
		}
	
		blocked
	}

	/// Return false if blocked.
	fn guard_read_allow(filters: &FilterTrees<bool>, child_info: Option<&ChildInfo>, key: &[u8]) -> bool {
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return true;
		};
		let len = key.len();
		for (key, value) in filters.seek_iter(key).value_iter() {
			// forbid write implies forbid read.
			if value.write_prefix {
				return true;
			}
			if value.read_only_prefix {
				return true;
			}
			if len == key.len() {
				if value.write_key {
					return true;
				}
				if value.read_only_key {
					return true;
				}
			}
		}
		false
	}

	/// allow iteration is only allowing interval definition.
	/// TODO simple test case with limit condition
	fn guard_read_allow_interval(
		filters: &FilterTrees<bool>,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) -> bool {
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return true;
		};
		let mut iter = filters.seek_iter(key).value_iter();
		let mut start_interval = None;
		while let Some((key, value)) = iter.next() {
			// forbid write implies forbid read.
			if value.write_prefix {
				start_interval = Some(key);
				break;
			}
			if value.read_only_prefix {
				start_interval = Some(key);
				break;
			}
		}
		let mut last_prefix = if let Some(key) = start_interval {
			if key_end.map(|end| end.starts_with(key)).unwrap_or(false) {
				return true;
			}
			key.to_vec()
		} else {
			return false;
		};
		for (key, value) in iter.node_iter().iter().value_iter() {
			if key_end.map(|end| key.as_slice() <= end).unwrap_or(true) {
				if !key.starts_with(last_prefix.as_slice()) {
					if value.write_prefix || value.read_only_prefix {
						last_prefix = key;
					} else {
						return false;
					}
				}
			} else {
				break;
			}
		}
		true
	}

	//TODO factor with guard_read_alow
	/// Return false if blocked.
	fn guard_write_allow(filters: &FilterTrees<bool>, child_info: Option<&ChildInfo>, key: &[u8]) -> bool {
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return true;
		};
		let len = key.len();
		for (key, value) in filters.seek_iter(key).value_iter() {
			// forbid write implies forbid read.
			if value.write_prefix {
				return true;
			}
			if len == key.len() {
				if value.write_key {
					return true;
				}
			}
		}
		false
	}

	fn guard_read_allow_prefix(filters: &FilterTrees<bool>, child_info: Option<&ChildInfo>, key: &[u8]) -> bool {
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return true;
		};
		for (_key, value) in filters.seek_iter(key).value_iter() {
			// allow write implies allow read.
			if value.write_prefix || value.read_only_prefix {
				return true;
			}
		}
		false
	}

	fn guard_write_allow_prefix(filters: &FilterTrees<bool>, child_info: Option<&ChildInfo>, key: &[u8]) -> bool {
		let filters = if let Some(filter) = filters.filter(child_info) {
			filter
		} else {
			return true;
		};
		for (_key, value) in filters.seek_iter(key).value_iter() {
			if value.write_prefix {
				return true;
			}
		}
		false
	}

	fn guard_read_prefix(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		let blocked = Self::key_read_forbid_prefix(&self.filters_forbid, child_info, key);
		for origin in blocked {
			self.failure_handlers.invalid_accesses(origin);
		}
		if self.allow_write_active {
			if !Self::guard_read_allow_prefix(&self.filters_allow, child_info, key) {
				self.failure_handlers.invalid_allowed_access();
			}
		}
	}

	pub(super) fn guard_write_prefix(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		let blocked = Self::key_write_forbid_prefix(&self.filters_forbid, child_info, key);
		for origin in blocked {
			self.failure_handlers.invalid_accesses(origin);
		}
		if self.allow_write_active {
			if !Self::guard_write_allow_prefix(&self.filters_allow, child_info, key) {
				self.failure_handlers.invalid_allowed_access();
			}
		}
	}

	pub(super) fn guard_read_interval(
		&self,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) {
		let blocked = Self::key_read_forbid_interval(&self.filters_forbid, child_info, key, key_end);
		for origin in blocked {
			self.failure_handlers.invalid_accesses(origin);
		}
		if self.allow_write_active || self.allow_read_active {
			if !Self::guard_read_allow_interval(&self.filters_allow, child_info, key, key_end) {
				self.failure_handlers.invalid_allowed_access();
			}
		}
	}

	pub(super) fn remove_worker(&mut self, task_id: TaskId) {
		if let Some(decl) = self.changes.remove(&task_id) {
			for (_child_storage, declaration) in decl.into_iter() {
				match declaration {
					WorkerDeclaration::Stateless
					| WorkerDeclaration::ReadLastBlock
					| WorkerDeclaration::ReadAtSpawn
					| WorkerDeclaration::WriteAtSpawn => (),
					WorkerDeclaration::ReadAtJoinOptimistic => (),
					WorkerDeclaration::WriteOptimistic => (),
					WorkerDeclaration::WriteAtJoinOptimistic => (),
					WorkerDeclaration::ReadAtJoinDeclarative(filter, _failure) => {
						// undo a `set_parent_declaration` call.
						self.failure_handlers.remove(task_id);
						self.remove_forbid_writes(filter, task_id);
					},
					WorkerDeclaration::WriteDeclarative(filter, _failure) => {
						self.failure_handlers.remove(task_id);
						self.remove_forbid_writes(filter, task_id);
					},
					WorkerDeclaration::WriteAtJoinDeclarative(write_filter, read_filter, _failure) => {
						self.failure_handlers.remove(task_id);
						self.remove_forbid_writes(write_filter, task_id);
						self.remove_forbid_writes(read_filter, task_id);
					},
				}
			}
		}
	}

	pub(super) fn is_result_for_parent_invalid(&self) -> bool {
		self.failure_handlers.parent_failure_handler.did_fail()
	}
}

#[derive(Debug, Clone, Default)]
pub struct Filter<F: Debug + Clone + Default> {
	/// write superseed read when define.
	/// So if forbid is only defined at write level.
	write_prefix: F,
	write_key: F,
	// read only is ignore 'false' or allow (forbid readonly
	// is equivalent to forbid write).
	read_only_prefix: F,
	read_only_key: F,
}

impl Filter<FilterOrigin> {
	fn is_empty(&self) -> bool {
		self.write_prefix.is_empty()
			&& self.write_key.is_empty()
			&& self.read_only_prefix.is_empty()
			&& self.read_only_key.is_empty()
	}
}

#[derive(Debug, Clone, Default)]
pub struct FilterOrigin {
	children: Option<BTreeSet<TaskId>>,
}

impl FilterOrigin {
	fn is_defined(&self) -> bool {
		self.children.is_some()
	}

	fn set(&mut self, from_child: TaskId) {
		if self.children.is_none() {
			let mut children = BTreeSet::new();
			children.insert(from_child);
			self.children = Some(children);
		} else {
			if let Some(children) = self.children.as_mut() {
				children.insert(from_child);
			}
		}
	}

	fn remove(&mut self, from_child: TaskId) {
		if self.children.as_mut()
			.map(|set| {
				set.remove(&from_child);
				set.is_empty()
			}).unwrap_or(false) {
			self.children = None;
		}
	}

	fn is_empty(&self) -> bool {
		self.children.as_ref()
			.map(|c| c.is_empty())
			.unwrap_or(true)
	}
}

pub(super) mod failure {
	use sp_std::cell::Cell;
	use sp_externalities::{TaskId, DeclarationFailureHandling};
	use sp_std::collections::btree_map::BTreeMap;

	/// Worker state for failure.
	#[derive(Debug, Clone, Default)]
	pub(super) struct DeclFailureHandling {
		/// When failure handling is not panic this is set to `true` on
		/// error.
		/// When this is true the worker result will be resolved to invalid.
		did_fail: Cell<bool>,

		/// How to handle worker broken assumption (panic or invalid result).
		failure: DeclarationFailureHandling,
	}

	impl DeclFailureHandling {
		pub(super) fn did_fail(&self) -> bool {
			self.did_fail.get()
		}

		fn invalid_access(&self) {
			match self.failure {
				DeclarationFailureHandling::Panic => {
					panic!(super::BROKEN_DECLARATION_ACCESS);
				},
				DeclarationFailureHandling::InvalidAtJoin => {
					self.did_fail.set(true);
				},
			}
		}
	}

	/// Main state for failure handlers.
	/// We can have different handling for every worker.
	#[derive(Debug, Clone)]
	pub(super) struct FailureHandlers {
		// For failure as declare by parent.
		// TODO rename to shorter name (same for children)
		pub(super) parent_failure_handler: DeclFailureHandling,
		// For failure as declare by children.
		pub(super) children_failure_handler: BTreeMap<TaskId, DeclFailureHandling>,
	}

	impl FailureHandlers {
		// TODO rename to invalid parent access?
		pub(super) fn invalid_allowed_access(&self) {
			self.parent_failure_handler.invalid_access();
		}

		// TODO rename to invalid child access?
		pub(super) fn invalid_accesses(&self, origin: &super::FilterOrigin) {
			if let Some(children) = origin.children.as_ref() {
				for child in children.iter() {
					self.invalid_access(*child);
				}
			}
		}

		fn invalid_access(&self, from_child: TaskId) {
			self.children_failure_handler.get(&from_child).expect("TODO").invalid_access()
		}

		pub(super) fn set_failure_handler(&mut self, from_child: Option<TaskId>, failure: DeclarationFailureHandling) {
			let handling = DeclFailureHandling {
				did_fail: Default::default(),
				failure,
			};
			if let Some(id) = from_child {
				self.children_failure_handler.insert(id, handling);
			} else {
				self.parent_failure_handler = handling;
			}
		}

		pub(super) fn remove(&mut self, child: TaskId) {
			self.children_failure_handler.remove(&child);
		}

		// TODO this does not make much sense, should be specific to a child marker
		pub(super) fn did_fail(&self) -> bool {
			if self.parent_failure_handler.did_fail.get() {
				return true;
			}
			for (_id, handler) in self.children_failure_handler.iter() {
				if handler.did_fail.get() {
					return true;
				}
			}
			false
		}
	}
}
