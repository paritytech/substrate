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

//! State access loggers.
//!
//! When optimistic worker is runnig, we logg our externalities access to be able
//! to resolve if the assumptions are correct on `join`.
//!
//! It is plugged in the overlay by commodity, but could be at a higher level.

use sp_externalities::{WorkerResult, TaskId};
use sp_std::collections::btree_set::BTreeSet;
#[cfg(feature = "std")]
use std::collections::HashMap as Map;
#[cfg(not(feature = "std"))]
use sp_std::collections::btree_map::BTreeMap as Map;
use sp_std::cell::{Cell, RefCell};
use crate::overlayed_changes::radix_trees::{AccessTreeWrite, AccessTreeWriteParent};
use sp_core::storage::ChildInfo;
use super::{StorageKey, retain_map};
use sp_std::vec::Vec;

/// Origin for the log.
/// None when the log is for the lifetime of the worker or
/// a children running id when this is related to a children
/// worker.
pub(crate) type OriginLog = BTreeSet<TaskId>;

#[derive(Debug, Clone, Default)]
pub(super) struct AccessLogger {
	/// True when logging read is needed.
	/// for this optimistic mode.
	/// This read is always compared with parent
	/// writes.
	parent_log_read: bool,
	/// True when logging write is needed.
	/// We do not use the child delta here to be able to
	/// keep trace of dropped transactional accesses.
	/// This read is always compared with parent
	/// writes and read when enabled.
	parent_log_write: bool,
	log_read: OriginLog,
	log_write: OriginLog,
	// this is roughly storage root call.
	parent_read_all: Cell<bool>,
	children_read_all: RefCell<OriginLog>,
	top_logger: StateLogger,
	children_logger: RefCell<Map<StorageKey, StateLogger>>,
	// TODO unused.
	eager_clean: bool,
}

/// Logger for a given trie state.
#[derive(Debug, Clone, Default)]
struct StateLogger {
	parent_read_key: RefCell<Vec<Vec<u8>>>,
	children_read_key: RefCell<Map<Vec<u8>, OriginLog>>,
	// Intervals are inclusive for start and end.
	parent_read_intervals: RefCell<Vec<(Vec<u8>, Option<Vec<u8>>)>>,
	children_read_intervals: RefCell<Map<(Vec<u8>, Option<Vec<u8>>), OriginLog>>,
	parent_write_key: Vec<Vec<u8>>,
	children_write_key: Map<Vec<u8>, OriginLog>,
	// this is roughly clear prefix.
	parent_write_prefix: AccessTreeWriteParent,
	children_write_prefix: AccessTreeWrite,
}

impl StateLogger {
	fn remove_parent_read_logs(&self) {
		self.parent_read_key.borrow_mut().clear();
		self.parent_read_intervals.borrow_mut().clear();
	}

	fn remove_all_children_read_logs(&mut self) {
		self.children_read_key.get_mut().clear();
		self.children_read_intervals.get_mut().clear();
	}

	fn remove_all_children_write_logs(&mut self) {
		self.children_write_key.clear();
		self.children_write_prefix.clear();
	}

	fn remove_children_read_logs(&mut self, marker: TaskId) {
		retain_map(self.children_read_key.get_mut(), |_key, value| {
			value.remove(&marker);
			!value.is_empty()
		});
		retain_map(self.children_read_intervals.get_mut(), |_key, value| {
			value.remove(&marker);
			!value.is_empty()
		});
	}

	fn remove_children_write_logs(&mut self, marker: TaskId) {
		retain_map(&mut self.children_write_key, |_key, value| {
			value.remove(&marker);
			!value.is_empty()
		});
		let mut to_remove = Vec::new();
		for (key, value) in self.children_write_prefix.iter_mut().value_iter_mut() {
			value.remove(&marker);
			if value.is_empty() {
				to_remove.push(key.to_vec())
			}
		}
		for key in to_remove.into_iter() {
			self.children_write_prefix.remove(&key);
		}
	}

	fn is_children_read_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.children_read_key.borrow().iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		for (_, ids) in self.children_read_intervals.borrow().iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		true
	}

	fn is_children_write_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.children_write_key.iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		for (_, ids) in self.children_write_prefix.iter().value_iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		true
	}

	// TODO rename
	// compare write from parent (`self`) against read from child (`access`).
	fn check_write_read(&self, access: &sp_externalities::StateLog, marker: TaskId) -> bool {
		for key in access.read_keys.iter() {
			if !self.check_key_against_write(key, marker) {
				return false;
			}
		}
		for interval in access.read_intervals.iter() {
			if !self.check_interval_against_write(interval, marker) {
				return false;
			}
		}
		true
	}

	// compare read from parent (`self`) against write from child (`access`).
	fn check_read_write(&self, access: &sp_externalities::StateLog, marker: TaskId) -> bool {
		for key in access.write_keys.iter() {
			if !self.check_key_against_read(key, marker) {
				return false;
			}
		}
		// Here ordering prefix could be use to optimize check (skiping child of a given prefix).
		for prefix in access.write_prefix.iter() {
			if !self.check_prefix_against_read(prefix, marker) {
				return false;
			}
		}
		true
	}
	// compare write from parent (`self`) against write from child (`access`).
	fn check_write_write(&self, access: &sp_externalities::StateLog, marker: TaskId) -> bool {
		for key in access.write_keys.iter() {
			if !self.check_key_against_write(key, marker) {
				return false;
			}
		}
		// Here ordering prefix could be use to optimize check (skiping child of a given prefix).
		for prefix in access.write_prefix.iter() {
			if !self.check_prefix_against_write(prefix, marker) {
				return false;
			}
		}
		true
	}
/*
	// Note that if we ensure marker are in sync, we do not need to check
	// that.
	// TODO rename intersect workrers and look for native defs (also OriginLog could be different
	// type)..
	fn check_any_write_marker(marker_set: &OriginLog, filter_set: &OriginLog) -> bool {
		for task_id in filter_set.iter() {
			if marker_set.contains(task_id) {
				return true;
			}
		}
		false
	}
*/
	fn check_key_against_write(&self, read_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.children_write_key.get(read_key) {
			if ids.contains(&marker) {
				return false;
			}
		}
		for (_prefix, ids) in self.children_write_prefix.seek_iter(read_key.as_slice()).value_iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		true
	}

	fn check_key_against_read(&self, read_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.children_read_key.borrow().get(read_key) {
			if ids.contains(&marker) {
				return false;
			}
		}
		// TODO this needs proper children_read_intervals structure.
		for ((start, end), ids) in self.children_read_intervals.borrow().iter() {
			if read_key >= start && end.as_ref().map(|end| read_key <= end).unwrap_or(true) {
				if ids.contains(&marker) {
					return false;
				}
			}
		}
		true
	}

	fn check_prefix_against_write(&self, prefix: &Vec<u8>, marker: TaskId) -> bool {
		// TODO here could benefit from a seek then iter.
		let mut first = false;
		for (key, ids) in self.children_write_key.iter() {
			if key.starts_with(prefix) {
				if ids.contains(&marker) {
					return false;
				} else {
					first = true;
				}
			} else if first {
				break;
			}
		}
		let mut iter = self.children_write_prefix.seek_iter(prefix).value_iter();
		while let Some((_prefix, ids)) = iter.next() {
			if ids.contains(&marker) {
				return false;
			}
		}
		for (_key, ids) in iter.node_iter().iter_prefix().value_iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		true	
	}

	fn check_prefix_against_read(&self, prefix: &Vec<u8>, marker: TaskId) -> bool {
		// TODO here could benefit from a seek then iter.
		let mut first = false;
		for (key, ids) in self.children_read_key.borrow().iter() {
			if key.starts_with(prefix) {
				if ids.contains(&marker) {
					return false;
				} else {
					first = true;
				}
			} else if first {
				break;
			}
		}
		// TODO this needs proper children_read_intervals structure.
		for ((start, end), ids) in self.children_read_intervals.borrow().iter() {
			if prefix.len() == 0
				|| start.starts_with(prefix)
				|| end.as_ref().map(|end| end.starts_with(prefix)).unwrap_or(false)
				|| (start >= start && end.as_ref().map(|end| prefix <= end).unwrap_or(true)) {
				if ids.contains(&marker) {
					return false;
				}
			}
		}
		true	
	}

	fn check_interval_against_write(
		&self,
		interval: &(Vec<u8>, Option<Vec<u8>>),
		marker: TaskId,
	) -> bool {
		// Could use a seek to start here, but this
		// (check read access on write) is a marginal use case
		// so not switching write_key to radix_tree at the time.
		for (key, ids) in self.children_write_key.iter() {
			if interval.1.as_ref().map(|end| key > end).unwrap_or(false) {
				break;
			}
			if key >= &interval.0 && ids.contains(&marker) {
				return false;
			}
		}
		let mut iter = self.children_write_prefix.seek_iter(interval.0.as_slice()).value_iter();
		while let Some((_prefix, ids)) = iter.next() {
			if ids.contains(&marker) {
				return false;
			}
		}
		// TODO there is probably a good way to merge redundant/contigus intervals here.
		// Also have it ordered for single iteration check.
		// (in fact since most of the time they are one step of iteration this is mandatory
		// but could be do more when we register new read interval.
		for (key, ids) in iter.node_iter().iter().value_iter() {
			if interval.1.as_ref().map(|end| &key > end).unwrap_or(false) {
				break;
			}
			// This is can do some check twice (all write prefix that are contained
			// by start, as they also where in seek iter)
			if ids.contains(&marker) {
				return false;
			}
		}
		true
	}
}

impl AccessLogger {
	fn is_children_read_empty(&self, marker: TaskId) -> bool {
		if !self.top_logger.is_children_read_empty(marker) {
			return false;
		}
		for child_logger in self.children_logger.borrow().iter() {
			if !child_logger.1.is_children_read_empty(marker) {
				return false;
			}
		}

		true
	}

	fn is_children_write_empty(&self, marker: TaskId) -> bool {
		if !self.top_logger.is_children_write_empty(marker) {
			return false;
		}
		for child_logger in self.children_logger.borrow().iter() {
			if !child_logger.1.is_children_write_empty(marker) {
				return false;
			}
		}

		true
	}


	pub(super) fn log_writes(&mut self, children: Option<TaskId>) {
		if let Some(worker) = children {
			self.log_write.insert(worker);
		} else {
			self.parent_log_write = true;
		}
	}

	pub(super) fn log_reads(&mut self, children: Option<TaskId>) {
		if let Some(worker) = children {
			self.log_read.insert(worker);
		} else {
			self.parent_log_read = true;
		}
	}

	pub(super) fn on_worker_result(&mut self, result: &WorkerResult) -> bool {
		match result {
			WorkerResult::CallAt(_result, _delta, marker) => {
				// should not be usefull here
				self.remove_worker(*marker);
				true
			},
			WorkerResult::Optimistic(_result, _delta, marker, accesses) => {
				let result = || -> bool {
					let has_read_child = accesses.has_read();
					let has_write_child = accesses.has_write();
					let has_read_parent = !self.is_children_read_empty(*marker);
					let has_write_parent = !self.is_children_write_empty(*marker);

					if has_read_child {
						if accesses.read_all {
							if has_write_parent {
								return false;
							}
						} else if has_write_parent {
							if !self.top_logger.check_write_read(&accesses.top_logger, *marker) {
								return false;
							}
							for (storage_key, child_logger) in accesses.children_logger.iter() {
								if let Some(access_logger) = self.children_logger.get_mut().get(storage_key) {
									if !access_logger.check_write_read(child_logger, *marker) {
										return false;
									}
								}
							}
						}
					}
					if has_write_child {
						if has_write_parent {
							if !self.top_logger.check_write_write(&accesses.top_logger, *marker) {
								return false;
							}
							for (storage_key, child_logger) in accesses.children_logger.iter() {
								if let Some(access_logger) = self.children_logger.get_mut().get(storage_key) {
									if !access_logger.check_write_write(child_logger, *marker) {
										return false;
									}
								}
							}
						}
						if has_read_parent {
							if self.parent_read_all.get() {
								return false;
							}
							if !self.top_logger.check_read_write(&accesses.top_logger, *marker) {
								return false;
							}
							for (storage_key, child_logger) in accesses.children_logger.iter() {
								if let Some(access_logger) = self.children_logger.get_mut().get(storage_key) {
									if !access_logger.check_read_write(child_logger, *marker) {
										return false;
									}
								}
							}
						}
					}
					// merge accesses with parent if needed
					if self.parent_log_write && has_write_child {
						// relative to the current three configs when write is logged for child, it is also for
						// parent.
						for key in accesses.top_logger.write_keys.iter() {
							self.log_write(None, key.as_slice());
						}
						for key in accesses.top_logger.write_prefix.iter() {
							self.log_write_prefix(None, key.as_slice());
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.write_keys.iter() {
								self.log_write_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
							for key in child_logger.write_prefix.iter() {
								self.log_write_prefix_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
						}

					}
					if self.parent_log_read && accesses.read_all {
						// relative to the current three configs when read is logged for child, it is also for
						// parent.
						self.log_read_all();
					} else if self.parent_log_read && has_read_child {
						for key in accesses.top_logger.read_keys.iter() {
							self.log_read(None, key.as_slice());
						}
						for key in accesses.top_logger.read_intervals.iter() {
							self.log_read_interval(None, key.0.as_slice(), key.1.as_ref().map(|end| end.as_slice()));
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.read_keys.iter() {
								self.log_read_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
							for key in child_logger.read_intervals.iter() {
								self.log_read_interval_storage_key(
									Some(storage_key.as_slice()),
									key.0.as_slice(),
									key.1.as_ref().map(|end| end.as_slice()),
								);
							}
						}
					}

					true
				} ();

				self.remove_worker(*marker);
				result
			},
			// When using filter there is no directly valid case.
			WorkerResult::Valid(_result, _delta) => true,
			// When using filter there is no invalid case.
			WorkerResult::Invalid => true,
			// will panic on resolve so no need to clean filter
			WorkerResult::RuntimePanic
			| WorkerResult::HardPanic => true,
		}
	}

	pub(super) fn remove_worker(&mut self, worker: TaskId) {
		if self.eager_clean {
			return self.remove_worker_eager(worker);
		}
		self.log_write.remove(&worker);
		// we could remove all occurence, but we only do when no runing thread
		// to just clear.
		if self.log_write.is_empty() {
			self.top_logger.remove_all_children_write_logs();
			for child_logger in self.children_logger.get_mut().iter_mut() {
				child_logger.1.remove_all_children_write_logs();
			}
		}
		self.log_read.remove(&worker);
		if self.log_read.is_empty() {
			self.top_logger.remove_all_children_read_logs();
			for child_logger in self.children_logger.get_mut().iter_mut() {
				child_logger.1.remove_all_children_read_logs();
			}
		}
	}

	fn remove_worker_eager(&mut self, worker: TaskId) {
		if self.log_write.remove(&worker) {
			if self.log_write.is_empty() {
				self.top_logger.remove_all_children_write_logs();
				for child_logger in self.children_logger.get_mut().iter_mut() {
					child_logger.1.remove_all_children_write_logs();
				}
			} else {
				self.top_logger.remove_children_write_logs(worker);
				for child_logger in self.children_logger.get_mut().iter_mut() {
					child_logger.1.remove_children_write_logs(worker);
				}
			}
		}
		if self.log_read.remove(&worker) {
			if self.log_read.is_empty() {
				self.top_logger.remove_all_children_read_logs();
				for child_logger in self.children_logger.get_mut().iter_mut() {
					child_logger.1.remove_all_children_read_logs();
				}
			} else {
				self.top_logger.remove_children_read_logs(worker);
				for child_logger in self.children_logger.get_mut().iter_mut() {
					child_logger.1.remove_children_read_logs(worker);
				}
			}
		}
	}

//	fn guard_read_all(&self) {
	pub(super) fn log_read_all(&self) {
		if self.parent_log_read && !self.parent_read_all.get() {
			self.parent_read_all.set(true);
			self.top_logger.remove_parent_read_logs();
			for child_logger in self.children_logger.borrow_mut().iter_mut() {
				child_logger.1.remove_parent_read_logs();
			}
		}
		if !self.log_read.is_empty() {
			self.children_read_all.borrow_mut().extend(self.log_read.iter().cloned());
			// Here we could remove children read logs, not sure if useful (need iter and filtering).
		}
	}

	fn logger_mut<'a>(
		top_logger: &'a mut StateLogger,
		children_logger: &'a mut RefCell<Map<StorageKey, StateLogger>>,
		storage_key: Option<&[u8]>,
	) -> &'a mut StateLogger {
		if let Some(storage_key) = storage_key {
			children_logger.get_mut().entry(storage_key.to_vec()).or_insert_with(Default::default)
		} else {
			top_logger
		}
	}

//	fn guard_read(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_read(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_read_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}
	fn log_read_storage_key(&self, storage_key: Option<&[u8]>, key: &[u8]) {
		let mut ref_children;
		if self.parent_log_read && !self.parent_read_all.get() {
			let logger = if let Some(storage_key) = storage_key {
				if !self.children_logger.borrow().contains_key(storage_key) {
					self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
				}
				ref_children = self.children_logger.borrow();
				ref_children.get(storage_key).expect("lazy init above")
			} else {
				&self.top_logger
			};
			// TODO consider map
			logger.parent_read_key.borrow_mut().push(key.to_vec());
		}
		if !self.log_read.is_empty() {
			let children_read_all = self.children_read_all.borrow();
			let mut children = self.log_read.difference(&children_read_all);
			if !children.next().is_none() {
				let logger = if let Some(storage_key) = storage_key {
					if !self.children_logger.borrow().contains_key(storage_key) {
						self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
					}
					ref_children = self.children_logger.borrow();
					ref_children.get(storage_key).expect("lazy init above")
				} else {
					&self.top_logger
				};
				let children = self.log_read.difference(&children_read_all);
				logger.children_read_key.borrow_mut().entry(key.to_vec())
					.or_default().extend(children.cloned());
			}
		}
	}

	pub(super) fn log_read_interval(
		&self,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) {
		self.log_read_interval_storage_key(child_info.map(|child_info| child_info.storage_key()), key, key_end)
	}

	fn log_read_interval_storage_key(
		&self,
		storage_key: Option<&[u8]>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) {
		let mut ref_children;
		if self.parent_log_read && !self.parent_read_all.get() {
			let logger = if let Some(storage_key) = storage_key {
				if !self.children_logger.borrow().contains_key(storage_key) {
					self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
				}
				ref_children = self.children_logger.borrow();
				ref_children.get(storage_key).expect("lazy init above")
			} else {
				&self.top_logger
			};
			// TODO consider map
			logger.parent_read_intervals.borrow_mut().push((key.to_vec(), key_end.map(|end| end.to_vec())));
		}
		if !self.log_read.is_empty() {
			let children_read_all = self.children_read_all.borrow();
			let mut children = self.log_read.difference(&children_read_all);
			if !children.next().is_none() {
				let logger = if let Some(storage_key) = storage_key {
					if !self.children_logger.borrow().contains_key(storage_key) {
						self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
					}
					ref_children = self.children_logger.borrow();
					ref_children.get(storage_key).expect("lazy init above")
				} else {
					&self.top_logger
				};
				let children = self.log_read.difference(&children_read_all);
				logger.children_read_intervals.borrow_mut().entry((key.to_vec(), key_end.map(|end| end.to_vec())))
					.or_default().extend(children.cloned());
			}
		}
	}

//	fn guard_write(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_write_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_write_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if self.parent_log_write {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			logger.parent_write_key.push(key.to_vec())
		}
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			logger.children_write_key.entry(key.to_vec())
				.or_default().extend(self.log_write.iter());
		}
	}

//	fn guard_write_prefix(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write_prefix(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_write_prefix_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_write_prefix_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if self.parent_log_write {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			logger.parent_write_prefix.insert(key, ());
		}
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			// TODO an entry api in radix_tree would be nice.
			if let Some(entry) = logger.children_write_prefix.get_mut(key) {
				entry.extend(self.log_write.iter());
			} else {
				logger.children_write_prefix.insert(key, self.log_write.clone());
			}
		}
	}

	pub(super) fn extract_parent_log(&mut self) -> Option<sp_externalities::AccessLog> {
		if !self.parent_log_read && !self.parent_log_write {
			return None;
		}

		let mut result = sp_externalities::AccessLog::default();
		if self.parent_read_all.get() {
			// Resetting state is not strictly needed, extract read should only happen
			// on end of lifetime of the overlay (at worker return).
			// But writing it for having explicitly a clean read state.
			self.parent_read_all.set(false);
			result.read_all = true;
		}
		if !result.read_all {
			result.top_logger.read_keys = sp_std::mem::take(self.top_logger.parent_read_key.get_mut());
			result.top_logger.read_intervals = sp_std::mem::take(self.top_logger.parent_read_intervals.get_mut());
		}
		result.top_logger.write_keys = sp_std::mem::take(&mut self.top_logger.parent_write_key);
		result.top_logger.write_prefix = sp_std::mem::take(&mut self.top_logger.parent_write_prefix)
			.iter().value_iter().map(|(key, _)| key).collect();
		result.children_logger = self.children_logger.get_mut().iter_mut()
			.map(|(storage_key, logger)| {
			let mut log = sp_externalities::StateLog::default();
			if !result.read_all {
				log.read_keys = sp_std::mem::take(logger.parent_read_key.get_mut());
				log.read_intervals = sp_std::mem::take(logger.parent_read_intervals.get_mut());
			}
			log.write_keys = sp_std::mem::take(&mut logger.parent_write_key);
			log.write_prefix = sp_std::mem::take(&mut logger.parent_write_prefix)
				.iter().value_iter().map(|(key, _)| key).collect();
			(storage_key.clone(), log)
		}).collect();

		Some(result)
	}
}
