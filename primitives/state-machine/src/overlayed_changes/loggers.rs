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
//!
//! TODO checks method should be rewrite by zip iterating on all sorted components, 
//! and maintaining a streaming state machine,
//! this would also require a 'jump_to' instruction on tree iterator.

use sp_externalities::{WorkerResult, TaskId, StateLog};
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
	/// True when logging read is needed in order
	/// to send and compare the log to the parent worker.
	parent_log_read: bool,
	/// True when logging write is needed in order
	/// to send and compare the log to the parent worker.
	parent_log_write: bool,
	/// Keep trace of read logging required to compare with children
	/// logged access.
	log_read: OriginLog,
	/// Keep trace of read logging required to compare with children
	/// logged access.
	log_write: OriginLog,
	/// Log that we access all key in read mode (usually by calling storage root).
	parent_read_all: Cell<bool>,
	/// Log that we access all key in read mode (usually by calling storage root),
	/// with some child workers running.
	children_read_all: RefCell<OriginLog>,
	/// Access logger for top trie.
	top_logger: StateLogger,
	/// Access logger for children trie.
	children_logger: RefCell<Map<StorageKey, StateLogger>>,
	// TODO unused except in test.
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

	// compare write from parent (`self`) against read from child (`access`).
	fn check_write_read(&self, access: &StateLog, marker: TaskId) -> bool {
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
	fn check_read_write(&self, access: &StateLog, marker: TaskId) -> bool {
		for key in access.read_write_keys.iter() {
			if !self.check_key_against_read(key, marker) {
				return false;
			}
		}
		// Here ordering prefix could be use to optimize check (skiping child of a given prefix).
		for prefix in access.read_write_prefix.iter() {
			if !self.check_prefix_against_read(prefix, marker) {
				return false;
			}
		}
		true
	}
	// compare write from parent (`self`) against write from child (`access`).
	fn check_write_write(&self, access: &StateLog, marker: TaskId) -> bool {
		for key in access.read_write_keys.iter() {
			if !self.check_key_against_write(key, marker) {
				return false;
			}
		}
		// Here ordering prefix could be use to optimize check (skiping child of a given prefix).
		for prefix in access.read_write_prefix.iter() {
			if !self.check_prefix_against_write(prefix, marker) {
				return false;
			}
		}
		true
	}

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

	fn check_key_against_read(&self, write_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.children_read_key.borrow().get(write_key) {
			if ids.contains(&marker) {
				return false;
			}
		}
		// TODO this needs proper children_read_intervals structure.
		for ((start, end), ids) in self.children_read_intervals.borrow().iter() {
			if write_key >= start && end.as_ref().map(|end| write_key <= end).unwrap_or(true) {
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
				|| (prefix >= start && end.as_ref().map(|end| prefix <= end).unwrap_or(true)) {
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
		// TODO here we really should merge redundant/contigus intervals on insert.
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
					let has_read_write_child = accesses.has_read_write();
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
					if has_read_write_child {
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
					if self.parent_log_write && has_read_write_child {
						// relative to the current three configs when write is logged for child, it is also for
						// parent.
						for key in accesses.top_logger.read_write_keys.iter() {
							self.log_write(None, key.as_slice());
						}
						for key in accesses.top_logger.read_write_prefix.iter() {
							self.log_write_prefix(None, key.as_slice());
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.read_write_keys.iter() {
								self.log_write_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
							for key in child_logger.read_write_prefix.iter() {
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
			// TODO a 'entry' api in radix_tree would be nice.
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
		result.top_logger.read_write_keys = sp_std::mem::take(&mut self.top_logger.parent_write_key);
		result.top_logger.read_write_prefix = sp_std::mem::take(&mut self.top_logger.parent_write_prefix)
			.iter().value_iter().map(|(key, _)| key).collect();
		result.children_logger = self.children_logger.get_mut().iter_mut()
			.map(|(storage_key, logger)| {
			let mut log = StateLog::default();
			if !result.read_all {
				log.read_keys = sp_std::mem::take(logger.parent_read_key.get_mut());
				log.read_intervals = sp_std::mem::take(logger.parent_read_intervals.get_mut());
			}
			log.read_write_keys = sp_std::mem::take(&mut logger.parent_write_key);
			log.read_write_prefix = sp_std::mem::take(&mut logger.parent_write_prefix)
				.iter().value_iter().map(|(key, _)| key).collect();
			(storage_key.clone(), log)
		}).collect();

		Some(result)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_check_write_write() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		let task2 = 2u64;
		parent_access_base.log_writes(Some(task1));
		parent_access_base.log_writes(Some(task2));
		// log read should not interfere
		parent_access_base.log_reads(Some(task1));
		parent_access_base.log_reads(Some(task2));
		let mut child_access = StateLog::default();
		child_access.write_keys.push(b"key1".to_vec());
		child_access.write_prefix.push(b"prefix".to_vec());
		assert!(parent_access_base.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access_base.top_logger.check_write_write(&child_access, task2));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"key1"[..]);
		parent_access.log_read_interval(None, &b""[..], None);
		assert!(parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access.top_logger.check_write_write(&child_access, task2));

		parent_access.log_write(None, &b"key1"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(!parent_access.top_logger.check_write_write(&child_access, task2));

		parent_access.remove_worker_eager(task2);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access.top_logger.check_write_write(&child_access, task2));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"key12"[..]);
		parent_access.log_write(None, &b"key2"[..]);
		parent_access.log_write(None, &b"k"[..]);
		parent_access.log_write(None, &b""[..]);
		parent_access.log_write(None, &b"prefi"[..]);
		parent_access.log_write_prefix(None, &b"a"[..]);
		parent_access.log_write_prefix(None, &b"key10"[..]);
		assert!(parent_access.top_logger.check_write_write(&child_access, task1));

		parent_access.log_write(None, &b"prefixed"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"prefix"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"key1"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"ke"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"pre"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"prefix"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"prefixed"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
	}

	#[test]
	fn test_check_write_read() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		parent_access_base.log_writes(Some(task1));
		// log read in parent should not interfere
		parent_access_base.log_reads(Some(task1));
		let mut child_access = StateLog::default();
		child_access.write_keys.push(b"keyw".to_vec());
		child_access.write_prefix.push(b"prefixw".to_vec());
		child_access.write_prefix.push(b"prefixx".to_vec());
		child_access.write_prefix.push(b"prefixz".to_vec());
		child_access.read_keys.push(b"keyr".to_vec());
		child_access.read_intervals.push((b"st_int".to_vec(), Some(b"w".to_vec())));
		child_access.read_intervals.push((b"z_int".to_vec(), Some(b"z_inter".to_vec())));
		child_access.read_intervals.push((b"z_z".to_vec(), None));
		assert!(parent_access_base.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"keyw"[..]);
		parent_access.log_read(None, &b"keyr"[..]);
		parent_access.log_read_interval(None, &b"z_int"[..], None);
		parent_access.log_write(None, &b"ke"[..]);
		parent_access.log_write(None, &b""[..]);
		parent_access.log_write(None, &b"prefixy"[..]);
		parent_access.log_write(None, &b"st_in"[..]);
		parent_access.log_write(None, &b"w0"[..]);
		assert!(parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"keyr"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"keyw"[..]);
		parent_access.log_write(None, &b"z_inter2"[..]);
		parent_access.log_write(None, &b"z_in"[..]);
		parent_access.log_write(None, &b"z_ins"[..]);
		parent_access.log_write_prefix(None, &b"p"[..]);
		parent_access.log_write_prefix(None, &b"prefixwed"[..]);
		// Note that these logical conflict (log write involve a read) are done by
		// check_write_write when write is enabled.
		// (we rely on the fact that check_write_read is only for read only.
		assert!(parent_access.top_logger.check_write_read(&child_access, task1));

		parent_access.log_write(None, &b"keyr"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"t_in_interval"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"{_in_end_interval"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));
	
		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b""[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"t_in_interval"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"key"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"t"[..]);
		assert!(!parent_access.top_logger.check_write_read(&child_access, task1));
	}

	#[test]
	fn test_check_read_write() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		parent_access_base.log_writes(Some(task1));
		// log read in parent should not interfere
		parent_access_base.log_reads(Some(task1));
		let mut child_access = StateLog::default();
		child_access.write_keys.push(b"keyw".to_vec());
		child_access.write_prefix.push(b"prefixw".to_vec());
		child_access.write_prefix.push(b"prefixx".to_vec());
		child_access.write_prefix.push(b"prefixz".to_vec());
		child_access.read_keys.push(b"keyr".to_vec());
		child_access.read_intervals.push((b"st_int".to_vec(), Some(b"w".to_vec())));
		child_access.read_intervals.push((b"z_int".to_vec(), Some(b"z_inter".to_vec())));
		child_access.read_intervals.push((b"z_z".to_vec(), None));
		assert!(parent_access_base.top_logger.check_read_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"st_int"[..]);
		parent_access.log_read(None, &b"keyr"[..]);
		parent_access.log_read(None, &b"prefix"[..]);
		parent_access.log_read(None, &b"prefixy"[..]);
		parent_access.log_read(None, &b"keywa"[..]);
		parent_access.log_read_interval(None, &b"z_i"[..], Some(&b"z_inta"[..]));
		parent_access.log_read_interval(None, &b"z_i"[..], Some(&b"z_j"[..]));
		parent_access.log_read_interval(None, &b"z_int"[..], None);
		parent_access.log_read_interval(None, &b"pre"[..], Some(&b"prefix"[..]));
		parent_access.log_write_prefix(None, &b""[..]);
		parent_access.log_write_prefix(None, &b"z_inti"[..]);
		parent_access.log_write(None, &b"keyw"[..]);
		parent_access.log_write(None, &b"prefixx"[..]);
		assert!(parent_access.top_logger.check_read_write(&child_access, task1));

		parent_access.log_read(None, &b"keyw"[..]);
		assert!(!parent_access.top_logger.check_read_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"prefixx"[..]);
		assert!(!parent_access.top_logger.check_read_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"prefixxa"[..]);
		assert!(!parent_access.top_logger.check_read_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read_interval(None, &b"pre"[..], Some(&b"prefixx"[..]));
		assert!(!parent_access.top_logger.check_read_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read_interval(None, &b"pre"[..], None);
		assert!(!parent_access.top_logger.check_read_write(&child_access, task1));
	}
}
