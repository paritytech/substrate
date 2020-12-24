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
use sp_std::cell::RefCell;
use crate::overlayed_changes::radix_trees::AccessTreeWrite;
use sp_core::storage::ChildInfo;
use super::StorageKey;
use sp_std::vec::Vec;

#[derive(Debug, Clone, Default)]
pub(super) struct AccessLogger {
	log_read: bool,
	log_write: BTreeSet<TaskId>,
	// this is roughly storage root call.
	read_all: bool,
	write_loggings_id: Vec<TaskId>,
	top_logger: StateLogger,
	children_logger: RefCell<Map<StorageKey, StateLogger>>,
}

/// Logger for a given trie state.
#[derive(Debug, Clone, Default)]
struct StateLogger {
	read_key: RefCell<Vec<Vec<u8>>>,
	// Interval is inclusive for start and end.
	read_intervals: RefCell<Vec<(Vec<u8>, Vec<u8>)>>,
	write_key: Map<Vec<u8>, BTreeSet<TaskId>>,
	// this is roughly clear prefix.
	write_prefix: AccessTreeWrite,
}

impl StateLogger {
	fn remove_read_logs(&mut self) {
		self.read_key.get_mut().clear();
		self.read_intervals.get_mut().clear();
	}
	fn remove_write_logs(&mut self) {
		self.write_key.clear();
		self.write_prefix.clear();
	}
	fn is_write_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.write_key.iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		for (_, ids) in self.write_prefix.iter().value_iter() {
			if ids.contains(&marker) {
				return false;
			}
		}
		true
	}
	fn check_write_read(&self, access: &sp_externalities::StateLog, marker_set: &BTreeSet<TaskId>) -> bool {
		let mut result = true;
		for key in access.read_keys.iter() {
			if !result {
				break;
			}
			result = self.check_write_read_key(key, marker_set);
		}
		for interval in access.read_intervals.iter() {
			if !result {
				break;
			}
			result = self.check_write_read_intervals(interval, marker_set);
		}
		result
	}
	// Note that if we ensure marker are in sync, we do not need to check
	// that.
	fn check_any_write_marker(marker_set: &BTreeSet<TaskId>, filter_set: &BTreeSet<TaskId>) -> bool {
		for task_id in filter_set.iter() {
			if marker_set.contains(task_id) {
				return true;
			}
		}
		false
	}

	fn check_write_read_key(&self, read_key: &Vec<u8>, marker_set: &BTreeSet<TaskId>) -> bool {
		let mut result = true;
		if let Some(ids) = self.write_key.get(read_key) {
			if Self::check_any_write_marker(marker_set, ids) {
				return false;
			}
		}
		for (prefix, ids) in self.write_prefix.seek_iter(read_key.as_slice()).value_iter() {
			if Self::check_any_write_marker(marker_set, ids) {
				return false;
			}
		}
		result
	}

	fn check_write_read_intervals(&self, interval: &(Vec<u8>, Vec<u8>), marker_set: &BTreeSet<TaskId>) -> bool {
		let mut result = true;
		// Could use a seek to start here, but this
		// (check read access on write) is a marginal use case
		// so not switching write_key to radix_tree at the time.
		for (key, ids) in self.write_key.iter() {
			if key > &interval.1 {
				break;
			}
			if key >= &interval.0 && Self::check_any_write_marker(marker_set, ids) {
				return false;
			}
		}
		let mut iter = self.write_prefix.seek_iter(interval.0.as_slice()).value_iter();
		while let Some((prefix, ids)) = iter.next() {
			if Self::check_any_write_marker(marker_set, ids) {
				return false;
			}
		}
		// TODO there is probably a good way to merge redundant/contigus intervals here.
		// Also have it ordered for single iteration check.
		// (in fact since most of the time they are one step of iteration this is mandatory
		// but could be do more when we register new read interval.
		for (key, ids) in iter.node_iter().iter_prefix().value_iter() {
			if key > interval.1 {
				break;
			}
			// This is can do some check twice (all write prefix that are contained
			// by start, as they also where in seek iter)
			if Self::check_any_write_marker(marker_set, ids) {
				return false;
			}
		}
		result
	}
}

impl AccessLogger {
	// actually this needs to be resolvable over the lifetime of a child worker.
	// So need to push worker id in the log.
	pub(super) fn log_writes(&mut self, worker: TaskId) {
		self.log_write.insert(worker);
	}
	// actually this is more a log all access incompatible with a parent writes
	// so you log for the whole time.
	// We don't include access for write as it will simply be the payload reported from
	// the write worker.
	pub(super) fn log_reads(&mut self) {
		self.log_read = true;
	}

	pub(super) fn on_worker_result(&mut self, result: &WorkerResult) -> bool {
		match result {
			WorkerResult::CallAt(result, marker) => {
				// should not be usefull here
				self.remove_worker(*marker);
				true
			},
			WorkerResult::Optimistic(result, marker, accesses) => {
				let mut result = true;

				if accesses.read_all {
					if result && !self.top_logger.is_write_empty(*marker) {
						result = false;
					}
					for child_logger in self.children_logger.get_mut().iter_mut() {
						if !result {
							break;
						}
						result = !child_logger.1.is_write_empty(*marker);
					}
				} else {
					if result {
						result = self.top_logger.check_write_read(&accesses.top_logger, &self.log_write);
					}
					for (storage_key, child_logger) in accesses.children_logger.iter() {
						if !result {
							break;
						}
						if let Some(access_logger) = self.children_logger.get_mut().get(storage_key) {
							result = access_logger.check_write_read(child_logger, &self.log_write);
						}
					}
				}

				self.remove_worker(*marker);
				result
			},
			// When using filter there is no directly valid case.
			WorkerResult::Valid(result) => true,
			// When using filter there is no invalid case.
			WorkerResult::Invalid => true,
			// will panic on resolve so no need to clean filter
			WorkerResult::HardPanic
			| WorkerResult::Panic => true,
		}
	}

	pub(super) fn remove_worker(&mut self, worker: TaskId) {
		self.log_write.remove(&worker);
		// we could remove all occurence, but we only do when no runing thread
		// to just clear.
		if self.log_write.is_empty() {
			self.top_logger.remove_write_logs();
			for child_logger in self.children_logger.get_mut().iter_mut() {
				child_logger.1.remove_write_logs();
			}
		}
	}

//	fn guard_read_all(&self) {
	fn log_read_all(&mut self) {
		self.read_all = true;
		self.top_logger.remove_read_logs();
		for child_logger in self.children_logger.get_mut().iter_mut() {
			child_logger.1.remove_read_logs();
		}
	}

	fn logger_mut<'a>(
		top_logger: &'a mut StateLogger,
		children_logger: &'a mut RefCell<Map<StorageKey, StateLogger>>,
		child_info: Option<&ChildInfo>,
	) -> &'a mut StateLogger {
		if let Some(child_info) = child_info {
			let storage_key = child_info.storage_key();
			children_logger.get_mut().entry(storage_key.to_vec()).or_insert_with(Default::default)
		} else {
			top_logger
		}
	}

//	fn guard_read(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_read(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
		if self.log_read && !self.read_all {
			let mut ref_children;
			let logger = if let Some(child_info) = child_info {
				let storage_key = child_info.storage_key();
				if !self.children_logger.borrow().contains_key(storage_key) {
					self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
				}
				ref_children = self.children_logger.borrow();
				ref_children.get(storage_key).expect("lazy init above")
			} else {
				&self.top_logger
			};
			// TODO consider map
			logger.read_key.borrow_mut().push(key.to_vec());
		}
	}

//	fn guard_read_interval(&self, child_info: Option<&ChildInfo>, key: &[u8], key_end: &[u8]) {
	pub(super) fn log_read_interval(&self, child_info: Option<&ChildInfo>, key: &[u8], key_end: &[u8]) {
		if self.log_read && !self.read_all {
			let mut ref_children;
			let logger = if let Some(child_info) = child_info {
				let storage_key = child_info.storage_key();
				if !self.children_logger.borrow().contains_key(storage_key) {
					self.children_logger.borrow_mut().insert(storage_key.to_vec(), Default::default());
				}
				ref_children = self.children_logger.borrow();
				ref_children.get(storage_key).expect("lazy init above")
			} else {
				&self.top_logger
			};
			// TODO consider map
			logger.read_intervals.borrow_mut().push((key.to_vec(), key_end.to_vec()));
		}
	}

//	fn guard_write(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, child_info);
			let mut entry = logger.write_key.entry(key.to_vec()).or_insert_with(Default::default);
			entry.extend(self.log_write.iter());
		}
	}

//	fn guard_write_prefix(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write_prefix(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, child_info);
			// TODO an entry api in radix_tree would be nice.
			if let Some(entry) = logger.write_prefix.get_mut(key) {
				entry.extend(self.log_write.iter());
			} else {
				logger.write_prefix.insert(key, self.log_write.clone());
			}
		}
	}

	pub(super) fn extract_read(&mut self) -> Option<sp_externalities::AccessLog> {
		if !self.log_read {
			return None;
		}

		if self.read_all {
			// Resetting state is not strictly needed, extract read should only happen
			// on end of lifetime of the overlay (at worker return).
			// But writing it for having explicitly a clean read state.
			self.read_all = false;
			return Some(sp_externalities::AccessLog {
				read_all: true,
				top_logger: Default::default(),
				children_logger: Default::default(),
			})
		}

		let read_keys = sp_std::mem::take(self.top_logger.read_key.get_mut());
		let read_intervals = sp_std::mem::take(self.top_logger.read_intervals.get_mut());
		let top_logger = sp_externalities::StateLog { read_keys, read_intervals };
		let children_logger: Vec<_> = self.children_logger.get_mut().iter_mut().map(|(storage_key, logger)| {
			let read_keys = sp_std::mem::take(logger.read_key.get_mut());
			let read_intervals = sp_std::mem::take(logger.read_intervals.get_mut());
			(storage_key, sp_externalities::StateLog { read_keys, read_intervals })
		}).collect();
		Some(sp_externalities::AccessLog {
			read_all: false,
			top_logger: Default::default(),
			children_logger: Default::default(),
		})
	}
}

