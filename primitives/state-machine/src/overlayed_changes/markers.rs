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

//! Markers associated with workers transactional states.
//!
//! This could be implemented directly into the OverlayChange, but
//! is kept out separate worker management codebase and transaction
//! management code base as much as possible.
//!
//! The purpose of these markers is to ensure the state on worker `join`
//! is not in a overlay transaction that is no longer correct (in this case
//! we join to an invalid state).
//!
//! It also enforce that child workers transaction behave as non worker
//! transaction (panic if there is an unclosed transaction that is not
//! from the worker, panic if trying to close or commit a transaction
//! that is not from the worker).

use sp_std::collections::btree_map::BTreeMap;
use sp_externalities::{WorkerResult, TaskId};
use sp_std::{vec, vec::Vec};

#[derive(Debug, Clone)]
pub(super) struct Markers {
	// current valid task ids
	markers: BTreeMap<TaskId, MarkerDesc>,
	// current transaction and associated
	// task ids.
	transactions: Vec<Vec<TaskId>>,
	// Depth of overlay transaction when
	// starting the worker.
	// When extracting data we would check
	// transactions.len() == 1
	// and then extract from overlay up to this
	// depth.
	start_depth: usize,
}

#[derive(Debug, Clone)]
struct MarkerDesc {
	transaction_depth: usize,
}

impl Default for Markers {
	fn default() -> Self {
		Markers {
			markers: BTreeMap::new(),
			transactions: vec![Default::default()],
			start_depth: 0,
		}
	}
}

impl Markers {
	/// Initialize marker for an existing overlay.
	pub(super) fn from_start_depth(start_depth: usize) -> Self {
		Markers {
			markers: BTreeMap::new(),
			transactions: vec![Default::default()],
			start_depth,
		}
	}

	/// Access base depth for this worker overlay.
	pub(super) fn start_depth(&self) -> usize {
		self.start_depth
	}
}

impl Markers {
	fn current_transaction_internal(transactions: &mut Vec<Vec<TaskId>>) -> (&mut Vec<TaskId>, usize) {
		let len = transactions.len();
		(transactions.last_mut()
			.expect("Initialized above"), len)
	}

	/// Add a marker at current transaction depth.
	pub(super) fn set_marker(&mut self, marker: TaskId) {
		let (tx, index) = Self::current_transaction_internal(&mut self.transactions);
		self.markers.insert(marker, MarkerDesc {
			transaction_depth: index,
		});
		tx.push(marker)
	}

	pub(super) fn start_transaction(&mut self) {
		self.transactions.push(Default::default());
	}

	#[must_use]
	pub(super) fn rollback_transaction(&mut self) -> Vec<TaskId> {
		if self.transactions.len() < 2 {
			panic!("Trying to rollback a transaction that was not open by the worker.");
		}
		if let Some(markers) = self.transactions.pop() {
			for marker in markers.iter() {
				self.markers.remove(marker);
			}
			markers
		} else {
			Default::default()
		}
	}

	#[must_use]
	pub(super) fn commit_transaction(&mut self) -> Vec<TaskId> {
		if self.transactions.len() < 2 {
			panic!("Trying to commit a transaction that was not open by the worker.");
		}
		if let Some(markers) = self.transactions.pop() {
			for marker in markers.iter() {
				self.markers.remove(marker);
			}
			markers
		} else {
			Default::default()
		}
	}

	pub(super) fn remove_worker(&mut self, marker: TaskId) -> bool {
		match self.markers.remove(&marker) {
			Some(marker_desc) => {
				if let Some(markers) = self.transactions.get_mut(marker_desc.transaction_depth) {
					if let Some(ix) = markers.iter().position(|id| id == &marker) {
						markers.remove(ix);
					}
				}
				true
			}
			None => false,
		}
	}

	pub(super) fn on_worker_result(&mut self, result: &WorkerResult) -> bool {
		match result {
			WorkerResult::CallAt(_result, _delta, marker) => {
				// invalid when nothing
				self.remove_worker(*marker)
			},
			WorkerResult::Optimistic(_result, _delta, marker, _accesses) => {
				// invalid when nothing
				self.remove_worker(*marker)
			},
			WorkerResult::Valid(_result, _delta) => true,
			WorkerResult::Invalid => true,
			WorkerResult::RuntimePanic
			| WorkerResult::HardPanic => true,
		}
	}
}
