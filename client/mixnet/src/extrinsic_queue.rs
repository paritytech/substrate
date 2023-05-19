// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! [`ExtrinsicQueue`] is a queue for extrinsics received from the mixnet. These extrinsics are
//! explicitly delayed by a random amount, to decorrelate the times at which they are received from
//! the times at which they are broadcast to peers.

use mixnet::reply_manager::ReplyContext;
use std::{cmp::Ordering, collections::BinaryHeap, time::Instant};

/// `Eq` and `Ord` are implemented for this to support use in `BinaryHeap`s. Only `deadline` is
/// compared.
struct DelayedExtrinsic<E> {
	/// When the extrinsic should actually be submitted to the pool.
	deadline: Instant,
	extrinsic: E,
	reply_context: ReplyContext,
}

impl<E> PartialEq for DelayedExtrinsic<E> {
	fn eq(&self, other: &Self) -> bool {
		self.deadline == other.deadline
	}
}

impl<E> Eq for DelayedExtrinsic<E> {}

impl<E> PartialOrd for DelayedExtrinsic<E> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<E> Ord for DelayedExtrinsic<E> {
	fn cmp(&self, other: &Self) -> Ordering {
		// Extrinsics with the earliest deadline considered greatest
		self.deadline.cmp(&other.deadline).reverse()
	}
}

pub struct ExtrinsicQueue<E> {
	capacity: usize,
	queue: BinaryHeap<DelayedExtrinsic<E>>,
	next_deadline_changed: bool,
}

impl<E> ExtrinsicQueue<E> {
	pub fn new(capacity: usize) -> Self {
		Self { capacity, queue: BinaryHeap::with_capacity(capacity), next_deadline_changed: false }
	}

	pub fn next_deadline(&self) -> Option<Instant> {
		self.queue.peek().map(|extrinsic| extrinsic.deadline)
	}

	pub fn next_deadline_changed(&mut self) -> bool {
		let changed = self.next_deadline_changed;
		self.next_deadline_changed = false;
		changed
	}

	pub fn has_space(&self) -> bool {
		self.queue.len() < self.capacity
	}

	pub fn insert(&mut self, deadline: Instant, extrinsic: E, reply_context: ReplyContext) {
		debug_assert!(self.has_space());
		let prev_deadline = self.next_deadline();
		self.queue.push(DelayedExtrinsic { deadline, extrinsic, reply_context });
		if self.next_deadline() != prev_deadline {
			self.next_deadline_changed = true;
		}
	}

	pub fn pop(&mut self) -> Option<(E, ReplyContext)> {
		self.next_deadline_changed = true;
		self.queue.pop().map(|extrinsic| (extrinsic.extrinsic, extrinsic.reply_context))
	}
}
