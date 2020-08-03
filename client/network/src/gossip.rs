// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Helper for sending rate-limited gossip messages.
//!
//! # Context
//!
//! The [`NetworkService`] struct provides a way to send notifications to a certain peer through
//! the [`NetworkService::notification_sender`] method. This method is quite low level and isn't
//! expected to be used directly.
//!
//! The [`DirectedGossip`] struct provided by this module is built on top of
//! [`NetworkService::notification_sender`] and provides a cleaner way to send notifications.
//!
//! # Behaviour
//!
//! An instance of [`DirectedGossip`] is specific to a certain combination of `PeerId` and
//! protocol name. It maintains a buffer of messages waiting to be sent out. The user of this API
//! is able to manipulate that queue, adding or removing obsolete messages.
//!
//! Creating a [`DirectedGossip`] also returns a opaque `Future` whose responsibility it to
//! drain that queue and actually send the messages. If the substream with the given combination
//! of peer and protocol is closed, the queue is silently discarded. It is the role of the user
//! to track which peers we are connected to.
//!
//! If multiple instances of [`DirectedGossip`] exist for the same peer and protocol, or if some
//! other code uses the [`NetworkService`] to send notifications to this peer and protocol, then
//! the notifications will be interleaved in an unpredictable way.
//!

use crate::{ExHashT, NetworkService, service::{NotificationSender, NotificationSenderError}};

use async_std::sync::{Condvar, Mutex, MutexGuard};
use futures::prelude::*;
use libp2p::PeerId;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use std::{
	collections::VecDeque,
	sync::{atomic, Arc},
	time::Duration,
};

/// Notifications sender for a specific combination of network service, peer, and protocol.
pub struct DirectedGossip<M> {
	/// Shared between the front and the back task.
	shared: Arc<Shared<M>>,
}

impl<M> DirectedGossip<M> {
	/// Returns a new [`DirectedGossip`] containing a queue of message for this specific
	/// combination of peer and protocol.
	///
	/// In addition to the [`DirectedGossip`], also returns a `Future` whose role is to drive
	/// the messages sending forward.
	pub fn new<B, H, F>(
		service: Arc<NetworkService<B, H>>,
		peer_id: PeerId,
		protocol: ConsensusEngineId,
		queue_size_limit: usize,
		messages_encode: F
	) -> (Self, impl Future<Output = ()> + Send + 'static)
	where
		M: Send + 'static,
		B: BlockT + 'static,
		H: ExHashT,
		F: Fn(M) -> Vec<u8> + Send + 'static,
	{
		DirectedGossipPrototype::new(service, peer_id)
			.build(protocol, queue_size_limit, messages_encode)
	}

	/// Locks the queue of messages towards this peer.
	///
	/// The returned `Future` is expected to be ready quite quickly.
	pub async fn lock_queue<'a>(&'a self) -> QueueLock<'a, M> {
		QueueLock {
			lock: self.shared.locked.lock().await,
			condvar: &self.shared.condvar,
			queue_size_limit: self.shared.queue_size_limit,
		}
	}

	/// Pushes a message to the queue, or discards it if the queue is full.
	///
	/// The returned `Future` is expected to be ready quite quickly.
	pub async fn queue_or_discard(&self, message: M)
	where
		M: Send + 'static
	{
		self.lock_queue().await.push_or_discard(message);
	}
}

impl<M> Drop for DirectedGossip<M> {
	fn drop(&mut self) {
		// The "clean" way to notify the `Condvar` here is normally to first lock the `Mutex`,
		// then notify the `Condvar` while the `Mutex` is locked. Unfortunately, the `Mutex`
		// being asynchronous, it can't reasonably be locked from within a destructor.
		// For this reason, this destructor is a "best effort" destructor.
		// See also the corresponding code in the background task.
		self.shared.stop_task.store(true, atomic::Ordering::Acquire);
		self.shared.condvar.notify_all();
	}
}

/// Utility. Generic over the type of the messages. Holds a [`NetworkService`] and a [`PeerId`].
/// Provides a [`DirectedGossipPrototype::build`] function that builds a [`DirectedGossip`].
pub struct DirectedGossipPrototype {
	service: Arc<dyn AbstractNotificationSender + Send + Sync + 'static>,
	peer_id: PeerId,
}

impl DirectedGossipPrototype {
	/// Builds a new [`DirectedGossipPrototype`] containing the given components.
	pub fn new<B, H>(
		service: Arc<NetworkService<B, H>>,
		peer_id: PeerId,
	) -> Self
	where
		B: BlockT + 'static,
		H: ExHashT,
	{
		DirectedGossipPrototype {
			service,
			peer_id,
		}
	}

	/// Turns this [`DirectedGossipPrototype`] into a [`DirectedGossip`] and a future.
	///
	/// See [`DirectGossip::new`] for details.
	pub fn build<M, F>(
		self,
		protocol: ConsensusEngineId,
		queue_size_limit: usize,
		messages_encode: F
	) -> (DirectedGossip<M>, impl Future<Output = ()> + Send + 'static)
	where
		M: Send + 'static,
		F: Fn(M) -> Vec<u8> + Send + 'static,
	{
		let shared = Arc::new(Shared {
			stop_task: atomic::AtomicBool::new(false),
			condvar: Condvar::new(),
			queue_size_limit,
			locked: Mutex::new(SharedLock {
				messages_queue: VecDeque::with_capacity(queue_size_limit),
			}),
		});

		let task = spawn_task(
			self.service,
			self.peer_id,
			protocol,
			shared.clone(),
			messages_encode
		);

		(DirectedGossip { shared }, task)
	}
}

/// Locked queue of messages to the given peer.
///
/// As long as this struct exists, the background task is asleep and the owner of the [`QueueLock`]
/// is in total control of the buffer.
#[must_use]
pub struct QueueLock<'a, M> {
	lock: MutexGuard<'a, SharedLock<M>>,
	condvar: &'a Condvar,
	/// Same as [`Shared::queue_size_limit`].
	queue_size_limit: usize,
}

impl<'a, M: Send + 'static> QueueLock<'a, M> {
	/// Pushes a message to the queue, or discards it if the queue is full.
	pub fn push_or_discard(&mut self, message: M) {
		if self.lock.messages_queue.len() < self.queue_size_limit {
			self.lock.messages_queue.push_back(message);
		}
	}

	/// Pushes a message to the queue. Does not enforce any limit to the size of the queue.
	/// Use this method only if the message is extremely important.
	pub fn push_unbounded(&mut self, message: M) {
		self.lock.messages_queue.push_back(message);
	}

	/// Calls `filter` for each message in the queue, and removes the ones for which `false` is
	/// returned.
	///
	/// > **Note**: The parameter of `filter` is a `&M` and not a `&mut M` (which would be
	/// >           better) because the underlying implementation relies on `VecDeque::retain`.
	pub fn retain(&mut self, filter: impl FnMut(&M) -> bool) {
		self.lock.messages_queue.retain(filter);
	}
}

impl<'a, M> Drop for QueueLock<'a, M> {
	fn drop(&mut self) {
		// We notify the `Condvar` in the destructor in order to be able to push multiple
		// messages and wake up the background task only one afterwards.
		self.condvar.notify_one();
	}
}

#[derive(Debug)]
struct Shared<M> {
	/// Read by the background task after locking `locked`. If true, the task stops.
	stop_task: atomic::AtomicBool,
	locked: Mutex<SharedLock<M>>,
	/// Must be notified every time the content of `locked` changes.
	condvar: Condvar,
	/// Maximum number of elements in `messages_queue`.
	queue_size_limit: usize,
}

#[derive(Debug)]
struct SharedLock<M> {
	/// Queue of messages waiting to be sent out.
	messages_queue: VecDeque<M>,
}

async fn spawn_task<M, F: Fn(M) -> Vec<u8>>(
	service: Arc<dyn AbstractNotificationSender + Send + Sync + 'static>,
	peer_id: PeerId,
	protocol: ConsensusEngineId,
	shared: Arc<Shared<M>>,
	messages_encode: F,
) {
	loop {
		let next_message = 'next_msg: loop {
			let mut locked = shared.locked.lock().await;

			loop {
				if shared.stop_task.load(atomic::Ordering::Acquire) {
					return;
				}

				if let Some(msg) = locked.messages_queue.pop_front() {
					break 'next_msg msg;
				}

				// It is possible that the destructor of `DirectedGossip` sets `stop_task` to
				// true and notifies the `Condvar` after the background task loads `stop_task`
				// and before it calls `Condvar::wait`.
				// See also the corresponding comment in `DirectedGossip::drop`.
				// For this reason, we use `wait_timeout`. In the worst case scenario,
				// `stop_task` will always be checked again after the timeout is reached.
				locked = shared.condvar.wait_timeout(locked, Duration::from_secs(10)).await.0;
			}
		};

		// Starting from below, we try to send the message. If an error happens when sending,
		// the only sane option we have is to silently discard the message.
		let sender = match service.notification_sender(peer_id.clone(), protocol) {
			Ok(s) => s,
			Err(_) => continue,
		};

		let ready = match sender.ready().await {
			Ok(r) => r,
			Err(_) => continue,
		};

		let _ = ready.send(messages_encode(next_message));
	}
}

/// Abstraction around `NetworkService` that permits removing the `B` and `H` parameters.
trait AbstractNotificationSender {
	fn notification_sender(
		&self,
		target: PeerId,
		engine_id: ConsensusEngineId,
	) -> Result<NotificationSender, NotificationSenderError>;
}

impl<B: BlockT, H: ExHashT> AbstractNotificationSender for NetworkService<B, H> {
	fn notification_sender(
		&self,
		target: PeerId,
		engine_id: ConsensusEngineId,
	) -> Result<NotificationSender, NotificationSenderError> {
		NetworkService::notification_sender(self, target, engine_id)
	}
}
