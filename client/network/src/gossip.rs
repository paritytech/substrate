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
//! The [`QueuedSender`] struct provided by this module is built on top of
//! [`NetworkService::notification_sender`] and provides a cleaner way to send notifications.
//!
//! # Behaviour
//!
//! An instance of [`QueuedSender`] is specific to a certain combination of `PeerId` and
//! protocol name. It maintains a buffer of messages waiting to be sent out. The user of this API
//! is able to manipulate that queue, adding or removing obsolete messages.
//!
//! Creating a [`QueuedSender`] also returns a opaque `Future` whose responsibility it to
//! drain that queue and actually send the messages. If the substream with the given combination
//! of peer and protocol is closed, the queue is silently discarded. It is the role of the user
//! to track which peers we are connected to.
//!
//! In normal situations, messages sent through a [`QueuedSender`] will arrive in the same
//! order as they have been sent.
//! It is possible, in the situation of disconnects and reconnects, that messages arrive in a
//! different order. See also https://github.com/paritytech/substrate/issues/6756.
//! However, if multiple instances of [`QueuedSender`] exist for the same peer and protocol, or
//! if some other code uses the [`NetworkService`] to send notifications to this combination or
//! peer and protocol, then the notifications will be interleaved in an unpredictable way.
//!

use crate::{ExHashT, NetworkService};

use async_std::sync::{Condvar, Mutex, MutexGuard};
use futures::prelude::*;
use libp2p::PeerId;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use std::{
	collections::VecDeque,
	fmt,
	sync::{atomic, Arc},
	time::Duration,
};

#[cfg(test)]
mod tests;

/// Notifications sender for a specific combination of network service, peer, and protocol.
pub struct QueuedSender<M> {
	/// Shared between the front and the back task.
	shared: Arc<Shared<M>>,
}

impl<M> QueuedSender<M> {
	/// Returns a new [`QueuedSender`] containing a queue of message for this specific
	/// combination of peer and protocol.
	///
	/// In addition to the [`QueuedSender`], also returns a `Future` whose role is to drive
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
		let shared = Arc::new(Shared {
			stop_task: atomic::AtomicBool::new(false),
			condvar: Condvar::new(),
			queue_size_limit,
			messages_queue: Mutex::new(VecDeque::with_capacity(queue_size_limit)),
		});

		let task = spawn_task(
			service,
			peer_id,
			protocol,
			shared.clone(),
			messages_encode
		);

		(QueuedSender { shared }, task)
	}

	/// Locks the queue of messages towards this peer.
	///
	/// The returned `Future` is expected to be ready quite quickly.
	pub async fn lock_queue<'a>(&'a self) -> QueueGuard<'a, M> {
		QueueGuard {
			messages_queue: self.shared.messages_queue.lock().await,
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

impl<M> fmt::Debug for QueuedSender<M> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("QueuedSender").finish()
	}
}

impl<M> Drop for QueuedSender<M> {
	fn drop(&mut self) {
		// The "clean" way to notify the `Condvar` here is normally to first lock the `Mutex`,
		// then notify the `Condvar` while the `Mutex` is locked. Unfortunately, the `Mutex`
		// being asynchronous, it can't reasonably be locked from within a destructor.
		// See also the corresponding code in the background task.
		self.shared.stop_task.store(true, atomic::Ordering::Release);
		self.shared.condvar.notify_all();
	}
}

/// Locked queue of messages to the given peer.
///
/// As long as this struct exists, the background task is asleep and the owner of the [`QueueGuard`]
/// is in total control of the buffer. Messages can only ever be sent out after the [`QueueGuard`]
/// is dropped.
#[must_use]
pub struct QueueGuard<'a, M> {
	messages_queue: MutexGuard<'a, VecDeque<M>>,
	condvar: &'a Condvar,
	/// Same as [`Shared::queue_size_limit`].
	queue_size_limit: usize,
}

impl<'a, M: Send + 'static> QueueGuard<'a, M> {
	/// Pushes a message to the queue, or discards it if the queue is full.
	///
	/// The message will only start being sent out after the [`QueueGuard`] is dropped.
	pub fn push_or_discard(&mut self, message: M) {
		if self.messages_queue.len() < self.queue_size_limit {
			self.messages_queue.push_back(message);
		}
	}

	/// Calls `filter` for each message in the queue, and removes the ones for which `false` is
	/// returned.
	///
	/// > **Note**: The parameter of `filter` is a `&M` and not a `&mut M` (which would be
	/// >           better) because the underlying implementation relies on `VecDeque::retain`.
	pub fn retain(&mut self, filter: impl FnMut(&M) -> bool) {
		self.messages_queue.retain(filter);
	}
}

impl<'a, M> Drop for QueueGuard<'a, M> {
	fn drop(&mut self) {
		// We notify the `Condvar` in the destructor in order to be able to push multiple
		// messages and wake up the background task only once afterwards.
		self.condvar.notify_one();
	}
}

#[derive(Debug)]
struct Shared<M> {
	/// Read by the background task after locking `locked`. If true, the task stops.
	stop_task: atomic::AtomicBool,
	/// Queue of messages waiting to be sent out.
	messages_queue: Mutex<VecDeque<M>>,
	/// Must be notified every time the content of `locked` changes.
	condvar: Condvar,
	/// Maximum number of elements in `messages_queue`.
	queue_size_limit: usize,
}

async fn spawn_task<B: BlockT, H: ExHashT, M, F: Fn(M) -> Vec<u8>>(
	service: Arc<NetworkService<B, H>>,
	peer_id: PeerId,
	protocol: ConsensusEngineId,
	shared: Arc<Shared<M>>,
	messages_encode: F,
) {
	loop {
		let next_message = 'next_msg: loop {
			let mut queue = shared.messages_queue.lock().await;

			loop {
				if shared.stop_task.load(atomic::Ordering::Acquire) {
					return;
				}

				if let Some(msg) = queue.pop_front() {
					break 'next_msg msg;
				}

				// It is possible that the destructor of `QueuedSender` sets `stop_task` to
				// true and notifies the `Condvar` after the background task loads `stop_task`
				// and before it calls `Condvar::wait`.
				// See also the corresponding comment in `QueuedSender::drop`.
				// For this reason, we use `wait_timeout`. In the worst case scenario,
				// `stop_task` will always be checked again after the timeout is reached.
				queue = shared.condvar.wait_timeout(queue, Duration::from_secs(10)).await.0;
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
