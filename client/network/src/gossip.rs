// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
//! different order. See also <https://github.com/paritytech/substrate/issues/6756>.
//! However, if multiple instances of [`QueuedSender`] exist for the same peer and protocol, or
//! if some other code uses the [`NetworkService`] to send notifications to this combination or
//! peer and protocol, then the notifications will be interleaved in an unpredictable way.
//!

use crate::{ExHashT, NetworkService};

use async_std::sync::{Mutex, MutexGuard};
use futures::prelude::*;
use futures::channel::mpsc::{channel, Receiver, Sender};
use libp2p::PeerId;
use sp_runtime::traits::Block as BlockT;
use std::{
	borrow::Cow,
	collections::VecDeque,
	fmt,
	sync::Arc,
};

#[cfg(test)]
mod tests;

/// Notifications sender for a specific combination of network service, peer, and protocol.
pub struct QueuedSender<M> {
	/// Shared between the user-facing [`QueuedSender`] and the background future.
	shared_message_queue: SharedMessageQueue<M>,
	/// Used to notify the background future to check for new messages in the message queue.
	notify_background_future: Sender<()>,
	/// Maximum number of elements in [`QueuedSender::shared_message_queue`].
	queue_size_limit: usize,
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
		protocol: Cow<'static, str>,
		queue_size_limit: usize,
		messages_encode: F
	) -> (Self, impl Future<Output = ()> + Send + 'static)
	where
		M: Send + 'static,
		B: BlockT + 'static,
		H: ExHashT,
		F: Fn(M) -> Vec<u8> + Send + 'static,
	{
		let (notify_background_future, wait_for_sender) = channel(0);

		let shared_message_queue = Arc::new(Mutex::new(
			VecDeque::with_capacity(queue_size_limit),
		));

		let background_future = create_background_future(
			wait_for_sender,
			service,
			peer_id,
			protocol,
			shared_message_queue.clone(),
			messages_encode
		);

		let sender = Self {
			shared_message_queue,
			notify_background_future,
			queue_size_limit,
		};

		(sender, background_future)
	}

	/// Locks the queue of messages towards this peer.
	///
	/// The returned `Future` is expected to be ready quite quickly.
	pub async fn lock_queue<'a>(&'a mut self) -> QueueGuard<'a, M> {
		QueueGuard {
			message_queue: self.shared_message_queue.lock().await,
			queue_size_limit: self.queue_size_limit,
			notify_background_future: &mut self.notify_background_future,
		}
	}

	/// Pushes a message to the queue, or discards it if the queue is full.
	///
	/// The returned `Future` is expected to be ready quite quickly.
	pub async fn queue_or_discard(&mut self, message: M)
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

/// Locked queue of messages to the given peer.
///
/// As long as this struct exists, the background future is asleep and the owner of the
/// [`QueueGuard`] is in total control of the message queue. Messages can only ever be sent out on
/// the network after the [`QueueGuard`] is dropped.
#[must_use]
pub struct QueueGuard<'a, M> {
	message_queue: MutexGuard<'a, MessageQueue<M>>,
	/// Same as [`QueuedSender::queue_size_limit`].
	queue_size_limit: usize,
	notify_background_future: &'a mut Sender<()>,
}

impl<'a, M: Send + 'static> QueueGuard<'a, M> {
	/// Pushes a message to the queue, or discards it if the queue is full.
	///
	/// The message will only start being sent out after the [`QueueGuard`] is dropped.
	pub fn push_or_discard(&mut self, message: M) {
		if self.message_queue.len() < self.queue_size_limit {
			self.message_queue.push_back(message);
		}
	}

	/// Calls `filter` for each message in the queue, and removes the ones for which `false` is
	/// returned.
	///
	/// > **Note**: The parameter of `filter` is a `&M` and not a `&mut M` (which would be
	/// >           better) because the underlying implementation relies on `VecDeque::retain`.
	pub fn retain(&mut self, filter: impl FnMut(&M) -> bool) {
		self.message_queue.retain(filter);
	}
}

impl<'a, M> Drop for QueueGuard<'a, M> {
	fn drop(&mut self) {
		// Notify background future to check for new messages in the message queue.
		let _ = self.notify_background_future.try_send(());
	}
}

type MessageQueue<M> = VecDeque<M>;

/// [`MessageQueue`] shared between [`QueuedSender`] and background future.
type SharedMessageQueue<M> = Arc<Mutex<MessageQueue<M>>>;

async fn create_background_future<B: BlockT, H: ExHashT, M, F: Fn(M) -> Vec<u8>>(
	mut wait_for_sender: Receiver<()>,
	service: Arc<NetworkService<B, H>>,
	peer_id: PeerId,
	protocol: Cow<'static, str>,
	shared_message_queue: SharedMessageQueue<M>,
	messages_encode: F,
) {
	loop {
		if wait_for_sender.next().await.is_none() {
			return
		}

		loop {
			let mut queue_guard = shared_message_queue.lock().await;
			let next_message = match queue_guard.pop_front() {
				Some(msg) => msg,
				None => break,
			};
			drop(queue_guard);

			// Starting from below, we try to send the message. If an error happens when sending,
			// the only sane option we have is to silently discard the message.
			let sender = match service.notification_sender(peer_id.clone(), protocol.clone()) {
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
}
