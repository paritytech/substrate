// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Code to meter unbounded channels.

use crate::metrics::UNBOUNDED_CHANNELS_COUNTER;
use async_channel::{Receiver, Sender, TryRecvError, TrySendError};
use futures::{
	stream::{FusedStream, Stream},
	task::{Context, Poll},
};
use log::error;
use sp_arithmetic::traits::SaturatedConversion;
use std::{
	backtrace::Backtrace,
	pin::Pin,
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc,
	},
};

/// Wrapper Type around [`async_channel::Sender`] that increases the global
/// measure when a message is added.
#[derive(Debug)]
pub struct TracingUnboundedSender<T> {
	inner: Sender<T>,
	name: &'static str,
	queue_size_warning: usize,
	warning_fired: Arc<AtomicBool>,
	creation_backtrace: Arc<Backtrace>,
}

// Strangely, deriving `Clone` requires that `T` is also `Clone`.
impl<T> Clone for TracingUnboundedSender<T> {
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.clone(),
			name: self.name,
			queue_size_warning: self.queue_size_warning,
			warning_fired: self.warning_fired.clone(),
			creation_backtrace: self.creation_backtrace.clone(),
		}
	}
}

/// Wrapper Type around [`async_channel::Receiver`] that decreases the global
/// measure when a message is polled.
#[derive(Debug)]
pub struct TracingUnboundedReceiver<T> {
	inner: Receiver<T>,
	name: &'static str,
}

/// Wrapper around [`async_channel::unbounded`] that tracks the in- and outflow via
/// `UNBOUNDED_CHANNELS_COUNTER` and warns if the message queue grows
/// above the warning threshold.
pub fn tracing_unbounded<T>(
	name: &'static str,
	queue_size_warning: usize,
) -> (TracingUnboundedSender<T>, TracingUnboundedReceiver<T>) {
	let (s, r) = async_channel::unbounded();
	let sender = TracingUnboundedSender {
		inner: s,
		name,
		queue_size_warning,
		warning_fired: Arc::new(AtomicBool::new(false)),
		creation_backtrace: Arc::new(Backtrace::force_capture()),
	};
	let receiver = TracingUnboundedReceiver { inner: r, name };
	(sender, receiver)
}

impl<T> TracingUnboundedSender<T> {
	/// Proxy function to [`async_channel::Sender`].
	pub fn is_closed(&self) -> bool {
		self.inner.is_closed()
	}

	/// Proxy function to [`async_channel::Sender`].
	pub fn close(&self) -> bool {
		self.inner.close()
	}

	/// Proxy function to `async_channel::Sender::try_send`.
	pub fn unbounded_send(&self, msg: T) -> Result<(), TrySendError<T>> {
		self.inner.try_send(msg).map(|s| {
			UNBOUNDED_CHANNELS_COUNTER.with_label_values(&[self.name, "send"]).inc();

			if self.inner.len() >= self.queue_size_warning &&
				self.warning_fired
					.compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
					.is_ok()
			{
				// `warning_fired` and `len()` are not synchronized, so it's possible
				// that the warning is fired few times before the `warning_fired` is seen
				// by all threads. This seems better than introducing a mutex guarding them.
				error!(
					"The number of unprocessed messages in channel `{}` exceeded {}.\n\
						The channel was created at:\n{}\n
						Last message was sent from:\n{}",
					self.name,
					self.queue_size_warning,
					self.creation_backtrace,
					Backtrace::force_capture(),
				);
			}

			s
		})
	}
}

impl<T> TracingUnboundedReceiver<T> {
	fn consume(&mut self) {
		// the number of messages about to be dropped
		let count = self.inner.len();
		// discount the messages
		if count > 0 {
			UNBOUNDED_CHANNELS_COUNTER
				.with_label_values(&[self.name, "dropped"])
				.inc_by(count.saturated_into());
		}
	}

	/// Proxy function to [`async_channel::Receiver`]
	/// that consumes all messages first and updates the counter.
	pub fn close(&mut self) -> bool {
		self.consume();
		self.inner.close()
	}

	/// Proxy function to [`async_channel::Receiver`]
	/// that discounts the messages taken out.
	pub fn try_recv(&mut self) -> Result<T, TryRecvError> {
		self.inner.try_recv().map(|s| {
			UNBOUNDED_CHANNELS_COUNTER.with_label_values(&[self.name, "received"]).inc();
			s
		})
	}
}

impl<T> Drop for TracingUnboundedReceiver<T> {
	fn drop(&mut self) {
		self.consume();
	}
}

impl<T> Unpin for TracingUnboundedReceiver<T> {}

impl<T> Stream for TracingUnboundedReceiver<T> {
	type Item = T;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<T>> {
		let s = self.get_mut();
		match Pin::new(&mut s.inner).poll_next(cx) {
			Poll::Ready(msg) => {
				if msg.is_some() {
					UNBOUNDED_CHANNELS_COUNTER.with_label_values(&[s.name, "received"]).inc();
				}
				Poll::Ready(msg)
			},
			Poll::Pending => Poll::Pending,
		}
	}
}

impl<T> FusedStream for TracingUnboundedReceiver<T> {
	fn is_terminated(&self) -> bool {
		self.inner.is_terminated()
	}
}
