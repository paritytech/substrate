// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use crate::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use futures::{lock::Mutex, prelude::*};
use futures_timer::Delay;
use std::{
	pin::Pin,
	task::{Context, Poll},
	time::Duration,
};

/// Holds a list of `UnboundedSender`s, each associated with a certain time period. Every time the
/// period elapses, we push an element on the sender.
///
/// Senders are removed only when they are closed.
pub struct StatusSinks<T> {
	/// Should only be locked by `next`.
	inner: Mutex<Inner<T>>,
	/// Sending side of `Inner::entries_rx`.
	entries_tx: TracingUnboundedSender<YieldAfter<T>>,
}

struct Inner<T> {
	/// The actual entries of the list.
	entries: stream::FuturesUnordered<YieldAfter<T>>,
	/// Receives new entries and puts them in `entries`.
	entries_rx: TracingUnboundedReceiver<YieldAfter<T>>,
}

struct YieldAfter<T> {
	delay: Delay,
	interval: Duration,
	sender: Option<TracingUnboundedSender<T>>,
}

impl<T> Default for StatusSinks<T> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T> StatusSinks<T> {
	/// Builds a new empty collection.
	pub fn new() -> StatusSinks<T> {
		let (entries_tx, entries_rx) = tracing_unbounded("status-sinks-entries");

		StatusSinks {
			inner: Mutex::new(Inner { entries: stream::FuturesUnordered::new(), entries_rx }),
			entries_tx,
		}
	}

	/// Adds a sender to the collection.
	///
	/// The `interval` is the time period between two pushes on the sender.
	pub fn push(&self, interval: Duration, sender: TracingUnboundedSender<T>) {
		let _ = self.entries_tx.unbounded_send(YieldAfter {
			delay: Delay::new(interval),
			interval,
			sender: Some(sender),
		});
	}

	/// Waits until one of the sinks is ready, then returns an object that can be used to send
	/// an element on said sink.
	///
	/// If the object isn't used to send an element, the slot is skipped.
	pub async fn next(&self) -> ReadySinkEvent<'_, T> {
		// This is only ever locked by `next`, which means that one `next` at a time can run.
		let mut inner = self.inner.lock().await;
		let inner = &mut *inner;

		loop {
			// Future that produces the next ready entry in `entries`, or doesn't produce anything if
			// the list is empty.
			let next_ready_entry = {
				let entries = &mut inner.entries;
				async move {
					if let Some(v) = entries.next().await {
						v
					} else {
						loop {
							futures::pending!()
						}
					}
				}
			};

			futures::select! {
				new_entry = inner.entries_rx.next() => {
					if let Some(new_entry) = new_entry {
						inner.entries.push(new_entry);
					}
				},
				(sender, interval) = next_ready_entry.fuse() => {
					return ReadySinkEvent {
						sinks: self,
						sender: Some(sender),
						interval,
					}
				}
			}
		}
	}
}

/// One of the sinks is ready.
#[must_use]
pub struct ReadySinkEvent<'a, T> {
	sinks: &'a StatusSinks<T>,
	sender: Option<TracingUnboundedSender<T>>,
	interval: Duration,
}

impl<'a, T> ReadySinkEvent<'a, T> {
	/// Sends an element on the sender.
	pub fn send(mut self, element: T) {
		if let Some(sender) = self.sender.take() {
			if sender.unbounded_send(element).is_ok() {
				let _ = self.sinks.entries_tx.unbounded_send(YieldAfter {
					// Note that since there's a small delay between the moment a task is
					// woken up and the moment it is polled, the period is actually not
					// `interval` but `interval + <delay>`. We ignore this problem in
					// practice.
					delay: Delay::new(self.interval),
					interval: self.interval,
					sender: Some(sender),
				});
			}
		}
	}
}

impl<'a, T> Drop for ReadySinkEvent<'a, T> {
	fn drop(&mut self) {
		if let Some(sender) = self.sender.take() {
			if sender.is_closed() {
				return
			}

			let _ = self.sinks.entries_tx.unbounded_send(YieldAfter {
				delay: Delay::new(self.interval),
				interval: self.interval,
				sender: Some(sender),
			});
		}
	}
}

impl<T> futures::Future for YieldAfter<T> {
	type Output = (TracingUnboundedSender<T>, Duration);

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = Pin::into_inner(self);

		match Pin::new(&mut this.delay).poll(cx) {
			Poll::Pending => Poll::Pending,
			Poll::Ready(()) => {
				let sender = this
					.sender
					.take()
					.expect("sender is always Some unless the future is finished; qed");
				Poll::Ready((sender, this.interval))
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::StatusSinks;
	use crate::mpsc::tracing_unbounded;
	use futures::prelude::*;
	use std::time::Duration;

	#[test]
	fn works() {
		// We're not testing that the `StatusSink` properly enforces an order in the intervals, as
		// this easily causes test failures on busy CPUs.

		let status_sinks = StatusSinks::new();

		let (tx, rx) = tracing_unbounded("test");
		status_sinks.push(Duration::from_millis(100), tx);

		let mut val_order = 5;

		futures::executor::block_on(futures::future::select(
			Box::pin(async move {
				loop {
					let ev = status_sinks.next().await;
					val_order += 1;
					ev.send(val_order);
				}
			}),
			Box::pin(async {
				let items: Vec<i32> = rx.take(3).collect().await;
				assert_eq!(items, [6, 7, 8]);
			}),
		));
	}
}
