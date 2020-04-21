// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use futures::{Stream, stream::futures_unordered::FuturesUnordered};
use std::time::Duration;
use std::pin::Pin;
use std::task::{Poll, Context};
use futures_timer::Delay;
use sp_utils::mpsc::TracingUnboundedSender;

/// Holds a list of `UnboundedSender`s, each associated with a certain time period. Every time the
/// period elapses, we push an element on the sender.
///
/// Senders are removed only when they are closed.
pub struct StatusSinks<T> {
	entries: FuturesUnordered<YieldAfter<T>>,
}

struct YieldAfter<T> {
	delay: Delay,
	interval: Duration,
	sender: Option<TracingUnboundedSender<T>>,
}

impl<T> StatusSinks<T> {
	/// Builds a new empty collection.
	pub fn new() -> StatusSinks<T> {
		StatusSinks {
			entries: FuturesUnordered::new(),
		}
	}

	/// Adds a sender to the collection.
	///
	/// The `interval` is the time period between two pushes on the sender.
	pub fn push(&mut self, interval: Duration, sender: TracingUnboundedSender<T>) {
		self.entries.push(YieldAfter {
			delay: Delay::new(interval),
			interval,
			sender: Some(sender),
		})
	}

	/// Processes all the senders. If any sender is ready, calls the `status_grab` function and
	/// pushes what it returns to the sender.
	///
	/// This function doesn't return anything, but it should be treated as if it implicitly
	/// returns `Poll::Pending`. In particular, it should be called again when the task
	/// is waken up.
	///
	/// # Panic
	///
	/// Panics if not called within the context of a task.
	pub fn poll(&mut self, cx: &mut Context, mut status_grab: impl FnMut() -> T) {
		loop {
			match Pin::new(&mut self.entries).poll_next(cx) {
				Poll::Ready(Some((sender, interval))) => {
					let status = status_grab();
					if sender.unbounded_send(status).is_ok() {
						self.entries.push(YieldAfter {
							// Note that since there's a small delay between the moment a task is
							// waken up and the moment it is polled, the period is actually not
							// `interval` but `interval + <delay>`. We ignore this problem in
							// practice.
							delay: Delay::new(interval),
							interval,
							sender: Some(sender),
						});
					}
				}
				Poll::Ready(None) |
				Poll::Pending => break,
			}
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
				let sender = this.sender.take()
					.expect("sender is always Some unless the future is finished; qed");
				Poll::Ready((sender, this.interval))
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::StatusSinks;
	use futures::prelude::*;
	use futures::channel::mpsc;
	use std::time::Duration;
	use std::task::Poll;

	#[test]
	fn works() {
		// We're not testing that the `StatusSink` properly enforces an order in the intervals, as
		// this easily causes test failures on busy CPUs.

		let mut status_sinks = StatusSinks::new();

		let (tx, rx) = mpsc::unbounded();
		status_sinks.push(Duration::from_millis(100), tx);

		let mut val_order = 5;

		futures::executor::block_on(futures::future::select(
			futures::future::poll_fn(move |cx| {
				status_sinks.poll(cx, || { val_order += 1; val_order });
				Poll::<()>::Pending
			}),
			Box::pin(async {
				let items: Vec<i32> = rx.take(3).collect().await;
				assert_eq!(items, [6, 7, 8]);
			})
		));
	}
}
