// Copyright 2019 Parity Technologies (UK) Ltd.
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

use futures::prelude::*;
use futures::sync::mpsc;
use futures::stream::futures_unordered::FuturesUnordered;
use std::time::{Duration, Instant};
use tokio_timer::Delay;

/// Holds a list of `UnboundedSender`s, each associated with a certain time period. Every time the
/// period elapses, we push an element on the sender.
///
/// Senders are removed only when they are closed.
pub struct StatusSinks<T> {
	entries: FuturesUnordered<YieldAfter<T>>,
}

struct YieldAfter<T> {
	delay: tokio_timer::Delay,
	interval: Duration,
	sender: Option<mpsc::UnboundedSender<T>>,
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
	pub fn push(&mut self, interval: Duration, sender: mpsc::UnboundedSender<T>) {
		self.entries.push(YieldAfter {
			delay: Delay::new(Instant::now() + interval),
			interval,
			sender: Some(sender),
		})
	}

	/// Processes all the senders. If any sender is ready, calls the `status_grab` function and
	/// pushes what it returns to the sender.
	///
	/// This function doesn't return anything, but it should be treated as if it implicitly
	/// returns `Ok(Async::NotReady)`. In particular, it should be called again when the task
	/// is waken up.
	///
	/// # Panic
	///
	/// Panics if not called within the context of a task.
	pub fn poll(&mut self, mut status_grab: impl FnMut() -> T) {
		loop {
			match self.entries.poll() {
				Ok(Async::Ready(Some((sender, interval)))) => {
					let status = status_grab();
					if sender.unbounded_send(status).is_ok() {
						self.entries.push(YieldAfter {
							// Note that since there's a small delay between the moment a task is
							// waken up and the moment it is polled, the period is actually not
							// `interval` but `interval + <delay>`. We ignore this problem in
							// practice.
							delay: Delay::new(Instant::now() + interval),
							interval,
							sender: Some(sender),
						});
					}
				}
				Err(()) |
				Ok(Async::Ready(None)) |
				Ok(Async::NotReady) => break,
			}
		}
	}
}

impl<T> Future for YieldAfter<T> {
	type Item = (mpsc::UnboundedSender<T>, Duration);
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		match self.delay.poll() {
			Ok(Async::NotReady) => Ok(Async::NotReady),
			Ok(Async::Ready(())) => {
				let sender = self.sender.take()
					.expect("sender is always Some unless the future is finished; qed");
				Ok(Async::Ready((sender, self.interval)))
			},
			Err(_) => Err(()),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::StatusSinks;
	use futures::prelude::*;
	use futures::sync::mpsc;
	use std::time::Duration;

	#[test]
	fn works() {
		// We're not testing that the `StatusSink` properly enforces an order in the intervals, as
		// this easily causes test failures on busy CPUs.

		let mut status_sinks = StatusSinks::new();

		let (tx, rx) = mpsc::unbounded();
		status_sinks.push(Duration::from_millis(100), tx);

		let mut runtime = tokio::runtime::Runtime::new().unwrap();

		let mut val_order = 5;
		runtime.spawn(futures::future::poll_fn(move || {
			status_sinks.poll(|| { val_order += 1; val_order });
			Ok(Async::NotReady)
		}));

		let done = rx
			.into_future()
			.and_then(|(item, rest)| {
				assert_eq!(item, Some(6));
				rest.into_future()
			})
			.and_then(|(item, rest)| {
				assert_eq!(item, Some(7));
				rest.into_future()
			})
			.map(|(item, _)| {
				assert_eq!(item, Some(8));
			});

		runtime.block_on(done).unwrap();
	}
}
