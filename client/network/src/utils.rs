// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use futures::{ready, stream::unfold, FutureExt, Stream, StreamExt};
use futures_timer::Delay;
use linked_hash_set::LinkedHashSet;
use std::{hash::Hash, num::NonZeroUsize, task::Poll, time::Duration};
use tokio::sync::watch;
use tokio_stream::wrappers::WatchStream;

/// Creates a stream that returns a new value every `duration`.
pub fn interval(duration: Duration) -> impl Stream<Item = ()> + Unpin {
	unfold((), move |_| Delay::new(duration).map(|_| Some(((), ())))).map(drop)
}

/// Wrapper around `LinkedHashSet` with bounded growth.
///
/// In the limit, for each element inserted the oldest existing element will be removed.
#[derive(Debug, Clone)]
pub struct LruHashSet<T: Hash + Eq> {
	set: LinkedHashSet<T>,
	limit: NonZeroUsize,
}

impl<T: Hash + Eq> LruHashSet<T> {
	/// Create a new `LruHashSet` with the given (exclusive) limit.
	pub fn new(limit: NonZeroUsize) -> Self {
		Self { set: LinkedHashSet::new(), limit }
	}

	/// Insert element into the set.
	///
	/// Returns `true` if this is a new element to the set, `false` otherwise.
	/// Maintains the limit of the set by removing the oldest entry if necessary.
	/// Inserting the same element will update its LRU position.
	pub fn insert(&mut self, e: T) -> bool {
		if self.set.insert(e) {
			if self.set.len() == usize::from(self.limit) {
				self.set.pop_front(); // remove oldest entry
			}
			return true
		}
		false
	}
}

/// A clone-able stream that yields [`T`].
/// Every instance of the stream will recieve the same data.
/// The stream is implemented on top of a spmc channel
/// see [`tokio::sync::watch::Receiver`]
pub struct MajorSyncStream<T: Clone + Sync + Send + 'static> {
	consumer: watch::Receiver<T>,
	inner: WatchStream<T>,
}

impl<T: Clone + Sync + Send + 'static> Clone for MajorSyncStream<T> {
	fn clone(&self) -> Self {
		let consumer = self.consumer.clone();
		let inner = WatchStream::new(consumer.clone());
		Self { consumer, inner }
	}
}

impl<T: Clone + Sync + Send + 'static> MajorSyncStream<T> {
	pub fn new(init: T) -> (watch::Sender<T>, Self) {
		let (tx, rx) = watch::channel(init);
		let consumer = rx.clone();
		let inner = WatchStream::new(consumer.clone());
		(tx, Self { consumer, inner })
	}
}

impl<T: Clone + Sync + Send + 'static> Stream for MajorSyncStream<T> {
	type Item = T;

	fn poll_next(
		mut self: std::pin::Pin<&mut Self>,
		cx: &mut std::task::Context<'_>,
	) -> std::task::Poll<Option<Self::Item>> {
		match ready!(self.inner.poll_next_unpin(cx)) {
			Some(item) => Poll::Ready(Some(item)),
			_ => Poll::Ready(None),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn maintains_limit() {
		let three = NonZeroUsize::new(3).unwrap();
		let mut set = LruHashSet::<u8>::new(three);

		// First element.
		assert!(set.insert(1));
		assert_eq!(vec![&1], set.set.iter().collect::<Vec<_>>());

		// Second element.
		assert!(set.insert(2));
		assert_eq!(vec![&1, &2], set.set.iter().collect::<Vec<_>>());

		// Inserting the same element updates its LRU position.
		assert!(!set.insert(1));
		assert_eq!(vec![&2, &1], set.set.iter().collect::<Vec<_>>());

		// We reached the limit. The next element forces the oldest one out.
		assert!(set.insert(3));
		assert_eq!(vec![&1, &3], set.set.iter().collect::<Vec<_>>());
	}
}
