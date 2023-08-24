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

//! Async channel that receives futures as input, processes them in unordered manner, and
//! yields the results once they are resolved via [`Stream`] interface.

use futures::{stream::FuturesUnordered, Future, Stream, StreamExt};
use sc_utils::mpsc::{
	tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender, TrySendError,
};
use std::{
	pin::Pin,
	task::{Context, Poll},
};

/// Sending side of the futures stream.
pub struct FuturesStreamSender<F> {
	tx: TracingUnboundedSender<F>,
}

/// Receiving side of the futures stream.
pub struct FuturesStreamReceiver<F> {
	rx: TracingUnboundedReceiver<F>,
	rx_terminated: bool,
	futures: FuturesUnordered<F>,
}

pub fn futures_stream<F>(
	name: &'static str,
	queue_size_warning: usize,
) -> (FuturesStreamSender<F>, FuturesStreamReceiver<F>) {
	let (tx, rx) = tracing_unbounded(name, queue_size_warning);

	(
		FuturesStreamSender { tx },
		FuturesStreamReceiver { rx, rx_terminated: false, futures: Default::default() },
	)
}

impl<F> FuturesStreamSender<F> {
	/// Push a futures for processing.
	pub fn push(&self, future: F) -> Result<(), TrySendError<F>> {
		self.tx.unbounded_send(future)
	}
}

impl<F> FuturesStreamReceiver<F> {
	/// The lower bound of the number of futures in the stream. Note that this estimate might be
	/// less than actual number by 1 in case the future was taken from the channel and not yet put
	/// into [`FuturesUnordered`].
	pub fn len_lower_bound(&self) -> usize {
		self.rx.len() + self.futures.len()
	}
}

impl<F: Future> Stream for FuturesStreamReceiver<F> {
	type Item = <F as Future>::Output;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		// Get futures out of `TracingUnboundedReceiver` and push them into `FuturesUnordered`.
		if !self.rx_terminated {
			while let Poll::Ready(item) = self.rx.poll_next_unpin(cx) {
				if let Some(future) = item {
					self.futures.push(future);
				} else {
					self.rx_terminated = true;
					break
				}
			}
		}

		// Poll `FuturesUnordered`.
		match self.futures.poll_next_unpin(cx) {
			Poll::Ready(Some(result)) => Poll::Ready(Some(result)),
			Poll::Ready(None) =>
				if self.rx_terminated {
					Poll::Ready(None)
				} else {
					Poll::Pending
				},
			Poll::Pending => Poll::Pending,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::future::{BoxFuture, FutureExt};

	/// [`Stream`] implementation for [`FuturesStreamReceiver`] relies on the undocumented
	/// feature that [`FuturesUnordered`] can be polled and repeatedly yield
	/// `Poll::Ready(None)` before any futures are added into it.
	#[tokio::test]
	async fn empty_futures_unordered_can_be_polled() {
		let mut unordered = FuturesUnordered::<BoxFuture<()>>::default();

		futures::future::poll_fn(|cx| {
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));

			Poll::Ready(())
		})
		.await;
	}

	/// [`Stream`] implementation for [`FuturesStreamReceiver`] relies on the undocumented
	/// feature that [`FuturesUnordered`] can be polled and repeatedly yield
	/// `Poll::Ready(None)` after all the futures in it have resolved.
	#[tokio::test]
	async fn deplenished_futures_unordered_can_be_polled() {
		let mut unordered = FuturesUnordered::<BoxFuture<()>>::default();

		unordered.push(futures::future::ready(()).boxed());
		assert_eq!(unordered.next().await, Some(()));

		futures::future::poll_fn(|cx| {
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));

			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn empty_futures_stream_yields_pending() {
		let (_tx, mut stream) = futures_stream::<BoxFuture<()>>("test", 100);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn futures_stream_resolves_futures_and_yields_pending() {
		let (tx, mut stream) = futures_stream("test", 100);
		tx.push(futures::future::ready(17)).unwrap();

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Ready(Some(17)));
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn futures_stream_terminates_if_sender_is_dropped() {
		let (tx, mut stream) = futures_stream::<BoxFuture<()>>("test", 100);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;

		drop(tx);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Ready(None));
			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn futures_stream_terminates_after_resolving_all_futures_if_sender_is_dropped() {
		let (tx, mut stream) = futures_stream("test", 100);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;

		tx.push(futures::future::ready(17)).unwrap();
		drop(tx);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Ready(Some(17)));
			assert_eq!(stream.poll_next_unpin(cx), Poll::Ready(None));
			Poll::Ready(())
		})
		.await;
	}

	#[test]
	fn futures_stream_len_is_zero_for_empty_stream() {
		let (_tx, stream) = futures_stream::<BoxFuture<()>>("test", 100);
		assert_eq!(stream.len_lower_bound(), 0);
	}

	#[tokio::test]
	async fn futures_stream_len_counts_and_discounts_resolved_futures() {
		let (tx, mut stream) = futures_stream("test", 100);
		assert_eq!(stream.len_lower_bound(), 0);

		tx.push(futures::future::ready(17)).unwrap();
		assert_eq!(stream.len_lower_bound(), 1);

		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Ready(Some(17)));
			assert_eq!(stream.len_lower_bound(), 0);

			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			assert_eq!(stream.len_lower_bound(), 0);

			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn futures_stream_len_counts_taken_pending_futures() {
		let (tx, mut stream) = futures_stream("test", 100);
		assert_eq!(stream.len_lower_bound(), 0);

		tx.push(futures::future::pending::<()>()).unwrap();

		// The future in the unbounded stream is counted.
		assert_eq!(stream.len_lower_bound(), 1);

		// Poll once to move the future from unbounded stream into [`FuturesUnordered`].
		futures::future::poll_fn(|cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;

		// The future is still counted in [`FuturesUnordered`].
		assert_eq!(stream.len_lower_bound(), 1);
	}
}
