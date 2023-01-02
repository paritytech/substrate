// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Features to meter unbounded channels

#[cfg(not(feature = "metered"))]
mod inner {
	// just aliased, non performance implications
	use futures::channel::mpsc::{self, UnboundedReceiver, UnboundedSender};
	pub type TracingUnboundedSender<T> = UnboundedSender<T>;
	pub type TracingUnboundedReceiver<T> = UnboundedReceiver<T>;

	/// Alias `mpsc::unbounded`
	pub fn tracing_unbounded<T>(
		_key: &'static str,
	) -> (TracingUnboundedSender<T>, TracingUnboundedReceiver<T>) {
		mpsc::unbounded()
	}
}

#[cfg(feature = "metered")]
mod inner {
	// tracing implementation
	use crate::metrics::UNBOUNDED_CHANNELS_COUNTER;
	use backtrace::Backtrace;
	use futures::{
		channel::mpsc::{
			self, SendError, TryRecvError, TrySendError, UnboundedReceiver, UnboundedSender,
		},
		sink::Sink,
		stream::{FusedStream, Stream},
		task::{Context, Poll},
	};
	use log::error;
	use std::{
		pin::Pin,
		sync::{
			atomic::{AtomicBool, AtomicI64, Ordering},
			Arc,
		},
	};

	/// Wrapper Type around `UnboundedSender` that increases the global
	/// measure when a message is added
	#[derive(Debug)]
	pub struct TracingUnboundedSender<T> {
		inner: UnboundedSender<T>,
		name: &'static str,
		// To not bother with ordering and possible underflow errors of the unsigned counter
		// we just use `i64` and `Ordering::Relaxed`, and perceive `queue_size` as approximate.
		// It can turn < 0 though.
		queue_size: Arc<AtomicI64>,
		queue_size_warning: i64,
		warning_fired: Arc<AtomicBool>,
		creation_backtrace: Arc<Backtrace>,
	}

	// Strangely, deriving `Clone` requires that `T` is also `Clone`.
	impl<T> Clone for TracingUnboundedSender<T> {
		fn clone(&self) -> Self {
			Self {
				inner: self.inner.clone(),
				name: self.name,
				queue_size: self.queue_size.clone(),
				queue_size_warning: self.queue_size_warning,
				warning_fired: self.warning_fired.clone(),
				creation_backtrace: self.creation_backtrace.clone(),
			}
		}
	}

	/// Wrapper Type around `UnboundedReceiver` that decreases the global
	/// measure when a message is polled
	#[derive(Debug)]
	pub struct TracingUnboundedReceiver<T> {
		inner: UnboundedReceiver<T>,
		name: &'static str,
		queue_size: Arc<AtomicI64>,
	}

	/// Wrapper around `mpsc::unbounded` that tracks the in- and outflow via
	/// `UNBOUNDED_CHANNELS_COUNTER` and warns if the message queue grows
	/// above the warning threshold.
	pub fn tracing_unbounded<T>(
		name: &'static str,
		queue_size_warning: i64,
	) -> (TracingUnboundedSender<T>, TracingUnboundedReceiver<T>) {
		let (s, r) = mpsc::unbounded();
		let queue_size = Arc::new(AtomicI64::new(0));
		let sender = TracingUnboundedSender {
			inner: s,
			name,
			queue_size: queue_size.clone(),
			queue_size_warning,
			warning_fired: Arc::new(AtomicBool::new(false)),
			creation_backtrace: Arc::new(Backtrace::new_unresolved()),
		};
		let receiver = TracingUnboundedReceiver { inner: r, name, queue_size };
		(sender, receiver)
	}

	impl<T> TracingUnboundedSender<T> {
		/// Proxy function to mpsc::UnboundedSender
		pub fn poll_ready(&self, ctx: &mut Context) -> Poll<Result<(), SendError>> {
			self.inner.poll_ready(ctx)
		}

		/// Proxy function to mpsc::UnboundedSender
		pub fn is_closed(&self) -> bool {
			self.inner.is_closed()
		}

		/// Proxy function to mpsc::UnboundedSender
		pub fn close_channel(&self) {
			self.inner.close_channel()
		}

		/// Proxy function to mpsc::UnboundedSender
		pub fn disconnect(&mut self) {
			self.inner.disconnect()
		}

		pub fn start_send(&mut self, msg: T) -> Result<(), SendError> {
			// The underlying implementation of [`UnboundedSender::start_send`] is the same as
			// [`UnboundedSender::unbounded_send`], so we just reuse the message counting and
			// error reporting code from `unbounded_send`.
			self.unbounded_send(msg).map_err(TrySendError::into_send_error)
		}

		/// Proxy function to mpsc::UnboundedSender
		pub fn unbounded_send(&self, msg: T) -> Result<(), TrySendError<T>> {
			self.inner.unbounded_send(msg).map(|s| {
				UNBOUNDED_CHANNELS_COUNTER.with_label_values(&[self.name, "send"]).inc();

				let queue_size = self.queue_size.fetch_add(1, Ordering::Relaxed);
				if queue_size == self.queue_size_warning &&
					self.warning_fired
						.compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
						.is_ok()
				{
					// `warning_fired` and `queue_size` are not synchronized, so it's possible
					// that the warning is fired few times before the `warning_fired` is seen
					// by all threads. This seems better than introducing a mutex guarding them.
					let mut backtrace = (*self.creation_backtrace).clone();
					backtrace.resolve();
					error!(
						"The number of unprocessed messages in channel `{}` reached {}.\n\
						 The channel was created at:\n{:?}",
						self.name, self.queue_size_warning, backtrace,
					);
				}

				s
			})
		}

		/// Proxy function to mpsc::UnboundedSender
		pub fn same_receiver(&self, other: &UnboundedSender<T>) -> bool {
			self.inner.same_receiver(other)
		}
	}

	impl<T> TracingUnboundedReceiver<T> {
		fn consume(&mut self) {
			// consume all items, make sure to reflect the updated count
			let mut count = 0;
			loop {
				if self.inner.is_terminated() {
					break
				}

				match self.try_next() {
					Ok(Some(..)) => count += 1,
					_ => break,
				}
			}
			// and discount the messages
			if count > 0 {
				UNBOUNDED_CHANNELS_COUNTER
					.with_label_values(&[self.name, "dropped"])
					.inc_by(count);
			}
		}

		/// Proxy function to mpsc::UnboundedReceiver
		/// that consumes all messages first and updates the counter
		pub fn close(&mut self) {
			self.consume();
			self.inner.close()
		}

		/// Proxy function to mpsc::UnboundedReceiver
		/// that discounts the messages taken out
		pub fn try_next(&mut self) -> Result<Option<T>, TryRecvError> {
			self.inner.try_next().map(|s| {
				if s.is_some() {
					let _ = self.queue_size.fetch_sub(1, Ordering::Relaxed);
					UNBOUNDED_CHANNELS_COUNTER.with_label_values(&[self.name, "received"]).inc();
				}
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
						let _ = s.queue_size.fetch_sub(1, Ordering::Relaxed);
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

	impl<T> Sink<T> for TracingUnboundedSender<T> {
		type Error = SendError;

		fn poll_ready(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
			TracingUnboundedSender::poll_ready(&*self, cx)
		}

		fn start_send(mut self: Pin<&mut Self>, msg: T) -> Result<(), Self::Error> {
			TracingUnboundedSender::start_send(&mut *self, msg)
		}

		fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
			Poll::Ready(Ok(()))
		}

		fn poll_close(
			mut self: Pin<&mut Self>,
			_: &mut Context<'_>,
		) -> Poll<Result<(), Self::Error>> {
			self.disconnect();
			Poll::Ready(Ok(()))
		}
	}

	impl<T> Sink<T> for &TracingUnboundedSender<T> {
		type Error = SendError;

		fn poll_ready(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
			TracingUnboundedSender::poll_ready(*self, cx)
		}

		fn start_send(self: Pin<&mut Self>, msg: T) -> Result<(), Self::Error> {
			self.unbounded_send(msg).map_err(TrySendError::into_send_error)
		}

		fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
			Poll::Ready(Ok(()))
		}

		fn poll_close(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
			// The difference with `TracingUnboundedSender` is intentional. The underlying
			// implementation differs for `UnboundedSender<T>` and `&UnboundedSender<T>`:
			// the latter closes the channel completely with `close_channel()`, while the former
			// only closes this specific sender with `disconnect()`.
			self.close_channel();
			Poll::Ready(Ok(()))
		}
	}
}

pub use inner::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
