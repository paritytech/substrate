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

use futures::{future::FusedFuture, FutureExt};
use futures_timer::Delay;
use std::{
	future::Future,
	pin::Pin,
	task::{Context, Poll, Waker},
	time::Duration,
};

enum Inner {
	Infinite {
		/// Waker from the most recent `poll` call. If `None`, either `poll` has not been called
		/// yet, we returned `Poll::Ready` from the last call, or the waker is attached to `delay`.
		waker: Option<Waker>,
		delay: Option<Delay>,
	},
	Finite(Delay),
}

/// Like [`Delay`] but the duration can be infinite (in which case the future will never fire).
/// Unlike [`Delay`], implements [`FusedFuture`], with [`is_terminated`](Self::is_terminated)
/// returning `true` when the delay is infinite. As with [`Delay`], once [`poll`](Self::poll)
/// returns [`Poll::Ready`], it will continue to do so until [`reset`](Self::reset) is called.
pub struct MaybeInfDelay(Inner);

impl MaybeInfDelay {
	/// Create a new `MaybeInfDelay` future. If `duration` is [`Some`], the future will fire after
	/// the given duration has elapsed. If `duration` is [`None`], the future will "never" fire
	/// (although see [`reset`](Self::reset)).
	pub fn new(duration: Option<Duration>) -> Self {
		match duration {
			Some(duration) => Self(Inner::Finite(Delay::new(duration))),
			None => Self(Inner::Infinite { waker: None, delay: None }),
		}
	}

	/// Reset the timer. `duration` is handled just like in [`new`](Self::new). Note that while
	/// this is similar to `std::mem::replace(&mut self, MaybeInfDelay::new(duration))`, with
	/// `replace` you would have to manually ensure [`poll`](Self::poll) was called again; with
	/// `reset` this is not necessary.
	pub fn reset(&mut self, duration: Option<Duration>) {
		match duration {
			Some(duration) => match &mut self.0 {
				Inner::Infinite { waker, delay } => {
					let mut delay = match delay.take() {
						Some(mut delay) => {
							delay.reset(duration);
							delay
						},
						None => Delay::new(duration),
					};
					if let Some(waker) = waker.take() {
						let mut cx = Context::from_waker(&waker);
						match delay.poll_unpin(&mut cx) {
							Poll::Pending => (), // Waker attached to delay
							Poll::Ready(_) => waker.wake(),
						}
					}
					self.0 = Inner::Finite(delay);
				},
				Inner::Finite(delay) => delay.reset(duration),
			},
			None =>
				self.0 = match std::mem::replace(
					&mut self.0,
					Inner::Infinite { waker: None, delay: None },
				) {
					Inner::Finite(delay) => Inner::Infinite { waker: None, delay: Some(delay) },
					infinite => infinite,
				},
		}
	}
}

impl Future for MaybeInfDelay {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
		match &mut self.0 {
			Inner::Infinite { waker, .. } => {
				*waker = Some(cx.waker().clone());
				Poll::Pending
			},
			Inner::Finite(delay) => delay.poll_unpin(cx),
		}
	}
}

impl FusedFuture for MaybeInfDelay {
	fn is_terminated(&self) -> bool {
		matches!(self.0, Inner::Infinite { .. })
	}
}
