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

use futures::{future::FutureExt, ready, stream::Stream};
use futures_timer::Delay;
use std::{
	pin::Pin,
	task::{Context, Poll},
	time::Duration,
};

/// Exponentially increasing interval
///
/// Doubles interval duration on each tick until the configured maximum is reached.
pub struct ExpIncInterval {
	max: Duration,
	next: Duration,
	delay: Delay,
}

impl ExpIncInterval {
	/// Create a new [`ExpIncInterval`].
	pub fn new(start: Duration, max: Duration) -> Self {
		let delay = Delay::new(start);
		Self { max, next: start * 2, delay }
	}

	/// Fast forward the exponentially increasing interval to the configured maximum.
	pub fn set_to_max(&mut self) {
		self.next = self.max;
		self.delay = Delay::new(self.next);
	}
}

impl Stream for ExpIncInterval {
	type Item = ();

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		ready!(self.delay.poll_unpin(cx));
		self.delay = Delay::new(self.next);
		self.next = std::cmp::min(self.max, self.next * 2);

		Poll::Ready(Some(()))
	}
}
