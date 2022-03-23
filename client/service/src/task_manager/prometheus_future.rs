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

//! Wrapper around a `Future` that reports statistics about when the `Future` is polled.

use futures::prelude::*;
use prometheus_endpoint::{prometheus::HistogramTimer, Counter, Histogram, U64};
use std::{
	fmt,
	pin::Pin,
	task::{Context, Poll},
};

/// Wraps around a `Future`. Report the polling duration to the `Histogram` and when the polling
/// starts to the `Counter`.
pub fn with_poll_durations<T>(
	idle_duration: Histogram,
	poll_duration: Histogram,
	poll_start: Counter<U64>,
	inner: T,
) -> PrometheusFuture<T> {
	PrometheusFuture { inner, idle_duration, poll_duration, poll_start, maybe_idle_timer: None }
}

/// Wraps around `Future` and adds diagnostics to it.
#[pin_project::pin_project]
// #[derive(Clone)]
pub struct PrometheusFuture<T> {
	/// The inner future doing the actual work.
	#[pin]
	inner: T,
	idle_duration: Histogram,
	poll_duration: Histogram,
	poll_start: Counter<U64>,
	maybe_idle_timer: Option<HistogramTimer>,
}

impl<T> Future for PrometheusFuture<T>
where
	T: Future,
{
	type Output = T::Output;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = self.project();

		if let Some(idle_timer) = this.maybe_idle_timer.take() {
			// We're about to poll the task - no longer idle, stop timer.
			drop(idle_timer);
		}

		this.poll_start.inc();
		let _timer = this.poll_duration.start_timer();
		let poll_result = Future::poll(this.inner, cx);

		match poll_result {
			Poll::Ready(_) => {
				// We don't start the idle timer because task has just finished.
			},
			Poll::Pending => {
				// The future is now idle, start the idle time measurement.
				*this.maybe_idle_timer = Some(this.idle_duration.start_timer());
			},
		}

		poll_result
		// `_timer` is dropped here and will observe the `poll()` duration
	}
}

impl<T> fmt::Debug for PrometheusFuture<T>
where
	T: fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Debug::fmt(&self.inner, f)
	}
}
