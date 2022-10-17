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
use prometheus_endpoint::{Counter, Histogram, U64};
use std::{
	fmt,
	pin::Pin,
	task::{Context, Poll},
};

/// Wraps around a `Future`. Report the polling duration to the `Histogram` and when the polling
/// starts to the `Counter`.
pub fn with_poll_durations<T>(
	poll_duration: Histogram,
	poll_start: Counter<U64>,
	inner: T,
) -> PrometheusFuture<T> {
	PrometheusFuture { inner, poll_duration, poll_start }
}

/// Wraps around `Future` and adds diagnostics to it.
#[pin_project::pin_project]
#[derive(Clone)]
pub struct PrometheusFuture<T> {
	/// The inner future doing the actual work.
	#[pin]
	inner: T,
	poll_duration: Histogram,
	poll_start: Counter<U64>,
}

impl<T> Future for PrometheusFuture<T>
where
	T: Future,
{
	type Output = T::Output;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = self.project();

		this.poll_start.inc();
		let _timer = this.poll_duration.start_timer();
		Future::poll(this.inner, cx)

		// `_timer` is dropped here and will observe the duration
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
