// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

//! Wrapper around a `Future` that reports statistics about when the `Future` is polled.

use futures::prelude::*;
use prometheus_endpoint::{Counter, Histogram, U64};
use std::{fmt, pin::Pin, task::{Context, Poll}};
use wasm_timer::Instant;

/// Wraps around a `Future`. Report the polling duration to the `Histogram` and when the polling
/// starts to the `Counter`.
pub fn with_poll_durations<T>(
	poll_duration: Histogram,
	poll_start: Counter<U64>,
	inner: T
) -> PrometheusFuture<T> {
	PrometheusFuture {
		inner,
		poll_duration,
		poll_start,
	}
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
		let before = Instant::now();
		let outcome = Future::poll(this.inner, cx);
		let after = Instant::now();

		this.poll_duration.observe((after - before).as_secs_f64());

		outcome
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
