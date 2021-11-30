// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! RPC middlware to collect prometheus metrics on RPC calls.

use jsonrpsee::types::middleware::Middleware;
use prometheus_endpoint::{
	register, CounterVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry, U64,
};

/// Metrics for RPC middleware storing information about the number of requests started/completed,
/// calls started/completed and their timings.
#[derive(Debug, Clone)]
pub struct RpcMetrics {
	requests_started: CounterVec<U64>,
	requests_finished: CounterVec<U64>,
	calls_time: HistogramVec,
	calls_started: CounterVec<U64>,
	calls_finished: CounterVec<U64>,
}

impl RpcMetrics {
	/// Create an instance of metrics
	pub fn new(metrics_registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			requests_started: register(
				CounterVec::new(
					Opts::new(
						"rpc_requests_started",
						"Number of RPC requests (not calls) received by the server.",
					),
					&["protocol"],
				)?,
				metrics_registry,
			)?,
			requests_finished: register(
				CounterVec::new(
					Opts::new(
						"rpc_requests_finished",
						"Number of RPC requests (not calls) processed by the server.",
					),
					&["protocol"],
				)?,
				metrics_registry,
			)?,
			calls_time: register(
				HistogramVec::new(
					HistogramOpts::new("rpc_calls_time", "Total time [μs] of processed RPC calls"),
					&["protocol", "method"],
				)?,
				metrics_registry,
			)?,
			calls_started: register(
				CounterVec::new(
					Opts::new(
						"rpc_calls_started",
						"Number of received RPC calls (unique un-batched requests)",
					),
					&["protocol", "method"],
				)?,
				metrics_registry,
			)?,
			calls_finished: register(
				CounterVec::new(
					Opts::new(
						"rpc_calls_finished",
						"Number of processed RPC calls (unique un-batched requests)",
					),
					&["protocol", "method", "is_error"],
				)?,
				metrics_registry,
			)?,
		})
	}
}

#[derive(Clone)]
/// Middleware for RPC calls
pub struct RpcMiddleware {
	metrics: RpcMetrics,
	transport_label: &'static str,
}

impl RpcMiddleware {
	/// Create a new [`RpcMiddleware`] with the provided [`RpcMetrics`].
	pub fn new(metrics: RpcMetrics, transport_label: &'static str) -> Self {
		Self { metrics, transport_label }
	}
}

impl Middleware for RpcMiddleware {
	type Instant = std::time::Instant;

	fn on_request(&self) -> Self::Instant {
		let now = std::time::Instant::now();
		self.metrics.requests_started.with_label_values(&[self.transport_label]).inc();
		now
	}

	fn on_call(&self, name: &str) {
		log::trace!(target: "rpc_metrics", "[{}] on_call name={}", self.transport_label, name);
		self.metrics
			.calls_started
			.with_label_values(&[self.transport_label, name])
			.inc();
	}

	fn on_result(&self, name: &str, success: bool, started_at: Self::Instant) {
		const TRUE: &str = "true";
		const FALSE: &str = "false";
		let micros = started_at.elapsed().as_micros();
		log::trace!(target: "rpc_metrics", "[{}] on_result name={}, success={}, started_at={:?}; call took {}μs", self.transport_label, name, success, started_at, micros);
		self.metrics
			.calls_time
			.with_label_values(&[self.transport_label, name])
			.observe(micros as _);

		self.metrics
			.calls_finished
			.with_label_values(&[self.transport_label, name, if success { TRUE } else { FALSE }])
			.inc();
	}

	fn on_response(&self, started_at: Self::Instant) {
		log::trace!(target: "rpc_metrics", "[{}] on_response started_at={:?}", self.transport_label, started_at);
		self.metrics.requests_finished.with_label_values(&[self.transport_label]).inc();
	}
}
