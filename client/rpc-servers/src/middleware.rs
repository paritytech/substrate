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

//! RPC middleware to collect prometheus metrics on RPC calls.

use jsonrpsee::server::logger::{HttpRequest, Logger, MethodKind, Params, TransportProtocol};
use prometheus_endpoint::{
	register, Counter, CounterVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry,
	U64,
};
use std::net::SocketAddr;

/// Histogram time buckets in microseconds.
const HISTOGRAM_BUCKETS: [f64; 11] = [
	5.0,
	25.0,
	100.0,
	500.0,
	1_000.0,
	2_500.0,
	10_000.0,
	25_000.0,
	100_000.0,
	1_000_000.0,
	10_000_000.0,
];

/// Metrics for RPC middleware storing information about the number of requests started/completed,
/// calls started/completed and their timings.
#[derive(Debug, Clone)]
pub struct RpcMetrics {
	/// Number of RPC requests received since the server started.
	requests_started: CounterVec<U64>,
	/// Number of RPC requests completed since the server started.
	requests_finished: CounterVec<U64>,
	/// Histogram over RPC execution times.
	calls_time: HistogramVec,
	/// Number of calls started.
	calls_started: CounterVec<U64>,
	/// Number of calls completed.
	calls_finished: CounterVec<U64>,
	/// Number of Websocket sessions opened.
	ws_sessions_opened: Option<Counter<U64>>,
	/// Number of Websocket sessions closed.
	ws_sessions_closed: Option<Counter<U64>>,
}

impl RpcMetrics {
	/// Create an instance of metrics
	pub fn new(metrics_registry: Option<&Registry>) -> Result<Option<Self>, PrometheusError> {
		if let Some(metrics_registry) = metrics_registry {
			Ok(Some(Self {
				requests_started: register(
					CounterVec::new(
						Opts::new(
							"substrate_rpc_requests_started",
							"Number of RPC requests (not calls) received by the server.",
						),
						&["protocol"],
					)?,
					metrics_registry,
				)?,
				requests_finished: register(
					CounterVec::new(
						Opts::new(
							"substrate_rpc_requests_finished",
							"Number of RPC requests (not calls) processed by the server.",
						),
						&["protocol"],
					)?,
					metrics_registry,
				)?,
				calls_time: register(
					HistogramVec::new(
						HistogramOpts::new(
							"substrate_rpc_calls_time",
							"Total time [μs] of processed RPC calls",
						)
						.buckets(HISTOGRAM_BUCKETS.to_vec()),
						&["protocol", "method"],
					)?,
					metrics_registry,
				)?,
				calls_started: register(
					CounterVec::new(
						Opts::new(
							"substrate_rpc_calls_started",
							"Number of received RPC calls (unique un-batched requests)",
						),
						&["protocol", "method"],
					)?,
					metrics_registry,
				)?,
				calls_finished: register(
					CounterVec::new(
						Opts::new(
							"substrate_rpc_calls_finished",
							"Number of processed RPC calls (unique un-batched requests)",
						),
						&["protocol", "method", "is_error"],
					)?,
					metrics_registry,
				)?,
				ws_sessions_opened: register(
					Counter::new(
						"substrate_rpc_sessions_opened",
						"Number of persistent RPC sessions opened",
					)?,
					metrics_registry,
				)?
				.into(),
				ws_sessions_closed: register(
					Counter::new(
						"substrate_rpc_sessions_closed",
						"Number of persistent RPC sessions closed",
					)?,
					metrics_registry,
				)?
				.into(),
			}))
		} else {
			Ok(None)
		}
	}
}

impl Logger for RpcMetrics {
	type Instant = std::time::Instant;

	fn on_connect(
		&self,
		_remote_addr: SocketAddr,
		_request: &HttpRequest,
		transport: TransportProtocol,
	) {
		if let TransportProtocol::WebSocket = transport {
			self.ws_sessions_opened.as_ref().map(|counter| counter.inc());
		}
	}

	fn on_request(&self, transport: TransportProtocol) -> Self::Instant {
		let transport_label = transport_label_str(transport);
		let now = std::time::Instant::now();
		self.requests_started.with_label_values(&[transport_label]).inc();
		now
	}

	fn on_call(&self, name: &str, params: Params, kind: MethodKind, transport: TransportProtocol) {
		let transport_label = transport_label_str(transport);
		log::trace!(
			target: "rpc_metrics",
			"[{}] on_call name={} params={:?} kind={}",
			transport_label,
			name,
			params,
			kind,
		);
		self.calls_started.with_label_values(&[transport_label, name]).inc();
	}

	fn on_result(
		&self,
		name: &str,
		success: bool,
		started_at: Self::Instant,
		transport: TransportProtocol,
	) {
		let transport_label = transport_label_str(transport);
		let micros = started_at.elapsed().as_micros();
		log::debug!(
			target: "rpc_metrics",
			"[{}] {} call took {} μs",
			transport_label,
			name,
			micros,
		);
		self.calls_time.with_label_values(&[transport_label, name]).observe(micros as _);

		self.calls_finished
			.with_label_values(&[
				transport_label,
				name,
				// the label "is_error", so `success` should be regarded as false
				// and vice-versa to be registrered correctly.
				if success { "false" } else { "true" },
			])
			.inc();
	}

	fn on_response(&self, result: &str, started_at: Self::Instant, transport: TransportProtocol) {
		let transport_label = transport_label_str(transport);
		log::trace!(target: "rpc_metrics", "[{}] on_response started_at={:?}", transport_label, started_at);
		log::trace!(target: "rpc_metrics::extra", "[{}] result={:?}", transport_label, result);
		self.requests_finished.with_label_values(&[transport_label]).inc();
	}

	fn on_disconnect(&self, _remote_addr: SocketAddr, transport: TransportProtocol) {
		if let TransportProtocol::WebSocket = transport {
			self.ws_sessions_closed.as_ref().map(|counter| counter.inc());
		}
	}
}

fn transport_label_str(t: TransportProtocol) -> &'static str {
	match t {
		TransportProtocol::Http => "http",
		TransportProtocol::WebSocket => "ws",
	}
}
