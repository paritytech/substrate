// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Middleware for RPC requests.

use jsonrpc_core::{
	Middleware as RequestMiddleware, Metadata,
	FutureResponse, FutureOutput
};
use prometheus_endpoint::{GaugeVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry, U64, register};

use futures::{future::Either, Future};

/// Metrics for RPC middleware
#[derive(Debug, Clone)]
pub struct RpcMetrics {
	requests_started: GaugeVec<U64>,
	requests_finished: GaugeVec<U64>,
	calls_time: HistogramVec,
	calls_started: GaugeVec<U64>,
	calls_finished: GaugeVec<U64>
}

impl RpcMetrics {
	/// Create an instance of metrics
	pub fn new(metrics_registry: Option<&Registry>) -> Result<Option<Self>, PrometheusError> {
		if let Some(r) = metrics_registry {
			Ok(Some(Self {
				requests_started: register(
					GaugeVec::new(
						Opts::new(
							"rpc_requests_started",
							"Number of RPC requests (not calls) received by the server."
						),
						&["protocol"],
					)?,
					r,
				)?,
				requests_finished: register(
					GaugeVec::new(
						Opts::new(
							"rpc_requests_finished",
							"Number of RPC requests (not calls) processed by the server."
						),
						&["protocol"],
					)?,
					r,
				)?,
				calls_time: register(
					HistogramVec::new(
						HistogramOpts::new(
							"rpc_calls_time",
							"Total time [ms] of processed RPC calls",
						),
						&["protocol", "method"]
					)?,
					r,
				)?,
				calls_started: register(
					GaugeVec::new(
						Opts::new(
							"rpc_calls_started",
							"Number of received RPC calls (unique un-batched requests)"
						),
						&["protocol", "method"]
					)?,
					r
				)?,
				calls_finished: register(
					GaugeVec::new(
						Opts::new(
							"rpc_calls_finished",
							"Number of processed RPC calls (unique un-batched requests)"
						),
						&["protocol", "method", "is_error"]
					)?,
					r
				)?,
			}))
		} else {
			Ok(None)
		}
	}
}

/// Middleware for RPC calls
pub struct RpcMiddleware {
	metrics: Option<RpcMetrics>,
	transport_label: String,
}

impl RpcMiddleware {
	/// Create an instance of middleware.
	///
	/// - `metrics`: Will be used to report statistics.
	/// - `transport_label`: The label that is used when reporting the statistics.
	pub fn new(metrics: Option<RpcMetrics>, transport_label: &str) -> Self {
		RpcMiddleware {
			metrics,
			transport_label: String::from(transport_label),
		}
	}
}

impl<M: Metadata> RequestMiddleware<M> for RpcMiddleware {
	type Future = FutureResponse;
	type CallFuture = FutureOutput;

	fn on_request<F, X>(&self, request: jsonrpc_core::Request, meta: M, next: F) -> Either<Self::Future, X>
	where
			F: Fn(jsonrpc_core::Request, M) -> X + Send + Sync,
			X: Future<Item = Option<jsonrpc_core::Response>, Error = ()> + Send + 'static,
	{
		let metrics = self.metrics.clone();
		let transport_label = self.transport_label.clone();
		if let Some(ref metrics) = metrics {
			metrics.requests_started.with_label_values(&[transport_label.as_str()]).inc();
		}
		Either::A(
			Box::new(next(request, meta)
				.then(move |r| {
					if let Some(ref metrics) = metrics {
						metrics.requests_finished.with_label_values(&[transport_label.as_str()]).inc();
					}
					r
				}))
		)
	}

	fn on_call<F, X>(&self, call: jsonrpc_core::Call, meta: M, next: F) -> Either<Self::CallFuture, X>
	where
		F: Fn(jsonrpc_core::Call, M) -> X + Send + Sync,
		X: Future<Item = Option<jsonrpc_core::Output>, Error = ()> + Send + 'static,
	{
		#[cfg(not(target_os = "unknown"))]
		let start = std::time::Instant::now();
		let name = call_name(&call).to_owned();
		let metrics = self.metrics.clone();
		let transport_label = self.transport_label.clone();
		log::trace!(target: "rpc_metrics", "[{}] {} call: {:?}", transport_label, name, &call);
		if let Some(ref metrics) = metrics {
			metrics.calls_started.with_label_values(&[
				transport_label.as_str(),
				name.as_str(),
			]).inc();
		}
		Either::A(Box::new(next(call, meta).then(move |r| {
			#[cfg(not(target_os = "unknown"))]
			let millis = start.elapsed().as_millis();
			// seems that std::time is not implemented for browser target
			#[cfg(target_os = "unknown")]
			let millis = 0;
			if let Some(ref metrics) = metrics {
				metrics.calls_time.with_label_values(&[
					transport_label.as_str(),
					name.as_str(),
				]).observe(millis as _);
				metrics.calls_finished.with_label_values(&[
					transport_label.as_str(),
					name.as_str(),
					format!("{}", is_success(&r)).as_str(),
				]).inc();
			}
			log::debug!(target: "rpc_metrics", "[{}] {} call took {} ms", transport_label, name, millis);
			r
		})))
	}
}

fn call_name(call: &jsonrpc_core::Call) -> &str {
	match call {
		jsonrpc_core::Call::Invalid { .. } => "invalid",
		jsonrpc_core::Call::MethodCall(ref call) => &*call.method,
		jsonrpc_core::Call::Notification(ref notification) => &*notification.method,
	}
}

fn is_success(output: &Result<Option<jsonrpc_core::Output>, ()>) -> bool {
	match output {
		Ok(Some(jsonrpc_core::Output::Success(..))) => true,
		_ => false,
	}
}
