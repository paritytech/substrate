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
	FutureOutput, FutureResponse, Metadata, Middleware as RequestMiddleware, Request, Response,
};
use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};

use futures::{future::Either, Future};

/// Metrics for RPC middleware
#[derive(Debug, Clone)]
pub struct RpcMetrics {
	rpc_calls: Option<CounterVec<U64>>,
}

impl RpcMetrics {
	/// Create an instance of metrics
	pub fn new(metrics_registry: Option<&Registry>) -> Result<Self, PrometheusError> {
		Ok(Self {
			rpc_calls: metrics_registry
				.map(|r| {
					register(
						CounterVec::new(
							Opts::new("rpc_calls_total", "Number of rpc calls received"),
							&["protocol"],
						)?,
						r,
					)
				})
				.transpose()?,
		})
	}
}

/// Middleware for RPC calls
pub struct RpcMiddleware {
	metrics: RpcMetrics,
	transport_label: String,
}

impl RpcMiddleware {
	/// Create an instance of middleware.
	///
	/// - `metrics`: Will be used to report statistics.
	/// - `transport_label`: The label that is used when reporting the statistics.
	pub fn new(metrics: RpcMetrics, transport_label: &str) -> Self {
		RpcMiddleware { metrics, transport_label: String::from(transport_label) }
	}
}

impl<M: Metadata> RequestMiddleware<M> for RpcMiddleware {
	type Future = FutureResponse;
	type CallFuture = FutureOutput;

	fn on_request<F, X>(&self, request: Request, meta: M, next: F) -> Either<FutureResponse, X>
	where
		F: Fn(Request, M) -> X + Send + Sync,
		X: Future<Output = Option<Response>> + Send + 'static,
	{
		if let Some(ref rpc_calls) = self.metrics.rpc_calls {
			rpc_calls.with_label_values(&[self.transport_label.as_str()]).inc();
		}

		Either::Right(next(request, meta))
	}
}
