// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use jsonrpc_core::{Middleware as RequestMiddleware, Metadata, Request, Response, FutureResponse, FutureOutput};
use prometheus_endpoint::{Registry, Counter, PrometheusError, register, U64};

use futures::{future::Either, Future};
use log::error;

struct RpcMetrics {
	rpc_calls: Counter<U64>,
}

impl RpcMetrics {
	fn register(r: &Registry, transport_prefix: &str) -> Result<Self, PrometheusError> {
		let collector_name = format!("{}_rpc_calls_total", transport_prefix);
		let collector_descr = format!("Number of rpc calls received over {}", transport_prefix);
		Ok(RpcMetrics {
			rpc_calls: register(Counter::new(
				collector_name,
				collector_descr,
			)?, r)?,
		})
	}
}

/// Middleware for RPC calls
pub struct RpcMiddleware {
	metrics: Option<RpcMetrics>,
}

impl RpcMiddleware {
	/// Create an instance of middleware
	/// transport_prefix must be uniq per handler in order to register Prometheus collector properly
	pub fn new(metrics_registry: Option<&Registry>, transport_prefix: &str) -> Self {
		RpcMiddleware {
			metrics: metrics_registry.and_then(|r| {
				let metrics = RpcMetrics::register(r, transport_prefix);
				if let Err(ref e) = metrics {
					error!("Cannot register metrics for middleware: {:?}", e);
				}
				metrics.ok()
			})
		}
	}
}

impl<M: Metadata> RequestMiddleware<M> for RpcMiddleware {
	type Future = FutureResponse;
	type CallFuture = FutureOutput;

	fn on_request<F, X>(&self, request: Request, meta: M, next: F) -> Either<FutureResponse, X>
	where
		F: Fn(Request, M) -> X + Send + Sync,
		X: Future<Item = Option<Response>, Error = ()> + Send + 'static,
	{
		if let Some(ref metrics) = self.metrics {
			metrics.rpc_calls.inc();
		}

		Either::B(next(request, meta))
	}
}