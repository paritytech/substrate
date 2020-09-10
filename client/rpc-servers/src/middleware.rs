// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Middlewares for RPC servers.

use http::{RequestMiddleware as HttpRequestMiddleware, RequestMiddlewareAction as HttpRequestMiddlewareAction};
use hyper::Body;
use prometheus_endpoint::{Registry, Counter, PrometheusError, register, U64};
use ws::{RequestMiddleware as WSRequestMiddleware, MiddlewareAction as WSRequestMiddlewareAction};

struct HTTPMetrics {
	http_rpc_calls: Counter<U64>,
}

impl HTTPMetrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(HTTPMetrics {
			http_rpc_calls: register(Counter::new(
				"rpc_http_calls",
				"Number of rpc calls received through http interface",
			)?, r)?,
		})
	}
}

/// Middleware for RPC calls over HTTP
pub struct HttpRpcMiddleware {
	metrics: Option<HTTPMetrics>,
}

impl HttpRpcMiddleware {
	pub fn new(metrics_registry: Option<&Registry>) -> Self {
		HttpRpcMiddleware {
			metrics: if let Some(r) = metrics_registry {
				if let Ok(registered_metrics) = HTTPMetrics::register(r) {
					Some(registered_metrics)
				} else {
					None
				}
			} else {
				None
			},
		}
	}
}

impl HttpRequestMiddleware for HttpRpcMiddleware {
	fn on_request(&self, request: hyper::Request<Body>) -> HttpRequestMiddlewareAction {
		if let Some(ref metrics) = self.metrics {
			metrics.http_rpc_calls.inc()
		}
		HttpRequestMiddlewareAction::Proceed {
			should_continue_on_invalid_cors: false,
			request,
		}
	}
}

struct WSMetrics {
	ws_rpc_calls: Counter<U64>,
}

impl WSMetrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(WSMetrics {
			ws_rpc_calls: register(Counter::new(
				"rpc_ws_calls",
				"Number of rpc calls received through web socket interface",
			)?, r)?,
		})
	}
}

/// Middleware for RPC calls over web sockets
pub struct WSRpcMiddleware {
	metrics: Option<WSMetrics>,
}

impl WSRpcMiddleware {
	pub fn new(metrics_registry: Option<&Registry>) -> Self {
		WSRpcMiddleware {
			metrics: if let Some(r) = metrics_registry {
				if let Ok(registered_metrics) = WSMetrics::register(r) {
					Some(registered_metrics)
				} else {
					None
				}
			} else {
				None
			},
		}
	}
}

impl WSRequestMiddleware for WSRpcMiddleware {
	fn process(&self, _req: &ws_core::Request) -> WSRequestMiddlewareAction {
		if let Some(ref metrics) = self.metrics {
			metrics.ws_rpc_calls.inc()
		}
		WSRequestMiddlewareAction::Proceed
	}
}
