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
	Call, FutureOutput, FutureResponse, Metadata, Middleware as RequestMiddleware, Output, Request,
	Response,
};
use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};

use futures::{future::Either, Future};

/// Custom rpc middleware
pub trait CustomMiddleware<M: Metadata>:
	Clone + Default + RequestMiddleware<M, Future = FutureResponse, CallFuture = FutureOutput>
{
}

impl<M, T> CustomMiddleware<M> for T
where
	M: Metadata,
	T: Clone + Default + RequestMiddleware<M, Future = FutureResponse, CallFuture = FutureOutput>,
{
}

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
pub struct RpcMiddleware<M: Metadata, CM: CustomMiddleware<M> = NoopCustomMiddleware> {
	metrics: RpcMetrics,
	transport_label: String,
	custom_middleware: CM,
	phantom: core::marker::PhantomData<M>,
}

impl<M: Metadata, CM: CustomMiddleware<M>> RpcMiddleware<M, CM> {
	/// Create an instance of middleware.
	///
	/// - `metrics`: Will be used to report statistics.
	/// - `transport_label`: The label that is used when reporting the statistics.
	pub fn new(metrics: RpcMetrics, transport_label: &str) -> Self {
		RpcMiddleware {
			metrics,
			transport_label: String::from(transport_label),
			custom_middleware: Default::default(),
			phantom: core::marker::PhantomData,
		}
	}
	/// Create an instance of middleware with a sub-middleware
	///
	/// - `metrics`: Will be used to report statistics.
	/// - `transport_label`: The label that is used when reporting the statistics.
	pub fn new_with_custom_middleware(
		metrics: RpcMetrics,
		transport_label: &str,
		custom_middleware: CM,
	) -> Self {
		RpcMiddleware {
			metrics,
			transport_label: String::from(transport_label),
			custom_middleware,
			phantom: core::marker::PhantomData,
		}
	}
}

impl<M: Metadata + Sync, CM: CustomMiddleware<M>> RequestMiddleware<M> for RpcMiddleware<M, CM> {
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

		self.custom_middleware.on_request(request, meta, next)
	}

	fn on_call<F, X>(&self, call: Call, meta: M, next: F) -> Either<Self::CallFuture, X>
	where
		F: Fn(Call, M) -> X + Send + Sync,
		X: Future<Output = Option<Output>> + Send + 'static,
	{
		self.custom_middleware.on_call(call, meta, next)
	}
}

#[derive(Clone, Copy, Default)]
/// The default custom middleware, do nothing
pub struct NoopCustomMiddleware;

impl<M: Metadata> RequestMiddleware<M> for NoopCustomMiddleware {
	type Future = FutureResponse;
	type CallFuture = FutureOutput;
}
