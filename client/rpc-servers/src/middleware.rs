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

use std::{
	error::Error,
	future::Future,
	net::SocketAddr,
	pin::Pin,
	task::{Context, Poll},
};

use http::{HeaderValue, Method, Request, Response, StatusCode, Uri};
use hyper::Body;
use jsonrpsee::{
	server::logger::{HttpRequest, Logger, MethodKind, Params, TransportProtocol},
	types::Response as RpcResponse,
};
use prometheus_endpoint::{
	register, Counter, CounterVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry,
	U64,
};
use tower::Service;

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

const RPC_SYSTEM_HEALTH_CALL: &str = r#"{"jsonrpc":"2.0","method":"system_health","id":0}"#;
const HEADER_VALUE_JSON: HeaderValue = HeaderValue::from_static("application/json; charset=utf-8");

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

/// Layer that applies [`NodeHealthProxy`] which
/// proxies `/health` and `/health/readiness` endpoints.
#[derive(Debug, Clone, Default)]
pub(crate) struct NodeHealthProxyLayer;

impl NodeHealthProxyLayer {
	pub fn new() -> Self {
		Self
	}
}

impl<S> tower::Layer<S> for NodeHealthProxyLayer {
	type Service = NodeHealthProxy<S>;

	fn layer(&self, service: S) -> Self::Service {
		NodeHealthProxy::new(service)
	}
}

pub(crate) struct NodeHealthProxy<S>(S);

impl<S> NodeHealthProxy<S> {
	/// Creates a new [`NodeHealthProxy`].
	pub fn new(service: S) -> Self {
		Self(service)
	}
}

impl<S> tower::Service<http::Request<Body>> for NodeHealthProxy<S>
where
	S: Service<http::Request<Body>, Response = Response<Body>>,
	S::Response: 'static,
	S::Error: Into<Box<dyn Error + Send + Sync>> + 'static,
	S::Future: Send + 'static,
{
	type Response = S::Response;
	type Error = Box<dyn Error + Send + Sync + 'static>;
	type Future =
		Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send + 'static>>;

	fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
		self.0.poll_ready(cx).map_err(Into::into)
	}

	fn call(&mut self, mut req: Request<Body>) -> Self::Future {
		let maybe_intercept = InterceptRequest::from_http(&req);

		// Modify the request and proxy it to `system_health`
		if let InterceptRequest::Health | InterceptRequest::Readiness = maybe_intercept {
			// RPC methods are accessed with `POST`.
			*req.method_mut() = Method::POST;
			// Precautionary remove the URI.
			*req.uri_mut() = Uri::from_static("/");

			// Requests must have the following headers:
			req.headers_mut().insert(http::header::CONTENT_TYPE, HEADER_VALUE_JSON);
			req.headers_mut().insert(http::header::ACCEPT, HEADER_VALUE_JSON);

			// Adjust the body to reflect the method call.
			req = req.map(|_| Body::from(RPC_SYSTEM_HEALTH_CALL));
		}

		// Call the inner service and get a future that resolves to the response.
		let fut = self.0.call(req);

		let res_fut = async move {
			let res = fut.await.map_err(|err| err.into())?;

			Ok(match maybe_intercept {
				InterceptRequest::No => res,
				InterceptRequest::Health => {
					let health = parse_rpc_response(res.into_body()).await?;
					http_ok_response(serde_json::to_string(&health)?)
				},
				InterceptRequest::Readiness => {
					let health = parse_rpc_response(res.into_body()).await?;
					if !health.is_syncing && health.peers > 0 {
						http_ok_response(Body::empty())
					} else {
						http_internal_error()
					}
				},
			})
		};

		Box::pin(res_fut)
	}
}

// NOTE: This is duplicated here to avoid dependency to the `RPC API`.
#[derive(Debug, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct Health {
	/// Number of connected peers
	pub peers: usize,
	/// Is the node syncing
	pub is_syncing: bool,
	/// Should this node have any peers
	///
	/// Might be false for local chains or when running without discovery.
	pub should_have_peers: bool,
}

fn http_ok_response<S: Into<hyper::Body>>(body: S) -> hyper::Response<hyper::Body> {
	http_response(StatusCode::OK, body)
}

fn http_response<S: Into<hyper::Body>>(
	status_code: StatusCode,
	body: S,
) -> hyper::Response<hyper::Body> {
	hyper::Response::builder()
		.status(status_code)
		.header(http::header::CONTENT_TYPE, HEADER_VALUE_JSON)
		.body(body.into())
		.expect("Header is valid; qed")
}

fn http_internal_error() -> hyper::Response<hyper::Body> {
	http_response(hyper::StatusCode::INTERNAL_SERVER_ERROR, Body::empty())
}

async fn parse_rpc_response(body: Body) -> Result<Health, Box<dyn Error + Send + Sync + 'static>> {
	let bytes = hyper::body::to_bytes(body).await?;

	serde_json::from_slice::<RpcResponse<Health>>(&bytes)
		.map(|r| r.result)
		.map_err(Into::into)
}

/// Whether the request should be treated as ordinary RPC call or be modified.
enum InterceptRequest {
	/// Proxy `/health` to `system_health`.
	Health,
	/// Checks if node has at least one peer and is not doing major syncing.
	///
	/// Returns HTTP status code 200 on success otherwise HTTP status code 500 is returned.
	Readiness,
	/// Treat as a ordinary RPC call and don't modify the request or response.
	No,
}

impl InterceptRequest {
	fn from_http(req: &Request<Body>) -> Self {
		match req.uri().path() {
			"/health" if req.method() == http::Method::GET => InterceptRequest::Health,
			"/health/readiness" if req.method() == http::Method::GET => InterceptRequest::Readiness,
			_ => InterceptRequest::No,
		}
	}
}
