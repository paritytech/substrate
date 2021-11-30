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

//! Substrate RPC servers.

#![warn(missing_docs)]

use jsonrpsee::{
	http_server::{AccessControlBuilder, HttpServerBuilder, HttpServerHandle},
	ws_server::{WsServerBuilder, WsServerHandle},
	RpcModule,
};
use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use std::net::SocketAddr;

use crate::middleware::{RpcMetrics, RpcMiddleware};

const MEGABYTE: usize = 1024 * 1024;

/// Maximal payload accepted by RPC servers.
pub const RPC_MAX_PAYLOAD_DEFAULT: usize = 15 * MEGABYTE;

/// Maximal buffer size in WS server.
pub const WS_MAX_BUFFER_CAPACITY_DEFAULT: usize = 16 * MEGABYTE;

/// Default maximum number of connections for WS RPC servers.
const WS_MAX_CONNECTIONS: usize = 100;

pub mod middleware;

// TODO: (dp) Wire up the ServerMetrics as well
/// RPC server-specific prometheus metrics.
#[derive(Debug, Clone, Default)]
pub struct ServerMetrics {
	/// Number of sessions opened.
	session_opened: Option<Counter<U64>>,
	/// Number of sessions closed.
	session_closed: Option<Counter<U64>>,
}

impl ServerMetrics {
	/// Create new WebSocket RPC server metrics.
	pub fn new(registry: Option<&Registry>) -> Result<Self, PrometheusError> {
		registry
			.map(|r| {
				Ok(Self {
					session_opened: register(
						Counter::new(
							"rpc_sessions_opened",
							"Number of persistent RPC sessions opened",
						)?,
						r,
					)?
					.into(),
					session_closed: register(
						Counter::new(
							"rpc_sessions_closed",
							"Number of persistent RPC sessions closed",
						)?,
						r,
					)?
					.into(),
				})
			})
			.unwrap_or_else(|| Ok(Default::default()))
	}
}

/// Type alias for http server
pub type HttpServer = HttpServerHandle;
/// Type alias for ws server
pub type WsServer = WsServerHandle;

/// Start HTTP server listening on given address.
pub fn start_http<M: Send + Sync + 'static>(
	addrs: &[SocketAddr],
	cors: Option<&Vec<String>>,
	maybe_max_payload_mb: Option<usize>,
	module: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<HttpServerHandle, anyhow::Error> {
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);

	let mut acl = AccessControlBuilder::new();

	log::info!("Starting JSON-RPC HTTP server: addr={:?}, allowed origins={:?}", addrs, cors);

	if let Some(cors) = cors {
		// Whitelist listening address.
		// NOTE: set_allowed_hosts will whitelist both ports but only one will used.
		acl = acl.set_allowed_hosts(format_allowed_hosts(addrs))?;
		acl = acl.set_allowed_origins(cors)?;
	};

	// TODO: (dp)
	let builder = HttpServerBuilder::default()
		.max_request_body_size(max_request_body_size as u32)
		.set_access_control(acl.build())
		.custom_tokio_runtime(rt.clone());

	let server = tokio::task::block_in_place(|| rt.block_on(async { builder.build(addrs) }))?;

	let rpc_api = build_rpc_api(module);
	let handle = server.start(rpc_api)?;

	Ok(handle)
}

/// Start WS server listening on given address.
pub fn start_ws<M: Send + Sync + 'static>(
	addrs: &[SocketAddr],
	max_connections: Option<usize>,
	cors: Option<&Vec<String>>,
	max_payload_mb: Option<usize>,
	prometheus_registry: Option<&Registry>,
	rpc_api: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<WsServerHandle, anyhow::Error> {
	let max_request_body_size = max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
	let max_connections = max_connections.unwrap_or(WS_MAX_CONNECTIONS);

	let mut builder = WsServerBuilder::new()
		.max_request_body_size(max_request_body_size as u32)
		.max_connections(max_connections as u64)
		.custom_tokio_runtime(rt.clone());

	if let Some(cors) = cors {
		// Whitelist listening address.
		// NOTE: set_allowed_hosts will whitelist both ports but only one will used.
		builder = builder.set_allowed_hosts(format_allowed_hosts(addrs))?;
		builder = builder.set_allowed_origins(cors)?;
	}

	let rpc_api = build_rpc_api(rpc_api);

	let handle = if let Some(prometheus_registry) = prometheus_registry {
		let metrics = RpcMetrics::new(&prometheus_registry)?;
		let middleware = RpcMiddleware::new(metrics, "ws".into());
		let builder = builder.set_middleware(middleware);
		let server = tokio::task::block_in_place(|| rt.block_on(builder.build(addrs)))?;
		server.start(rpc_api)?
	} else {
		let server= tokio::task::block_in_place(|| rt.block_on(builder.build(addrs)))?;
		server.start(rpc_api)?
	};

	log::info!("Starting JSON-RPC WS server: addrs={:?}, allowed origins={:?}", addrs, cors);
	Ok(handle)
}

fn format_allowed_hosts(addrs: &[SocketAddr]) -> Vec<String> {
	let mut hosts = Vec::with_capacity(addrs.len() * 2);
	for addr in addrs {
		hosts.push(format!("localhost:{}", addr.port()));
		hosts.push(format!("127.0.0.1:{}", addr.port()));
	}
	hosts
}

fn build_rpc_api<M: Send + Sync + 'static>(mut rpc_api: RpcModule<M>) -> RpcModule<M> {
	let mut available_methods = rpc_api.method_names().collect::<Vec<_>>();
	available_methods.sort_unstable();

	rpc_api
		.register_method("rpc_methods", move |_, _| {
			Ok(serde_json::json!({
				"version": 1,
				"methods": available_methods,
			}))
		})
		.expect("infallible all other methods have their own address space; qed");

	rpc_api
}
