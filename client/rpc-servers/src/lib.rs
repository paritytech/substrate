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
	http_server::{HttpServerBuilder, HttpStopHandle},
	ws_server::{WsServerBuilder, WsStopHandle},
	RpcModule,
};

const MEGABYTE: usize = 1024 * 1024;

/// Maximal payload accepted by RPC servers.
pub const RPC_MAX_PAYLOAD_DEFAULT: usize = 15 * MEGABYTE;

/// Default maximum number of connections for WS RPC servers.
const WS_MAX_CONNECTIONS: usize = 100;

/*/// RPC server-specific prometheus metrics.
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
}*/

/// Type alias for http server
pub type HttpServer = HttpStopHandle;
/// Type alias for ws server
pub type WsServer = WsStopHandle;

// TODO: (dp) port this stuff
// impl ws::SessionStats for ServerMetrics {
// 	fn open_session(&self, _id: ws::SessionId) {
// 		self.session_opened.as_ref().map(|m| m.inc());
// 	}

// 	fn close_session(&self, _id: ws::SessionId) {
// 		self.session_closed.as_ref().map(|m| m.inc());
// 	}
// }

/// Start HTTP server listening on given address.
pub fn start_http<M: Send + Sync + 'static>(
	addr: std::net::SocketAddr,
	_cors: Option<&Vec<String>>,
	maybe_max_payload_mb: Option<usize>,
	module: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<HttpStopHandle, anyhow::Error> {
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);

	let server = HttpServerBuilder::default()
		.max_request_body_size(max_request_body_size as u32)
		.build(addr)?;

	let handle = server.stop_handle();
	let rpc_api = build_rpc_api(module);

	rt.spawn(async move {
		let _ = server.start(rpc_api).await;
	});

	Ok(handle)
}

/// Start WS server listening on given address.
pub fn start_ws<M: Send + Sync + 'static>(
	addr: std::net::SocketAddr,
	max_connections: Option<usize>,
	_cors: Option<&Vec<String>>,
	maybe_max_payload_mb: Option<usize>,
	module: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<WsStopHandle, anyhow::Error> {
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
	let max_connections = max_connections.unwrap_or(WS_MAX_CONNECTIONS);

	let server = tokio::task::block_in_place(|| {
		rt.block_on(
			WsServerBuilder::default()
				.max_request_body_size(max_request_body_size as u32)
				.max_connections(max_connections as u64)
				.build(addr),
		)
	})?;

	let handle = server.stop_handle();
	let rpc_api = build_rpc_api(module);
	rt.spawn(async move { server.start(rpc_api).await });

	Ok(handle)
}

fn build_rpc_api<M: Send + Sync + 'static>(mut rpc_api: RpcModule<M>) -> RpcModule<M> {
	let mut available_methods = rpc_api.method_names().collect::<Vec<_>>();
	// NOTE(niklasad1): substrate master doesn't have this.
	available_methods.push("rpc_methods");
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
