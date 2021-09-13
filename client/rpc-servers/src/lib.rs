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

use futures_channel::oneshot;
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
pub async fn start_http<M: Send + Sync + 'static>(
	addr: std::net::SocketAddr,
	_cors: Option<&Vec<String>>,
	maybe_max_payload_mb: Option<usize>,
	mut module: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<HttpStopHandle, String> {
	let (tx, rx) = oneshot::channel::<Result<HttpStopHandle, String>>();
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);

	rt.spawn(async move {
		let server = match HttpServerBuilder::default()
			.max_request_body_size(max_request_body_size as u32)
			.build(addr)
		{
			Ok(server) => server,
			Err(e) => {
				let _ = tx.send(Err(e.to_string()));
				return
			},
		};
		// TODO: (dp) DRY this up; it's the same as the WS code
		let handle = server.stop_handle();
		let mut methods_api = RpcModule::new(());
		let mut available_methods = module.method_names().collect::<Vec<_>>();
		available_methods.sort_unstable();

		// TODO: (dp) not sure this is correct; shouldn't the `rpc_methods` also be listed?
		methods_api
			.register_method("rpc_methods", move |_, _| {
				Ok(serde_json::json!({
					"version": 1,
					"methods": available_methods,
				}))
			})
			.expect("infallible all other methods have their own address space; qed");

		module.merge(methods_api).expect("infallible already checked; qed");
		let _ = tx.send(Ok(handle));
		let _ = server.start(module).await;
	});

	rx.await.unwrap_or(Err("Channel closed".to_string()))
}

/// Start WS server listening on given address.
pub async fn start_ws<M: Send + Sync + 'static>(
	addr: std::net::SocketAddr,
	max_connections: Option<usize>,
	_cors: Option<&Vec<String>>,
	maybe_max_payload_mb: Option<usize>,
	mut module: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<WsStopHandle, String> {
	let (tx, rx) = oneshot::channel::<Result<WsStopHandle, String>>();
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
	let max_connections = max_connections.unwrap_or(WS_MAX_CONNECTIONS);

	rt.spawn(async move {
		let server = match WsServerBuilder::default()
			.max_request_body_size(max_request_body_size as u32)
			.max_connections(max_connections as u64)
			.build(addr)
			.await
		{
			Ok(server) => server,
			Err(e) => {
				let _ = tx.send(Err(e.to_string()));
				return
			},
		};
		// TODO: (dp) DRY this up; it's the same as the HTTP code
		let handle = server.stop_handle();
		let mut methods_api = RpcModule::new(());
		let mut available_methods = module.method_names().collect::<Vec<_>>();
		available_methods.sort();

		// TODO: (dp) not sure this is correct; shouldn't the `rpc_methods` also be listed?
		methods_api
			.register_method("rpc_methods", move |_, _| {
				Ok(serde_json::json!({
					"version": 1,
					"methods": available_methods,
				}))
			})
			.expect("infallible all other methods have their own address space; qed");

		module.merge(methods_api).expect("infallible already checked; qed");
		let _ = tx.send(Ok(handle));
		server.start(module).await;
	});

	rx.await.unwrap_or(Err("Channel closed".to_string()))
}
