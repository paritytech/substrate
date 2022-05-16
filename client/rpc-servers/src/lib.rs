// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
use std::{error::Error as StdError, net::SocketAddr};

pub use crate::middleware::{RpcMetrics, RpcMiddleware};
pub use jsonrpsee::core::{
	id_providers::{RandomIntegerIdProvider, RandomStringIdProvider},
	traits::IdProvider,
};

const MEGABYTE: usize = 1024 * 1024;

/// Maximal payload accepted by RPC servers.
pub const RPC_MAX_PAYLOAD_DEFAULT: usize = 15 * MEGABYTE;

/// Default maximum number of connections for WS RPC servers.
const WS_MAX_CONNECTIONS: usize = 100;

/// Default maximum number subscriptions per connection for WS RPC servers.
const WS_MAX_SUBS_PER_CONN: usize = 1024;

pub mod middleware;

/// Type alias for http server
pub type HttpServer = HttpServerHandle;
/// Type alias for ws server
pub type WsServer = WsServerHandle;

/// WebSocket specific settings on the server.
pub struct WsConfig {
	/// Maximum connections.
	pub max_connections: Option<usize>,
	/// Maximum subscriptions per connection.
	pub max_subs_per_conn: Option<usize>,
	/// Maximum rpc request payload size.
	pub max_payload_in_mb: Option<usize>,
	/// Maximum rpc response payload size.
	pub max_payload_out_mb: Option<usize>,
}

impl WsConfig {
	// Deconstructs the config to get the finalized inner values.
	//
	// `Payload size` or `max subs per connection` bigger than u32::MAX will be truncated.
	fn deconstruct(self) -> (u32, u32, u64, u32) {
		let max_conns = self.max_connections.unwrap_or(WS_MAX_CONNECTIONS) as u64;
		let max_payload_in_mb = payload_size_or_default(self.max_payload_in_mb) as u32;
		let max_payload_out_mb = payload_size_or_default(self.max_payload_out_mb) as u32;
		let max_subs_per_conn = self.max_subs_per_conn.unwrap_or(WS_MAX_SUBS_PER_CONN) as u32;

		(max_payload_in_mb, max_payload_out_mb, max_conns, max_subs_per_conn)
	}
}

/// Start HTTP server listening on given address.
pub async fn start_http<M: Send + Sync + 'static>(
	addrs: [SocketAddr; 2],
	cors: Option<&Vec<String>>,
	max_payload_in_mb: Option<usize>,
	max_payload_out_mb: Option<usize>,
	metrics: Option<RpcMetrics>,
	rpc_api: RpcModule<M>,
	rt: tokio::runtime::Handle,
) -> Result<HttpServerHandle, Box<dyn StdError + Send + Sync>> {
	let max_payload_in = payload_size_or_default(max_payload_in_mb);
	let max_payload_out = payload_size_or_default(max_payload_out_mb);

	let mut acl = AccessControlBuilder::new();

	if let Some(cors) = cors {
		// Whitelist listening address.
		// NOTE: set_allowed_hosts will whitelist both ports but only one will used.
		acl = acl.set_allowed_hosts(format_allowed_hosts(&addrs[..]))?;
		acl = acl.set_allowed_origins(cors)?;
	};

	let builder = HttpServerBuilder::new()
		.max_request_body_size(max_payload_in as u32)
		.max_response_body_size(max_payload_out as u32)
		.set_access_control(acl.build())
		.health_api("/health", "system_health")
		.custom_tokio_runtime(rt);

	let rpc_api = build_rpc_api(rpc_api);
	let (handle, addr) = if let Some(metrics) = metrics {
		let middleware = RpcMiddleware::new(metrics, "http".into());
		let builder = builder.set_middleware(middleware);
		let server = builder.build(&addrs[..]).await?;
		let addr = server.local_addr();
		(server.start(rpc_api)?, addr)
	} else {
		let server = builder.build(&addrs[..]).await?;
		let addr = server.local_addr();
		(server.start(rpc_api)?, addr)
	};

	log::info!(
		"Running JSON-RPC HTTP server: addr={}, allowed origins={:?}",
		addr.map_or_else(|_| "unknown".to_string(), |a| a.to_string()),
		cors
	);

	Ok(handle)
}

/// Start WS server listening on given address.
pub async fn start_ws<M: Send + Sync + 'static>(
	addrs: [SocketAddr; 2],
	cors: Option<&Vec<String>>,
	ws_config: WsConfig,
	metrics: Option<RpcMetrics>,
	rpc_api: RpcModule<M>,
	rt: tokio::runtime::Handle,
	id_provider: Option<Box<dyn IdProvider>>,
) -> Result<WsServerHandle, Box<dyn StdError + Send + Sync>> {
	let (max_payload_in, max_payload_out, max_connections, max_subs_per_conn) =
		ws_config.deconstruct();

	let mut builder = WsServerBuilder::new()
		.max_request_body_size(max_payload_in)
		.max_response_body_size(max_payload_out)
		.max_connections(max_connections)
		.max_subscriptions_per_connection(max_subs_per_conn)
		.custom_tokio_runtime(rt);

	if let Some(provider) = id_provider {
		builder = builder.set_id_provider(provider);
	} else {
		builder = builder.set_id_provider(RandomStringIdProvider::new(16));
	};

	if let Some(cors) = cors {
		// Whitelist listening address.
		// NOTE: set_allowed_hosts will whitelist both ports but only one will used.
		builder = builder.set_allowed_hosts(format_allowed_hosts(&addrs[..]))?;
		builder = builder.set_allowed_origins(cors)?;
	}

	let rpc_api = build_rpc_api(rpc_api);
	let (handle, addr) = if let Some(metrics) = metrics {
		let middleware = RpcMiddleware::new(metrics, "ws".into());
		let builder = builder.set_middleware(middleware);
		let server = builder.build(&addrs[..]).await?;
		let addr = server.local_addr();
		(server.start(rpc_api)?, addr)
	} else {
		let server = builder.build(&addrs[..]).await?;
		let addr = server.local_addr();
		(server.start(rpc_api)?, addr)
	};

	log::info!(
		"Running JSON-RPC WS server: addr={}, allowed origins={:?}",
		addr.map_or_else(|_| "unknown".to_string(), |a| a.to_string()),
		cors
	);

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

fn payload_size_or_default(size_mb: Option<usize>) -> usize {
	size_mb.map_or(RPC_MAX_PAYLOAD_DEFAULT, |mb| mb.saturating_mul(MEGABYTE))
}
