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

// mod middleware;

use std::io;

const MEGABYTE: usize = 1024 * 1024;

/// Maximal payload accepted by RPC servers.
pub const RPC_MAX_PAYLOAD_DEFAULT: usize = 15 * MEGABYTE;

/// Default maximum number of connections for WS RPC servers.
const WS_MAX_CONNECTIONS: usize = 100;

/// Default thread pool size for RPC HTTP servers.
const HTTP_THREADS: usize = 4;

pub use self::inner::*;
// pub use middleware::{RpcMiddleware, RpcMetrics};

#[cfg(not(target_os = "unknown"))]
mod inner {
	use super::*;
	use jsonrpsee::{ws_server::WsServerBuilder, http_server::HttpServerBuilder, RpcModule};

	/// Start HTTP server listening on given address.
	///
	/// **Note**: Only available if `not(target_os = "unknown")`.
	// TODO: return handle here.
	pub fn start_http<M: Send + Sync + 'static>(
		addr: std::net::SocketAddr,
		worker_threads: Option<usize>,
		_cors: Option<&Vec<String>>,
		maybe_max_payload_mb: Option<usize>,
		module: RpcModule<M>,
	) -> io::Result<()>  {

		let max_request_body_size = maybe_max_payload_mb.map(|mb| mb.saturating_mul(MEGABYTE))
			.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
		std::thread::spawn(move || {
			let rt = tokio::runtime::Builder::new_multi_thread()
				.worker_threads(worker_threads.unwrap_or(HTTP_THREADS))
				.thread_name("substrate jsonrpc http server")
				.enable_all()
				.build()
				.unwrap();

			rt.block_on(async move {
				let mut server = HttpServerBuilder::default()
					.max_request_body_size(max_request_body_size as u32)
					.build(addr)
					.unwrap();

				server.register_module(module).unwrap();
				let mut methods_api = RpcModule::new(());
				let mut methods = server.method_names();
				methods.sort();

				methods_api.register_method("rpc_methods", move |_, _| {
					Ok(serde_json::json!({
						"version": 1,
						"methods": methods,
					}))
				}).unwrap();

				server.register_module(methods_api).unwrap();
				let _ = server.start().await;
			});
		});

		Ok(())
	}

	/// Start WS server listening on given address.
	///
	/// **Note**: Only available if `not(target_os = "unknown")`.
	pub fn start_ws<M: Send + Sync + 'static>(
		addr: std::net::SocketAddr,
		worker_threads: Option<usize>,
		max_connections: Option<usize>,
		_cors: Option<&Vec<String>>,
		maybe_max_payload_mb: Option<usize>,
		module: RpcModule<M>,
	) -> io::Result<()> {
		let max_request_body_size = maybe_max_payload_mb.map(|mb| mb.saturating_mul(MEGABYTE))
			.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
		let max_connections = max_connections.unwrap_or(WS_MAX_CONNECTIONS);

		std::thread::spawn(move || {
			let rt = tokio::runtime::Builder::new_multi_thread()
				.worker_threads(worker_threads.unwrap_or(HTTP_THREADS))
				.thread_name("substrate jsonrpc http server")
				.enable_all()
				.build()
				.unwrap();

			rt.block_on(async move {
				let mut server = WsServerBuilder::default()
					.max_request_body_size(max_request_body_size as u32)
					.max_connections(max_connections as u64)
					.build(addr)
					.await
					.unwrap();

				server.register_module(module).unwrap();
				let mut methods_api = RpcModule::new(());
				let mut methods = server.method_names();
				methods.sort();

				methods_api.register_method("rpc_methods", move |_, _| {
					Ok(serde_json::json!({
						"version": 1,
						"methods": methods,
					}))
				}).unwrap();

				server.register_module(methods_api).unwrap();

				let _ = server.start().await;
			});
		});
		Ok(())
	}

	// TODO: CORS and host filtering.
}

#[cfg(target_os = "unknown")]
mod inner {}
