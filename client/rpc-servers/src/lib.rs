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

mod middleware;

use jsonrpc_core::{IoHandlerExtension, MetaIoHandler};
use log::error;
use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use pubsub::PubSubMetadata;
use std::io;

const MEGABYTE: usize = 1024 * 1024;

/// Maximal payload accepted by RPC servers.
pub const RPC_MAX_PAYLOAD_DEFAULT: usize = 15 * MEGABYTE;

/// Default maximum number of connections for WS RPC servers.
const WS_MAX_CONNECTIONS: usize = 100;

/// Default thread pool size for RPC HTTP servers.
const HTTP_THREADS: usize = 4;

/// The RPC IoHandler containing all requested APIs.
pub type RpcHandler<T> = pubsub::PubSubHandler<T, RpcMiddleware>;

pub use middleware::{method_names, RpcMetrics, RpcMiddleware};

/// Construct rpc `IoHandler`
pub fn rpc_handler<M: PubSubMetadata>(
	extension: impl IoHandlerExtension<M>,
	rpc_middleware: RpcMiddleware,
) -> RpcHandler<M> {
	let io_handler = MetaIoHandler::with_middleware(rpc_middleware);
	let mut io = pubsub::PubSubHandler::new(io_handler);
	extension.augment(&mut io);

	// add an endpoint to list all available methods.
	let mut methods = io.iter().map(|x| x.0.clone()).collect::<Vec<String>>();
	io.add_method("rpc_methods", {
		methods.sort();
		let methods = serde_json::to_value(&methods)
			.expect("Serialization of Vec<String> is infallible; qed");

		move |_| {
			let methods = methods.clone();
			async move {
				Ok(serde_json::json!({
					"version": 1,
					"methods": methods,
				}))
			}
		}
	});
	io
}

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

/// Type alias for ipc server
pub type IpcServer = ipc::Server;
/// Type alias for http server
pub type HttpServer = http::Server;
/// Type alias for ws server
pub type WsServer = ws::Server;

impl ws::SessionStats for ServerMetrics {
	fn open_session(&self, _id: ws::SessionId) {
		self.session_opened.as_ref().map(|m| m.inc());
	}

	fn close_session(&self, _id: ws::SessionId) {
		self.session_closed.as_ref().map(|m| m.inc());
	}
}

/// Start HTTP server listening on given address.
pub fn start_http<M: pubsub::PubSubMetadata + Default + Unpin>(
	addr: &std::net::SocketAddr,
	thread_pool_size: Option<usize>,
	cors: Option<&Vec<String>>,
	io: RpcHandler<M>,
	maybe_max_payload_mb: Option<usize>,
) -> io::Result<http::Server> {
	let max_request_body_size = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);

	http::ServerBuilder::new(io)
		.threads(thread_pool_size.unwrap_or(HTTP_THREADS))
		.health_api(("/health", "system_health"))
		.allowed_hosts(hosts_filtering(cors.is_some()))
		.rest_api(if cors.is_some() { http::RestApi::Secure } else { http::RestApi::Unsecure })
		.cors(map_cors::<http::AccessControlAllowOrigin>(cors))
		.max_request_body_size(max_request_body_size)
		.start_http(addr)
}

/// Start IPC server listening on given path.
pub fn start_ipc<M: pubsub::PubSubMetadata + Default>(
	addr: &str,
	io: RpcHandler<M>,
	server_metrics: ServerMetrics,
) -> io::Result<ipc::Server> {
	let builder = ipc::ServerBuilder::new(io);
	#[cfg(target_os = "unix")]
	builder.set_security_attributes({
		let security_attributes = ipc::SecurityAttributes::empty();
		security_attributes.set_mode(0o600)?;
		security_attributes
	});
	builder.session_stats(server_metrics).start(addr)
}

/// Start WS server listening on given address.
pub fn start_ws<
	M: pubsub::PubSubMetadata + From<futures::channel::mpsc::UnboundedSender<String>>,
>(
	addr: &std::net::SocketAddr,
	max_connections: Option<usize>,
	cors: Option<&Vec<String>>,
	io: RpcHandler<M>,
	maybe_max_payload_mb: Option<usize>,
	server_metrics: ServerMetrics,
) -> io::Result<ws::Server> {
	let rpc_max_payload = maybe_max_payload_mb
		.map(|mb| mb.saturating_mul(MEGABYTE))
		.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
	ws::ServerBuilder::with_meta_extractor(io, |context: &ws::RequestContext| {
		context.sender().into()
	})
	.max_payload(rpc_max_payload)
	.max_connections(max_connections.unwrap_or(WS_MAX_CONNECTIONS))
	.allowed_origins(map_cors(cors))
	.allowed_hosts(hosts_filtering(cors.is_some()))
	.session_stats(server_metrics)
	.start(addr)
	.map_err(|err| match err {
		ws::Error::Io(io) => io,
		ws::Error::ConnectionClosed => io::ErrorKind::BrokenPipe.into(),
		e => {
			error!("{}", e);
			io::ErrorKind::Other.into()
		},
	})
}

fn map_cors<T: for<'a> From<&'a str>>(cors: Option<&Vec<String>>) -> http::DomainsValidation<T> {
	cors.map(|x| x.iter().map(AsRef::as_ref).map(Into::into).collect::<Vec<_>>())
		.into()
}

fn hosts_filtering(enable: bool) -> http::DomainsValidation<http::Host> {
	if enable {
		// NOTE The listening address is whitelisted by default.
		// Setting an empty vector here enables the validation
		// and allows only the listening address.
		http::DomainsValidation::AllowOnly(vec![])
	} else {
		http::DomainsValidation::Disabled
	}
}
