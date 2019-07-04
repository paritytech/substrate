// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Contains the object that makes the telemetry work.
//!
//! # Usage
//!
//! - Create a `TelemetryWorker` with `TelemetryWorker::new`.
//! - Send messages to the telemetry with `TelemetryWorker::send_message`. Messages will only be
//!   sent to the appropriate targets. Messages may be ignored if the target happens to be
//!   temporarily unreachable.
//! - You must appropriately poll the worker with `TelemetryWorker::poll`. Polling will/may produce
//!   events indicating what happened since the latest polling.
//!

use bytes::BytesMut;
use futures::prelude::*;
use libp2p::{core::transport::OptionalTransport, core::ConnectedPoint, Multiaddr, Transport, wasm_ext};
use log::{trace, warn, error};
use slog::Drain;
use std::{io, time};
use tokio_io::AsyncWrite;

mod node;

/// Timeout after which a connection attempt is considered failed. Includes the WebSocket HTTP
/// upgrading.
const CONNECT_TIMEOUT: time::Duration = time::Duration::from_secs(20);

/// Event generated when polling the worker.
#[derive(Debug)]
pub enum TelemetryWorkerEvent {
	/// We have established a connection to one of the telemetry endpoint, either for the first
	/// time or after having been disconnected earlier.
	Connected,
}

/// Telemetry processing machine.
#[derive(Debug)]
pub struct TelemetryWorker {
	/// List of nodes with their maximum verbosity level.
	nodes: Vec<(node::Node<WsTrans>, u8)>,
}

/// The pile of libp2p transports.
#[cfg(not(target_os = "unknown"))]
type WsTrans = libp2p::core::transport::timeout::TransportTimeout<
	libp2p::core::transport::OrTransport<
		libp2p::core::transport::map::Map<
			OptionalTransport<wasm_ext::ExtTransport>,
			fn(wasm_ext::Connection, ConnectedPoint) -> StreamSink<wasm_ext::Connection>
		>,
		libp2p::websocket::framed::WsConfig<libp2p::dns::DnsConfig<libp2p::tcp::TcpConfig>>
	>
>;
#[cfg(target_os = "unknown")]
type WsTrans = libp2p::core::transport::timeout::TransportTimeout<
	libp2p::core::transport::map::Map<
		OptionalTransport<wasm_ext::ExtTransport>,
		fn(wasm_ext::Connection, ConnectedPoint) -> StreamSink<wasm_ext::Connection>
	>
>;

impl TelemetryWorker {
	/// Builds a new `TelemetryWorker`.
	///
	/// The endpoints must be a list of targets, plus a verbosity level. When you send a message
	/// to the telemetry, only the targets whose verbosity is higher than the verbosity of the
	/// message will receive it.
	pub fn new(
		endpoints: impl IntoIterator<Item = (Multiaddr, u8)>,
		wasm_external_transport: impl Into<Option<wasm_ext::ExtTransport>>
	) -> Self {
		let transport = match wasm_external_transport.into() {
			Some(t) => OptionalTransport::some(t),
			None => OptionalTransport::none()
		}.map((|inner, _| StreamSink(inner)) as fn(_, _) -> _);

		// The main transport is the `wasm_external_transport`, but if we're on desktop we add
		// support for TCP+WebSocket+DNS as a fallback. In practice, you're not expected to pass
		// an external transport on desktop and the fallback is used all the time.
		#[cfg(not(target_os = "unknown"))]
		let transport = transport.or_transport({
			let inner = libp2p::dns::DnsConfig::new(libp2p::tcp::TcpConfig::new());
			libp2p::websocket::framed::WsConfig::new(inner)
		});

		let transport = transport.with_timeout(CONNECT_TIMEOUT);

		TelemetryWorker {
			nodes: endpoints.into_iter().map(|(addr, verbosity)| {
				let node = node::Node::new(transport.clone(), addr);
				(node, verbosity)
			}).collect()
		}
	}

	/// Polls the worker for events that happened.
	pub fn poll(&mut self) -> Async<TelemetryWorkerEvent> {
		for (node, _) in &mut self.nodes {
			loop {
				match node.poll() {
					Async::Ready(node::NodeEvent::Connected) =>
						return Async::Ready(TelemetryWorkerEvent::Connected),
					Async::Ready(node::NodeEvent::Disconnected(_)) => continue,
					Async::NotReady => break,
				}
			}
		}

		Async::NotReady
	}

	/// Equivalent to `slog::Drain::log`, but takes `self` by `&mut` instead, which is more convenient.
	///
	/// Keep in mind that you should call `TelemetryWorker::poll` in order to process the messages.
	/// You should call this function right after calling `slog::Drain::log`.
	pub fn log(&mut self, record: &slog::Record, values: &slog::OwnedKVList) -> Result<(), ()> {
		let msg_verbosity = match record.tag().parse::<u8>() {
			Ok(v) => v,
			Err(err) => {
				warn!(target: "telemetry", "Failed to parse telemetry tag {:?}: {:?}", 
					record.tag(), err);
				return Err(())
			}
		};

		// None of the nodes want that verbosity, so just return without doing any serialization.
		if self.nodes.iter().all(|(_, node_max_verbosity)| msg_verbosity > *node_max_verbosity) {
			trace!(
				target: "telemetry",
				"Skipping log entry because verbosity {:?} is too high for all endpoints",
				msg_verbosity
			);
			return Ok(())
		}

		// Turn the message into JSON.
		let serialized = {
			let mut out = Vec::new();
			slog_json::Json::default(&mut out).log(record, values).map_err(|_| ())?;
			out
		};

		for (node, node_max_verbosity) in &mut self.nodes {
			if msg_verbosity > *node_max_verbosity {
				trace!(target: "telemetry", "Skipping {:?} for log entry with verbosity {:?}",
					node.addr(), msg_verbosity);
				continue;
			}

			// `send_message` returns an error if we're not connected, which we silently ignore.
			let _ = node.send_message(serialized.clone());
		}

		Ok(())
	}
}

/// Wraps around an `AsyncWrite` and implements `Sink`. Guarantees that each item being sent maps
/// to one call of `write`.
///
/// For some context, we put this object around the `wasm_ext::ExtTransport` in order to make sure
/// that each telemetry message maps to one single call to `write` in the WASM FFI.
struct StreamSink<T>(T);
impl<T: AsyncWrite> Sink for StreamSink<T> {
	type SinkItem = BytesMut;
	type SinkError = io::Error;

	fn start_send(&mut self, item: Self::SinkItem) -> Result<AsyncSink<Self::SinkItem>, io::Error> {
		match self.0.write(&item[..]) {
			Ok(n) if n == item.len() => Ok(AsyncSink::Ready),
			Ok(_) => {
				error!(target: "telemetry",
					"Detected some internal buffering happening in the telemetry");
				Err(io::Error::new(io::ErrorKind::Other, "Internal buffering detected"))
			},
			Err(ref err) if err.kind() == io::ErrorKind::WouldBlock => Ok(AsyncSink::NotReady(item)),
			Err(err) => Err(err),
		}
	}

	fn poll_complete(&mut self) -> Poll<(), io::Error> {
		match self.0.flush() {
			Ok(()) => Ok(Async::Ready(())),
			Err(ref err) if err.kind() == io::ErrorKind::WouldBlock => Ok(Async::NotReady),
			Err(err) => Err(err),
		}
	}
}
