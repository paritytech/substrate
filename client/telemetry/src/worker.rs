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

use futures::{prelude::*, ready};
use libp2p::{
	core::transport::{OptionalTransport, timeout::TransportTimeout},
	Multiaddr,
	Transport,
	wasm_ext
};
use log::{trace, warn, error};
use slog::Drain;
use std::{io, pin::Pin, task::Context, task::Poll, time};

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

trait StreamAndSink<I>: Stream + Sink<I> {}
impl<T: ?Sized + Stream + Sink<I>, I> StreamAndSink<I> for T {}

type WsTrans = libp2p::core::transport::Boxed<
	Pin<Box<dyn StreamAndSink<
		Vec<u8>,
		Item = Result<Vec<u8>, io::Error>,
		Error = io::Error
	> + Send>>
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
	) -> Result<Self, io::Error> {
		let transport = match wasm_external_transport.into() {
			Some(t) => OptionalTransport::some(t),
			None => OptionalTransport::none()
		}.map((|inner, _| StreamSink::from(inner)) as fn(_, _) -> _);

		// The main transport is the `wasm_external_transport`, but if we're on desktop we add
		// support for TCP+WebSocket+DNS as a fallback. In practice, you're not expected to pass
		// an external transport on desktop and the fallback is used all the time.
		#[cfg(not(target_os = "unknown"))]
		let transport = transport.or_transport({
			let inner = libp2p::dns::DnsConfig::new(libp2p::tcp::TcpConfig::new())?;
			libp2p::websocket::framed::WsConfig::new(inner)
				.and_then(|connec, _| {
					let connec = connec
						.with(|item| {
							let item = libp2p::websocket::framed::OutgoingData::Binary(item);
							future::ready(Ok::<_, io::Error>(item))
						})
						.try_filter(|item| future::ready(item.is_data()))
						.map_ok(|data| data.into_bytes());
					future::ready(Ok::<_, io::Error>(connec))
				})
		});

		let transport = TransportTimeout::new(
			transport.map(|out, _| {
				let out = out
					.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
					.sink_map_err(|err| io::Error::new(io::ErrorKind::Other, err));
				Box::pin(out) as Pin<Box<_>>
			}),
			CONNECT_TIMEOUT
		).boxed();

		Ok(TelemetryWorker {
			nodes: endpoints.into_iter().map(|(addr, verbosity)| {
				let node = node::Node::new(transport.clone(), addr);
				(node, verbosity)
			}).collect()
		})
	}

	/// Polls the worker for events that happened.
	pub fn poll(&mut self, cx: &mut Context) -> Poll<TelemetryWorkerEvent> {
		for (node, _) in &mut self.nodes {
			loop {
				match node::Node::poll(Pin::new(node), cx) {
					Poll::Ready(node::NodeEvent::Connected) =>
						return Poll::Ready(TelemetryWorkerEvent::Connected),
					Poll::Ready(node::NodeEvent::Disconnected(_)) => continue,
					Poll::Pending => break,
				}
			}
		}

		Poll::Pending
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
			let _ = node.send_message(&serialized.clone()[..]);
		}

		Ok(())
	}
}

/// Wraps around an `AsyncWrite` and implements `Sink`. Guarantees that each item being sent maps
/// to one call of `write`.
///
/// For some context, we put this object around the `wasm_ext::ExtTransport` in order to make sure
/// that each telemetry message maps to one single call to `write` in the WASM FFI.
#[pin_project::pin_project]
struct StreamSink<T>(#[pin] T, Option<Vec<u8>>);

impl<T> From<T> for StreamSink<T> {
	fn from(inner: T) -> StreamSink<T> {
		StreamSink(inner, None)
	}
}

impl<T: AsyncRead> Stream for StreamSink<T> {
	type Item = Result<Vec<u8>, io::Error>;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let this = self.project();
		let mut buf = vec![0; 128];
		match ready!(AsyncRead::poll_read(this.0, cx, &mut buf)) {
			Ok(0) => Poll::Ready(None),
			Ok(n) => {
				buf.truncate(n);
				Poll::Ready(Some(Ok(buf)))
			},
			Err(err) => Poll::Ready(Some(Err(err))),
		}
	}
}

impl<T: AsyncWrite> StreamSink<T> {
	fn poll_flush_buffer(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), io::Error>> {
		let this = self.project();

		if let Some(buffer) = this.1 {
			if ready!(this.0.poll_write(cx, &buffer[..]))? != buffer.len() {
				error!(target: "telemetry",
					"Detected some internal buffering happening in the telemetry");
				let err = io::Error::new(io::ErrorKind::Other, "Internal buffering detected");
				return Poll::Ready(Err(err));
			}
		}

		*this.1 = None;
		Poll::Ready(Ok(()))
	}
}

impl<T: AsyncWrite> Sink<Vec<u8>> for StreamSink<T> {
	type Error = io::Error;

	fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(StreamSink::poll_flush_buffer(self, cx))?;
		Poll::Ready(Ok(()))
	}

	fn start_send(self: Pin<&mut Self>, item: Vec<u8>) -> Result<(), Self::Error> {
		let this = self.project();
		debug_assert!(this.1.is_none());
		*this.1 = Some(item);
		Ok(())
	}

	fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(self.as_mut().poll_flush_buffer(cx))?;
		let this = self.project();
		AsyncWrite::poll_flush(this.0, cx)
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(self.as_mut().poll_flush_buffer(cx))?;
		let this = self.project();
		AsyncWrite::poll_close(this.0, cx)
	}
}
