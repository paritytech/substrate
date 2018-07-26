// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Telemtetry utils.
//! 
//! `telemetry` macro be used from whereever in the Substrate codebase
//! in order to send real-time logging information to the telemetry
//! server (if there is one). We use the async drain adapter of `slog`
//! so that the logging thread doesn't get held up at all.

extern crate parking_lot;
extern crate websocket as ws;
extern crate slog_async;
extern crate slog_json;
#[macro_use]
extern crate log;
#[macro_use(o, kv)]
extern crate slog;
extern crate slog_scope;

use std::{io, time};
use parking_lot::Mutex;
use slog::Drain;
pub use slog_scope::with_logger;

/// Configuration for telemetry.
pub struct TelemetryConfig {
	/// URL of the telemetry WebSocket server.
	pub url: String,
	/// What do do when we connect to the server.
	pub on_connect: Box<Fn() + Send + 'static>,
}

/// Telemetry service guard.
pub type Telemetry = slog_scope::GlobalLoggerGuard;

/// Size of the channel for passing messages to telemetry thread.
const CHANNEL_SIZE: usize = 262144;

/// Initialise telemetry.
pub fn init_telemetry(config: TelemetryConfig) -> slog_scope::GlobalLoggerGuard {
	let client = ws::ClientBuilder::new(&config.url).ok().and_then(|mut x| x.connect(None).ok());
	let log = slog::Logger::root(
		slog_async::Async::new(
			slog_json::Json::default(
				TelemetryWriter {
					buffer: vec![],
					out: Mutex::new(client),
					config,
					last_time: None,	// ensures that on_connect will be called.
				}
			).fuse()
		).chan_size(CHANNEL_SIZE)
		.overflow_strategy(slog_async::OverflowStrategy::DropAndReport)
		.build().fuse(), o!()
	);
	slog_scope::set_global_logger(log)
}

/// Exactly equivalent to `slog_scope::info`, provided as a convenience.
#[macro_export]
macro_rules! telemetry {
	( $($t:tt)* ) => { $crate::with_logger(|l| slog_info!(l, $($t)* )) }
}

struct TelemetryWriter {
	buffer: Vec<u8>,
	out: Mutex<Option<ws::sync::Client<Box<ws::stream::sync::NetworkStream + Send>>>>,
	config: TelemetryConfig,
	last_time: Option<time::Instant>,
}

/// Every two minutes we reconnect to the telemetry server otherwise we don't get notified
/// of a flakey connection that has been dropped and needs to be reconnected. We can remove
/// this once we introduce a keepalive ping/pong.
const RECONNECT_PERIOD: u64 = 120;

impl TelemetryWriter {
	fn ensure_connected(&mut self) {
		let mut client = self.out.lock();

		let controlled_disconnect = if let Some(t) = self.last_time {
			if t.elapsed().as_secs() > RECONNECT_PERIOD && client.is_some() {
				trace!(target: "telemetry", "Performing controlled drop of the telemetry connection.");
				let _ = client.as_mut().and_then(|socket|
					socket.send_message(&ws::Message::text("{\"msg\":\"system.reconnect\"}")).ok()
				);
				*client = None;
				true
			} else {
				false
			}
		} else {
			false
		};

		let just_connected = if client.is_none() {
			if !controlled_disconnect {
				info!(target: "telemetry", "Connection dropped unexpectedly. Reconnecting to telemetry server...");
			}
			*client = ws::ClientBuilder::new(&self.config.url).ok().and_then(|mut x| x.connect(None).ok());
			client.is_some()
		} else {
			self.last_time.is_none()
		};

		drop(client);
		if just_connected {
			if !controlled_disconnect {
				info!("Reconnected to telemetry server: {}", self.config.url);
			}
			self.last_time = Some(time::Instant::now());
			(self.config.on_connect)();
		}
	}
}

impl io::Write for TelemetryWriter {
	fn write(&mut self, msg: &[u8]) -> io::Result<usize> {
		if msg.iter().any(|x| *x == b'\n') {
			let _ = self.flush();
		} else {
			self.buffer.extend_from_slice(msg);
		}
		Ok(msg.len())
	}

	fn flush(&mut self) -> io::Result<()> {
		self.ensure_connected();

		let mut l = self.out.lock();
		let socket_closed = if let Some(ref mut socket) = *l {
			if let Ok(s) = ::std::str::from_utf8(&self.buffer[..]) {
				let r = socket.send_message(&ws::Message::text(s));
				trace!(target: "telemetry", "Sent to telemetry: {} -> {:?}", s, r);
				r.is_err()
			} else { false }
		} else { false };
		if socket_closed {
			*l = None;
		}
		self.buffer.clear();
		Ok(())
	}
}
