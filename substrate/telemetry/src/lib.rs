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

use std::io;
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

/// Size of the channel for passing messages to telemetry thread.
const CHANNEL_SIZE: usize = 262144;

/// Initialise telemetry.
pub fn init_telemetry(config: TelemetryConfig) -> slog_scope::GlobalLoggerGuard {
	let log = slog::Logger::root(
		slog_async::Async::new(
			slog_json::Json::default(
				TelemetryWriter {
					buffer: vec![],
					out: Mutex::new(
						ws::ClientBuilder::new(&config.url).ok().and_then(|mut x| x.connect(None).ok())
					),
					config,
					first_time: true,	// ensures that on_connect will be called.
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
	first_time: bool,
}

impl TelemetryWriter {
	fn ensure_connected(&mut self) {
		if self.first_time {
			info!("Connected to telemetry server: {}", self.config.url);
			(self.config.on_connect)();
			self.first_time = false;
		}
		let mut client = self.out.lock();
		if client.is_none() {
			*client = ws::ClientBuilder::new(&self.config.url).ok().and_then(|mut x| x.connect(None).ok());
			drop(client);
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
				socket.send_message(&ws::Message::text(s)).is_err()
			} else { false }
		} else { false };
		if socket_closed {
			*l = None;
		}
		self.buffer.clear();
		Ok(())
	}
}
