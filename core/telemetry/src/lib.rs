// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Telemetry utils.
//!
//! `telemetry` macro may be used anywhere in the Substrate codebase
//! in order to send real-time logging information to the telemetry
//! server (if there is one). We use the async drain adapter of `slog`
//! so that the logging thread doesn't get held up at all.

extern crate parking_lot;
extern crate ws;
extern crate slog_async;
extern crate slog_json;
#[macro_use]
extern crate log;
#[macro_use(o)]
extern crate slog;
extern crate slog_scope;

use std::{io, time, thread};
use std::sync::Arc;
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
	let writer = TelemetryWriter::new();
	let out_sync = writer.out.clone();
	let log = slog::Logger::root(
		slog_async::Async::new(
			slog_json::Json::default(writer).fuse()
		).chan_size(CHANNEL_SIZE)
		.overflow_strategy(slog_async::OverflowStrategy::DropAndReport)
		.build().fuse(), o!()
	);
	let logger_guard = slog_scope::set_global_logger(log);

	thread::spawn(move || {
		loop {
			trace!(target: "telemetry", "Connecting to Telemetry...");
			let _ = ws::connect(config.url.as_str(), |out| Connection::new(out, &*out_sync, &config));

			thread::sleep(time::Duration::from_millis(5000));
		}
	});

	return logger_guard;
}

/// Exactly equivalent to `slog_scope::info`, provided as a convenience.
#[macro_export]
macro_rules! telemetry {
	( $($t:tt)* ) => { $crate::with_logger(|l| slog_info!(l, $($t)* )) }
}

struct Connection<'a> {
	out: ws::Sender,
	out_sync: &'a Mutex<Option<ws::Sender>>,
	config: &'a TelemetryConfig,
}

impl<'a> Connection<'a> {
	fn new(out: ws::Sender, out_sync: &'a Mutex<Option<ws::Sender>>, config: &'a TelemetryConfig) -> Self {
		Connection {
			out,
			out_sync,
			config,
		}
	}
}

impl<'a> ws::Handler for Connection<'a> {
	fn on_open(&mut self, _: ws::Handshake) -> ws::Result<()> {
		trace!(target: "telemetry", "Connected!");

		*self.out_sync.lock() = Some(self.out.clone());
		(self.config.on_connect)();
		Ok(())
	}

    fn on_close(&mut self, code: ws::CloseCode, reason: &str) {
		*self.out_sync.lock() = None;

		trace!(target: "telemetry", "Connection closing due to ({:?}) {}", code, reason);
    }

	fn on_error(&mut self, _: ws::Error) {
		*self.out_sync.lock() = None;

		// Sleep to ensure that reconnecting isn't spamming logs.
		// This happens in it's own thread so it won't block anything.
		thread::sleep(time::Duration::from_millis(1000));
	}
}

struct TelemetryWriter {
	buffer: Vec<u8>,
	out: Arc<Mutex<Option<ws::Sender>>>,
}

impl TelemetryWriter {
	fn new() -> Self {
		let out = Arc::new(Mutex::new(None));

		TelemetryWriter {
			buffer: Vec::new(),
			out,
		}
	}
}

impl io::Write for TelemetryWriter {
	fn write(&mut self, msg: &[u8]) -> io::Result<usize> {
		let mut iter = msg.split(|x| *x == b'\n');
		let first = iter.next().expect("Split iterator always has at least one element; qed");

		self.buffer.extend_from_slice(first);

		// Flush for each occurrence of new line character
		for continued in iter {
			let _ = self.flush();
			self.buffer.extend_from_slice(continued);
		}

		Ok(msg.len())
	}

	fn flush(&mut self) -> io::Result<()> {
		if self.buffer.is_empty() {
			return Ok(());
		}
		if let Ok(s) = ::std::str::from_utf8(&self.buffer[..]) {
			let mut out = self.out.lock();

			let error = if let Some(ref mut o) = *out {
				let r = o.send(s);
				trace!(target: "telemetry", "Sent to telemetry: {} -> {:?}", s, r);

				r.is_err()
			} else {
				trace!(target: "telemetry", "Telemetry socket closed, failed to send: {}", s);
				false
			};

			if error {
				*out = None;
			}
		}
		self.buffer.clear();
		Ok(())
	}
}
