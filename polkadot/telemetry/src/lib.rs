// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Telemtetry utils.

extern crate parking_lot;
extern crate websocket as ws;
extern crate slog_async;
extern crate slog_json;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate slog;

use std::io;
use parking_lot::Mutex;
use slog::Drain;

pub struct TelemetryConfig {
	pub url: String,
	pub on_connect: Box<Fn() + Send + 'static>,
}

lazy_static!{
	static ref TELEMETRY_CONFIG: Mutex<Option<TelemetryConfig>> = Mutex::new(None);
}

pub struct TelemetryWriter {
	buffer: Vec<u8>,
	out: Mutex<Option<ws::sync::Client<Box<ws::stream::sync::NetworkStream + Send>>>>,
}

impl TelemetryWriter {
	fn new() -> Self {
		TelemetryWriter { buffer: vec![], out: Mutex::new(None) }
	}

	pub fn disable() {
		*TELEMETRY_CONFIG.lock() = None;
	}

	pub fn enable(config: TelemetryConfig) {
		*TELEMETRY_CONFIG.lock() = Some(config);
	}

	fn ensure_connected(&self) {
		let mut client = self.out.lock();
		if client.is_none() {
			if let Some(ref config) = *TELEMETRY_CONFIG.lock() {
				*client = ws::ClientBuilder::new(&config.url).ok().and_then(|mut x| x.connect(None).ok());
				drop(client);
				(config.on_connect)();
			}
		}
	}
}

impl io::Write for TelemetryWriter {
	fn write(&mut self, msg: &[u8]) -> io::Result<usize> {
		if msg == b"\n" {
			let _ = self.flush();
		} else {
			self.buffer.extend_from_slice(msg);
		}
		Ok(msg.len())
	}
	
	fn flush(&mut self) -> io::Result<()> {
		self.ensure_connected();
		if if let Some(ref mut socket) = *self.out.lock() {
			if let Ok(s) = ::std::str::from_utf8(&self.buffer[..]) {
				socket.send_message(&ws::Message::text(s)).is_err()
			} else { false }
		} else { false } {
			*self.out.lock() = None;
		}
		self.buffer.clear();
		Ok(())
	}
}

lazy_static!{
	pub static ref SLOG_TELEMETRY: slog::Logger = slog::Logger::root(slog_async::Async::new(slog_json::Json::default(TelemetryWriter::new()).fuse()).build().fuse(), o!());
}

#[macro_export]
macro_rules! telemetry {
	( $($t:tt)* ) => { slog_info!($crate::SLOG_TELEMETRY, $($t)*) }
} 
