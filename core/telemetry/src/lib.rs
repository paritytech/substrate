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

//! Telemetry utils.
//!
//! `telemetry` macro may be used anywhere in the Substrate codebase
//! in order to send real-time logging information to the telemetry
//! server (if there is one). We use the async drain adapter of `slog`
//! so that the logging thread doesn't get held up at all.

use std::{io, time, thread};
use std::sync::Arc;
use parking_lot::Mutex;
use slog::{Drain, o, OwnedKVList, Record};
use log::trace;
use rand::{thread_rng, Rng};
pub use slog_scope::with_logger;
pub use slog;
use serde::{Serialize, Deserialize};
use core::result;

/// Configuration for telemetry.
pub struct TelemetryConfig {
	/// Collection of telemetry WebSocket servers with a corresponding verbosity level.
	pub endpoints: TelemetryEndpoints,
	/// What do do when we connect to the servers.
	/// Note that this closure is executed each time we connect to a telemetry endpoint.
	pub on_connect: Box<Fn() + Send + Sync + 'static>,
}

/// Telemetry service guard.
pub type Telemetry = slog_scope::GlobalLoggerGuard;

/// Size of the channel for passing messages to telemetry thread.
const CHANNEL_SIZE: usize = 262144;

/// Log levels.
pub const SUBSTRATE_DEBUG: &str = "9";
pub const SUBSTRATE_INFO: &str = "0";

pub const CONSENSUS_TRACE: &str = "9";
pub const CONSENSUS_DEBUG: &str = "5";
pub const CONSENSUS_WARN: &str = "4";
pub const CONSENSUS_INFO: &str = "0";

/// Multiply logging to all drains. This is similar to `slog::Duplicate`, which is
/// limited to two drains though and doesn't support dynamic nesting at runtime.
#[derive(Debug, Clone)]
pub struct Multiply<D: Drain> (pub Vec<Box<D>>);

impl<D: Drain> Multiply<D> {
	pub fn new(v: Vec<Box<D>>) -> Self {
		Multiply(v)
	}
}

impl<D: Drain> Drain for Multiply<D> {
	type Ok = Vec<D::Ok>;
	type Err = Vec<D::Err>;

	fn log(&self, record: &Record, logger_values: &OwnedKVList) -> result::Result<Self::Ok, Self::Err> {
		let mut oks = Vec::new();
		let mut errs = Vec::new();

		self.0.iter().for_each(|l| {
			let res: Result<<D as Drain>::Ok, <D as Drain>::Err> = (*l).log(record, logger_values);
			match res {
				Ok(o) => oks.push(o),
				Err(e) => errs.push(e),
			}
		});

		if !errs.is_empty() {
			result::Result::Err(errs)
		} else {
			result::Result::Ok(oks)
		}
	}
}

/// Initialize telemetry.
pub fn init_telemetry(config: TelemetryConfig) -> slog_scope::GlobalLoggerGuard {
	let mut endpoint_drains: Vec<Box<slog::Filter<_, _>>> = Vec::new();
	let mut out_syncs = Vec::new();

	// Set up a filter/drain for each endpoint
	config.endpoints.0.iter().for_each(|(url, verbosity)| {
		let writer = TelemetryWriter::new(Arc::new(url.to_owned()));
		let out_sync = writer.out.clone();
		out_syncs.push(out_sync);

		let until_verbosity = *verbosity;
		let filter = slog::Filter(
			slog_json::Json::default(writer).fuse(),
			move |rec| {
				let tag = rec.tag().parse::<u8>()
					.expect("`telemetry!` macro requires tag.");
				tag <= until_verbosity
			});

		let filter = Box::new(filter) as Box<slog::Filter<_, _>>;
		endpoint_drains.push(filter);
	});

	// Set up logging to all endpoints
	let drain = slog_async::Async::new(Multiply::new(endpoint_drains).fuse());
	let root = slog::Logger::root(drain.chan_size(CHANNEL_SIZE)
		.overflow_strategy(slog_async::OverflowStrategy::DropAndReport)
		.build().fuse(), o!()
	);
	let logger_guard = slog_scope::set_global_logger(root);

	// Spawn a thread for each endpoint
	let on_connect = Arc::new(config.on_connect);
	config.endpoints.0.into_iter().for_each(|(url, verbosity)| {
		let inner_verbosity = Arc::new(verbosity.to_owned());
		let inner_on_connect = Arc::clone(&on_connect);

		let out_sync = out_syncs.remove(0);
		let out_sync = Arc::clone(&out_sync);

		thread::spawn(move || {
			loop {
				let on_connect = Arc::clone(&inner_on_connect);
				let out_sync = Arc::clone(&out_sync);
				let verbosity = Arc::clone(&inner_verbosity);

				trace!(target: "telemetry",
					"Connecting to Telemetry at {} with verbosity {}", url, Arc::clone(&verbosity));

				let _ = ws::connect(url.to_owned(),
					|out| {
						Connection::new(out, Arc::clone(&out_sync), Arc::clone(&on_connect), url.clone())
					});

				// Sleep for a random time between 5-10 secs. If there are general connection
				// issues not all threads should be synchronized in their re-connection time.
				let random_sleep = thread_rng().gen_range(0, 5);
				thread::sleep(time::Duration::from_secs(5) + time::Duration::from_secs(random_sleep));
			}
		});
	});

	return logger_guard;
}

/// Translates to `slog_scope::info`, but contains an additional verbosity
/// parameter which the log record is tagged with. Additionally the verbosity
/// parameter is added to the record as a key-value pair.
#[macro_export]
macro_rules! telemetry {
	 ( $a:expr; $b:expr; $( $t:tt )* ) => {
		$crate::with_logger(|l| {
			$crate::slog::slog_info!(l, #$a, $b; $($t)* )
		})
    }
}

struct Connection {
	out: ws::Sender,
	out_sync: Arc<Mutex<Option<ws::Sender>>>,
	on_connect: Arc<Box<Fn() + Send + Sync + 'static>>,
	url: String,
}

impl Connection {
	fn new(
		out: ws::Sender,
		out_sync: Arc<Mutex<Option<ws::Sender>>>,
		on_connect: Arc<Box<Fn() + Send + Sync + 'static>>,
		url: String
	) -> Self {
		Connection {
			out,
			out_sync,
			on_connect,
			url,
		}
	}
}

impl ws::Handler for Connection {
	fn on_open(&mut self, _: ws::Handshake) -> ws::Result<()> {
		trace!(target: "telemetry", "Connected to {}!", self.url);

		*self.out_sync.lock() = Some(self.out.clone());
		(self.on_connect)();
		Ok(())
	}

    fn on_close(&mut self, code: ws::CloseCode, reason: &str) {
		*self.out_sync.lock() = None;

		trace!(target: "telemetry", "Connection to {} closing due to ({:?}) {}",
			self.url, code, reason);
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
	url: Arc<String>,
}

impl TelemetryWriter {
	fn new(url: Arc<String>) -> Self {
		let out = Arc::new(Mutex::new(None));

		TelemetryWriter {
			buffer: Vec::new(),
			out,
			url,
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
				trace!(target: "telemetry", "Sent to telemetry {}: {} -> {:?}", self.url, s, r);

				r.is_err()
			} else {
				trace!(target: "telemetry", "Telemetry socket closed to {}, failed to send: {}", self.url, s);
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryEndpoints (Vec<(String, u8)>);

impl TelemetryEndpoints {
	pub fn new(endpoints: Vec<(String, u8)>) -> Self {
		TelemetryEndpoints(endpoints)
	}
}
