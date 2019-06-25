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

//! Telemetry utilities.
//!
//! Calling `init_telemetry` registers a global `slog` logger using `slog_scope::set_global_logger`.
//! After that, calling `slog_scope::with_logger` will return a logger that sends information to
//! the telemetry endpoints. The `telemetry!` macro is a short-cut for calling
//! `slog_scope::with_logger` followed with `slog_log!`.
//!
//! Note that you are supposed to only ever use `telemetry!` and not `slog_scope::with_logger` at
//! the moment. Substate may eventually be reworked to get proper `slog` support, including sending
//! information to the telemetry.
//!
//! The [`Telemetry`] struct implements `Stream` and must be polled regularly (or sent to a
//! background thread/task) in order for the telemetry to properly function. Dropping the object
//! will also deregister the global logger and replace it with a logger that discards messages.
//! The `Stream` generates [`TelemetryEvent`]s.
//!
//! > **Note**: Cloning the [`Telemetry`] and polling from multiple clones has an unspecified behaviour.
//!
//! # Example
//!
//! ```no_run
//! use futures::prelude::*;
//!
//! let telemetry = substrate_telemetry::init_telemetry(substrate_telemetry::TelemetryConfig {
//! 	endpoints: substrate_telemetry::TelemetryEndpoints::new(vec![
//! 		// The `0` is the maximum verbosity level of messages to send to this endpoint.
//! 		("wss://example.com".into(), 0)
//! 	]),
//! 	// Can be used to pass an external implementation of WebSockets.
//! 	wasm_external_transport: None,
//! });
//!
//! // The `telemetry` object implements `Stream` and must be processed.
//! std::thread::spawn(move || {
//! 	tokio::run(telemetry.for_each(|_| Ok(())));
//! });
//!
//! // Sends a message on the telemetry.
//! substrate_telemetry::telemetry!(substrate_telemetry::SUBSTRATE_INFO; "test";
//! 	"foo" => "bar",
//! )
//! ```
//!

use futures::{prelude::*, task::AtomicTask};
use libp2p::{Multiaddr, wasm_ext};
use log::warn;
use parking_lot::Mutex;
use serde::{Serialize, Deserialize};
use std::sync::{Arc, Weak};
use std::time::{Duration, Instant};

pub use slog_scope::with_logger;
pub use slog;

mod worker;

/// Configuration for telemetry.
pub struct TelemetryConfig {
	/// Collection of telemetry WebSocket servers with a corresponding verbosity level.
	pub endpoints: TelemetryEndpoints,

	/// Optional external implementation of a libp2p transport. Used in WASM contexts where we need
	/// some binding between the networking provided by the operating system or environment and
	/// libp2p.
	///
	/// This parameter exists whatever the target platform is, but it is expected to be set to
	/// `Some` only when compiling for WASM.
	///
	/// > **Important**: Each individual call to `write` corresponds to one message. There is no
	/// >                internal buffering going on. In the context of WebSockets, each `write`
	/// >                must be one individual WebSockets frame.
	pub wasm_external_transport: Option<wasm_ext::ExtTransport>,
}

/// List of telemetry servers we want to talk to. Contains the URL of the server, and the
/// maximum verbosity level.
///
/// The URL string can be either a URL or a multiaddress.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryEndpoints(Vec<(String, u8)>);

impl TelemetryEndpoints {
	pub fn new(endpoints: Vec<(String, u8)>) -> Self {
		TelemetryEndpoints(endpoints)
	}
}

/// Log levels.
pub const SUBSTRATE_DEBUG: &str = "9";
pub const SUBSTRATE_INFO: &str = "0";

pub const CONSENSUS_TRACE: &str = "9";
pub const CONSENSUS_DEBUG: &str = "5";
pub const CONSENSUS_WARN: &str = "4";
pub const CONSENSUS_INFO: &str = "1";

/// Telemetry object. Implements `Future` and must be polled regularly.
/// Contains an `Arc` and can be cloned and pass around. Only one clone needs to be polled
/// regularly.
/// Dropping all the clones unregisters the telemetry.
#[derive(Clone)]
pub struct Telemetry {
	inner: Arc<TelemetryInner>,
	/// Slog guard so that we don't get deregistered.
	_guard: Arc<slog_scope::GlobalLoggerGuard>,
}

// Implementation notes: considering that logging can happen at any moment, we only have two
// options: locking a mutex (which we currently do), or using a channel (which we should do).
// At the moment, `slog` doesn't provide any easy way to serialize records in order to send them
// over a channel, but ideally that's what should be done.

/// Shared between `Telemetry` and `TelemetryDrain`.
struct TelemetryInner {
	/// Worker for the telemetry.
	worker: Mutex<worker::TelemetryWorker>,
	/// Task to wake up when we add a log entry to the worker.
	polling_task: AtomicTask,
}

/// Implements `slog::Drain`.
struct TelemetryDrain {
	inner: std::panic::AssertUnwindSafe<Weak<TelemetryInner>>,
}

/// Initializes the telemetry. See the crate root documentation for more information.
///
/// Please be careful to not call this function twice in the same program. The `slog` crate
/// doesn't provide any way of knowing whether a global logger has already been registered.
pub fn init_telemetry(config: TelemetryConfig) -> Telemetry {
	// Build the list of telemetry endpoints.
	let mut endpoints = Vec::new();
	for &(ref url, verbosity) in &config.endpoints.0 {
		match url_to_multiaddr(url) {
			Ok(addr) => endpoints.push((addr, verbosity)),
			Err(err) => warn!(target: "telemetry", "Invalid telemetry URL {}: {}", url, err),
		}
	}

	let inner = Arc::new(TelemetryInner {
		worker: Mutex::new(worker::TelemetryWorker::new(endpoints, config.wasm_external_transport)),
		polling_task: AtomicTask::new(),
	});

	let guard = {
		let logger = TelemetryDrain { inner: std::panic::AssertUnwindSafe(Arc::downgrade(&inner)) };
		let root = slog::Logger::root(slog::Drain::fuse(logger), slog::o!());
		slog_scope::set_global_logger(root)
	};

	Telemetry {
		inner,
		_guard: Arc::new(guard),
	}
}

/// Event generated when polling the worker.
#[derive(Debug)]
pub enum TelemetryEvent {
	/// We have established a connection to one of the telemetry endpoint, either for the first
	/// time or after having been disconnected earlier.
	Connected,
}

impl Stream for Telemetry {
	type Item = TelemetryEvent;
	type Error = ();

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		let before = Instant::now();

		let mut has_connected = false;
		while let Async::Ready(event) = self.inner.worker.lock().poll() {
			// Right now we only have one possible event. This line is here in order to not
			// forget to handle any possible new event type.
			let worker::TelemetryWorkerEvent::Connected = event;
			has_connected = true;
		}

		if before.elapsed() > Duration::from_millis(200) {
			warn!(target: "telemetry", "Polling the telemetry took more than 200ms");
		}

		if has_connected {
			Ok(Async::Ready(Some(TelemetryEvent::Connected)))
		} else {
			self.inner.polling_task.register();
			Ok(Async::NotReady)
		}
	}
}

impl slog::Drain for TelemetryDrain {
	type Ok = ();
	type Err = ();

	fn log(&self, record: &slog::Record, values: &slog::OwnedKVList) -> Result<Self::Ok, Self::Err> {
		if let Some(inner) = self.inner.0.upgrade() {
			let before = Instant::now();
			let result = inner.worker.lock().log(record, values);
			inner.polling_task.notify();
			if before.elapsed() > Duration::from_millis(50) {
				warn!(target: "telemetry", "Writing a telemetry log took more than 50ms");
			}
			result
		} else {
			Ok(())
		}
	}
}

/// Parses a WebSocket URL into a libp2p `Multiaddr`.
fn url_to_multiaddr(url: &str) -> Result<Multiaddr, libp2p::multiaddr::Error> {
	// First, assume that we have a `Multiaddr`.
	let parse_error = match url.parse() {
		Ok(ma) => return Ok(ma),
		Err(err) => err,
	};

	// If not, try the `ws://path/url` format.
	if let Ok(ma) = libp2p::multiaddr::from_url(url) {
		return Ok(ma)
	}

	// If we have no clue about the format of that string, assume that we were expecting a
	// `Multiaddr`.
	Err(parse_error)
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
