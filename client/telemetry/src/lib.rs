// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//! the moment. Substrate may eventually be reworked to get proper `slog` support, including sending
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
//! let telemetry = sc_telemetry::init_telemetry(sc_telemetry::TelemetryConfig {
//! 	endpoints: sc_telemetry::TelemetryEndpoints::new(vec![
//! 		// The `0` is the maximum verbosity level of messages to send to this endpoint.
//! 		("wss://example.com".into(), 0)
//! 	]).expect("Invalid URL or multiaddr provided"),
//! 	// Can be used to pass an external implementation of WebSockets.
//! 	wasm_external_transport: None,
//! });
//!
//! // The `telemetry` object implements `Stream` and must be processed.
//! std::thread::spawn(move || {
//! 	futures::executor::block_on(telemetry.for_each(|_| future::ready(())));
//! });
//!
//! // Sends a message on the telemetry.
//! sc_telemetry::telemetry!(sc_telemetry::SUBSTRATE_INFO; "test";
//! 	"foo" => "bar",
//! )
//! ```
//!

use futures::{prelude::*, channel::mpsc};
use libp2p::{Multiaddr, wasm_ext};
use log::{error, warn};
use parking_lot::Mutex;
use serde::{Serialize, Deserialize, Deserializer};
use std::{pin::Pin, sync::Arc, task::{Context, Poll}, time::Duration};
use wasm_timer::Instant;

pub use libp2p::wasm_ext::ExtTransport;
pub use slog_scope::with_logger;
pub use slog;

mod async_record;
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
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TelemetryEndpoints(
	#[serde(deserialize_with = "url_or_multiaddr_deser")]
	Vec<(Multiaddr, u8)>
);

/// Custom deserializer for TelemetryEndpoints, used to convert urls or multiaddr to multiaddr.
fn url_or_multiaddr_deser<'de, D>(deserializer: D) -> Result<Vec<(Multiaddr, u8)>, D::Error>
	where D: Deserializer<'de>
{
	Vec::<(String, u8)>::deserialize(deserializer)?
		.iter()
		.map(|e| Ok((url_to_multiaddr(&e.0)
		.map_err(serde::de::Error::custom)?, e.1)))
		.collect()
}

impl TelemetryEndpoints {
	pub fn new(endpoints: Vec<(String, u8)>) -> Result<Self, libp2p::multiaddr::Error> {
		let endpoints: Result<Vec<(Multiaddr, u8)>, libp2p::multiaddr::Error> = endpoints.iter()
			.map(|e| Ok((url_to_multiaddr(&e.0)?, e.1)))
			.collect();
		endpoints.map(Self)
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

/// Log levels.
pub const SUBSTRATE_DEBUG: &str = "9";
pub const SUBSTRATE_INFO: &str = "0";

pub const CONSENSUS_TRACE: &str = "9";
pub const CONSENSUS_DEBUG: &str = "5";
pub const CONSENSUS_WARN: &str = "4";
pub const CONSENSUS_INFO: &str = "1";

/// Telemetry object. Implements `Future` and must be polled regularly.
/// Contains an `Arc` and can be cloned and pass around. Only one clone needs to be polled
/// regularly and should be polled regularly.
/// Dropping all the clones unregisters the telemetry.
#[derive(Clone)]
pub struct Telemetry {
	inner: Arc<Mutex<TelemetryInner>>,
	/// Slog guard so that we don't get deregistered.
	_guard: Arc<slog_scope::GlobalLoggerGuard>,
}

/// Behind the `Mutex` in `Telemetry`.
///
/// Note that ideally we wouldn't have to make the `Telemetry` cloneable, as that would remove the
/// need for a `Mutex`. However there is currently a weird hack in place in `sc-service`
/// where we extract the telemetry registration so that it continues running during the shutdown
/// process.
struct TelemetryInner {
	/// Worker for the telemetry. `None` if it failed to initialize.
	worker: Option<worker::TelemetryWorker>,
	/// Receives log entries for them to be dispatched to the worker.
	receiver: mpsc::Receiver<async_record::AsyncRecord>,
}

/// Implements `slog::Drain`.
struct TelemetryDrain {
	/// Sends log entries.
	sender: std::panic::AssertUnwindSafe<mpsc::Sender<async_record::AsyncRecord>>,
}

/// Initializes the telemetry. See the crate root documentation for more information.
///
/// Please be careful to not call this function twice in the same program. The `slog` crate
/// doesn't provide any way of knowing whether a global logger has already been registered.
pub fn init_telemetry(config: TelemetryConfig) -> Telemetry {
	// Build the list of telemetry endpoints.
	let (endpoints, wasm_external_transport) = (config.endpoints.0, config.wasm_external_transport);

	let (sender, receiver) = mpsc::channel(16);
	let guard = {
		let logger = TelemetryDrain { sender: std::panic::AssertUnwindSafe(sender) };
		let root = slog::Logger::root(slog::Drain::fuse(logger), slog::o!());
		slog_scope::set_global_logger(root)
	};

	let worker = match worker::TelemetryWorker::new(endpoints, wasm_external_transport) {
		Ok(w) => Some(w),
		Err(err) => {
			error!(target: "telemetry", "Failed to initialize telemetry worker: {:?}", err);
			None
		}
	};

	Telemetry {
		inner: Arc::new(Mutex::new(TelemetryInner {
			worker,
			receiver,
		})),
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

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let before = Instant::now();

		// Because the `Telemetry` is cloneable, we need to put the actual fields behind a `Mutex`.
		// However, the user is only ever supposed to poll from one instance of `Telemetry`, while
		// the other instances are used only for RAII purposes.
		// We assume that the user is following this advice and therefore that the `Mutex` is only
		// ever locked once at a time.
		let mut inner = match self.inner.try_lock() {
			Some(l) => l,
			None => {
				warn!(
					target: "telemetry",
					"The telemetry seems to be polled multiple times simultaneously"
				);
				// Returning `Pending` here means that we may never get polled again, but this is
				// ok because we're in a situation where something else is actually currently doing
				// the polling.
				return Poll::Pending;
			}
		};

		let mut has_connected = false;

		// The polling pattern is: poll the worker so that it processes its queue, then add one
		// message from the receiver (if possible), then poll the worker again, and so on.
		loop {
			if let Some(worker) = inner.worker.as_mut() {
				while let Poll::Ready(event) = worker.poll(cx) {
					// Right now we only have one possible event. This line is here in order to not
					// forget to handle any possible new event type.
					let worker::TelemetryWorkerEvent::Connected = event;
					has_connected = true;
				}
			}

			if let Poll::Ready(Some(log_entry)) = Stream::poll_next(Pin::new(&mut inner.receiver), cx) {
				if let Some(worker) = inner.worker.as_mut() {
					log_entry.as_record_values(|rec, val| { let _ = worker.log(rec, val); });
				}
			} else {
				break;
			}
		}

		if before.elapsed() > Duration::from_millis(200) {
			warn!(target: "telemetry", "Polling the telemetry took more than 200ms");
		}

		if has_connected {
			Poll::Ready(Some(TelemetryEvent::Connected))
		} else {
			Poll::Pending
		}
	}
}

impl slog::Drain for TelemetryDrain {
	type Ok = ();
	type Err = ();

	fn log(&self, record: &slog::Record, values: &slog::OwnedKVList) -> Result<Self::Ok, Self::Err> {
		let before = Instant::now();

		let serialized = async_record::AsyncRecord::from(record, values);
		// Note: interestingly, `try_send` requires a `&mut` because it modifies some internal value, while `clone()`
		// is lock-free.
		if let Err(err) = self.sender.clone().try_send(serialized) {
			warn!(target: "telemetry", "Ignored telemetry message because of error on channel: {:?}", err);
		}

		if before.elapsed() > Duration::from_millis(50) {
			warn!(target: "telemetry", "Writing a telemetry log took more than 50ms");
		}

		Ok(())
	}
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

#[cfg(test)]
mod telemetry_endpoints_tests {
	use libp2p::Multiaddr;
	use super::TelemetryEndpoints;
	use super::url_to_multiaddr;

	#[test]
	fn valid_endpoints() {
		let endp = vec![("wss://telemetry.polkadot.io/submit/".into(), 3), ("/ip4/80.123.90.4/tcp/5432".into(), 4)];
		let telem = TelemetryEndpoints::new(endp.clone()).expect("Telemetry endpoint should be valid");
		let mut res: Vec<(Multiaddr, u8)> = vec![];
		for (a, b) in endp.iter() {
			res.push((url_to_multiaddr(a).expect("provided url should be valid"), *b))
		}
		assert_eq!(telem.0, res);
	}

	#[test]
	fn invalid_endpoints() {
		let endp = vec![("/ip4/...80.123.90.4/tcp/5432".into(), 3), ("/ip4/no:!?;rlkqre;;::::///tcp/5432".into(), 4)];
		let telem = TelemetryEndpoints::new(endp);
		assert!(telem.is_err());
	}

	#[test]
	fn valid_and_invalid_endpoints() {
		let endp = vec![("/ip4/80.123.90.4/tcp/5432".into(), 3), ("/ip4/no:!?;rlkqre;;::::///tcp/5432".into(), 4)];
		let telem = TelemetryEndpoints::new(endp);
		assert!(telem.is_err());
	}
}
