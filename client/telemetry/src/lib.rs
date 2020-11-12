// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

// TODO update doc
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

use futures::{channel::mpsc, prelude::*};
use libp2p::{wasm_ext, Multiaddr};
use log::{error, warn};
use parking_lot::Mutex;
use serde::{Deserialize, Deserializer, Serialize};
use std::{
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};
use wasm_timer::Instant;

pub use chrono;
pub use libp2p::wasm_ext::ExtTransport;
pub use serde_json;
pub use tracing;

mod layer;
pub mod worker;

pub use layer::*;
use worker::node_pool::*;

/// List of telemetry servers we want to talk to. Contains the URL of the server, and the
/// maximum verbosity level.
///
/// The URL string can be either a URL or a multiaddress.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
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

impl TelemetryEndpoints {
	/// Return `true` if there are no telemetry endpoints, `false` otherwise.
	pub fn is_empty(&self) -> bool {
		self.0.is_empty()
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
pub const SUBSTRATE_DEBUG: u8 = 9;
pub const SUBSTRATE_INFO: u8 = 0;

pub const CONSENSUS_TRACE: u8 = 9;
pub const CONSENSUS_DEBUG: u8 = 5;
pub const CONSENSUS_WARN: u8 = 4;
pub const CONSENSUS_INFO: u8 = 1;

/// Telemetry object. Implements `Future` and must be polled regularly.
/// Contains an `Arc` and can be cloned and pass around. Only one clone needs to be polled
/// regularly and should be polled regularly.
/// Dropping all the clones unregisters the telemetry.
#[derive(Debug)]
pub struct Telemetry {
	inner: TelemetryInner,
	span: tracing::Span,
}

impl Drop for Telemetry {
	fn drop(&mut self) {
		let span_id = self.span.id().expect("the span is enabled; qed");
		tracing::dispatcher::get_default(move |dispatch| dispatch.exit(&span_id));
	}
}

/// TODO update doc as Telemetry isnt clonable anymore
/// Behind the `Mutex` in `Telemetry`.
///
/// Note that ideally we wouldn't have to make the `Telemetry` cloneable, as that would remove the
/// need for a `Mutex`. However there is currently a weird hack in place in `sc-service`
/// where we extract the telemetry registration so that it continues running during the shutdown
/// process.
#[derive(Debug)]
struct TelemetryInner {
	/// Worker for the telemetry. `None` if it failed to initialize.
	worker: Option<worker::TelemetryWorker>,
	/// Receives log entries for them to be dispatched to the worker.
	receiver: mpsc::Receiver<(u8, String)>,
}

impl Telemetry {
	// TODO update doc
	/// Initializes the telemetry. See the crate root documentation for more information.
	///
	/// Please be careful to not call this function twice in the same program. The `slog` crate
	/// doesn't provide any way of knowing whether a global logger has already been registered.
	pub fn new(
		endpoints: TelemetryEndpoints,
		wasm_external_transport: Option<wasm_ext::ExtTransport>,
		node_pool: Option<&NodePool>,
	) -> (Self, mpsc::Sender<(u8, String)>) {
		let endpoints = endpoints.0;

		let (sender, receiver) = mpsc::channel(16);

		let worker = match worker::TelemetryWorker::new(
			endpoints,
			wasm_external_transport,
			node_pool,
		) {
			Ok(w) => Some(w),
			Err(err) => {
				error!(target: "telemetry", "Failed to initialize telemetry worker: {:?}", err);
				None
			}
		};

		let span = tracing::info_span!(TELEMETRY_LOG_SPAN);
		let span_id = span.id().expect("the span is enabled; qed");
		tracing::dispatcher::get_default(move |dispatch| dispatch.enter(&span_id));

		(
			Self {
				inner: TelemetryInner {
					worker,
					receiver,
				},
				span,
			},
			sender,
		)
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

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let before = Instant::now();

		let mut has_connected = false;

		// The polling pattern is: poll the worker so that it processes its queue, then add one
		// message from the receiver (if possible), then poll the worker again, and so on.
		loop {
			if let Some(worker) = self.inner.worker.as_mut() {
				while let Poll::Ready(event) = worker.poll(cx) {
					// Right now we only have one possible event. This line is here in order to not
					// forget to handle any possible new event type.
					let worker::TelemetryWorkerEvent::Connected = event;
					has_connected = true;
				}
			}

			if let Poll::Ready(Some((
				message_verbosity,
				json,
			))) = Stream::poll_next(Pin::new(&mut self.inner.receiver), cx)
			{
				if let Some(worker) = self.inner.worker.as_mut() {
					let _ = worker.log(message_verbosity, json.as_str());
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

/// TODO doc
#[derive(Debug, Default)]
pub struct Telemetries {
	senders: Senders,
	node_pool: NodePool,
	wasm_external_transport: Option<wasm_ext::ExtTransport>,
}

impl Telemetries {
	/// TODO doc
	pub fn with_wasm_external_transport(wasm_external_transport: wasm_ext::ExtTransport) -> Self {
		Self {
			wasm_external_transport: Some(wasm_external_transport),
			..Default::default()
		}
	}

	// TODO update doc / move to root
	/// endpoints:
	///
	/// Collection of telemetry WebSocket servers with a corresponding verbosity level.
	/// Optional external implementation of a libp2p transport. Used in WASM contexts where we need
	/// some binding between the networking provided by the operating system or environment and
	/// libp2p.
	///
	/// wasm_external_transport:
	///
	/// This parameter exists whatever the target platform is, but it is expected to be set to
	/// `Some` only when compiling for WASM.
	///
	/// > **Important**: Each individual call to `write` corresponds to one message. There is no
	/// >                internal buffering going on. In the context of WebSockets, each `write`
	/// >                must be one individual WebSockets frame.
	pub fn get_or_create(&self, endpoints: TelemetryEndpoints) -> Telemetry {
		let (telemetry, sender) = Telemetry::new(
			endpoints.clone(),
			self.wasm_external_transport.clone(),
			Some(&self.node_pool),
		);
		let id = telemetry.span.id().expect("the span is enabled; qed").into_u64();

		self.senders.insert(id, sender);

		telemetry
	}

	pub fn senders(&self) -> Senders {
		self.senders.clone()
	}
}

/// TODO doc
/// Translates to `slog_scope::info`, but contains an additional verbosity
/// parameter which the log record is tagged with. Additionally the verbosity
/// parameter is added to the record as a key-value pair.
#[macro_export(local_inner_macros)]
macro_rules! telemetry {
	( $a:expr; $b:expr; $( $t:tt )* ) => {{
		let message_verbosity: u8 = $a;
		let mut json = format_fields_to_json!($($t)*);
		// NOTE: the span id will be added later in the JSON for the greater good
		json.insert("level".into(), "INFO".into());
		json.insert("msg".into(), $b.into());
		json.insert("ts".into(), $crate::chrono::Local::now().to_rfc3339().into());
		$crate::tracing::info!(target: $crate::TELEMETRY_LOG_SPAN,
			message_verbosity,
			json = $crate::serde_json::to_string(&json)
				.expect("contains only string keys; qed").as_str()
		);
	}};
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! format_fields_to_json {
	( $k:literal => $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		let mut map = $crate::serde_json::Map::new();
		map.insert($k.into(), $crate::serde_json::to_value($v)
			.expect("telemetry values must be serializable"));
		$(
			map.append(&mut format_fields_to_json!($($t)*));
		)*
		map
	}};
	( $k:literal => ? $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		let mut map = $crate::serde_json::Map::new();
		map.insert($k.into(), std::format!("{:?}", $v).into());
		$(
			map.append(&mut format_fields_to_json!($($t)*));
		)*
		map
	}};
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
