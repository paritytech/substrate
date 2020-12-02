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

//! Telemetry utilities.
//!
//! You can collect telemetries for a substrate node by creating a `Telemetry` object. For every
//! substrate node there must be only one `Telemetry` object. This `Telemetry` object can connect to
//! multiple telemetry endpoints. The `Telemetry` object is a `Stream` that needs to be polled
//! regularly in order to function.
//!
//! The macro `telemetry!` can be used to report telemetries from anywhere in the code but a
//! `Telemetry` must have been initialized. Creating a `Telemetry` will make all the following code
//! execution (including newly created async background tasks) use this `Telemetry` when reporting
//! telemetries. If multiple `Telemetry` objects are created, the latest one (higher up in the
//! stack) will be used. If no `Telemetry` object can be found, nothing is reported.
//!
//! To re-use connections to the same server you need to use the `Telemetries` object to create
//! multiple `Telemetry`. `Telemetries` also manages a collection of channel `Sender` for you (see
//! `Senders`). `Telemetries` should be used unless you need finer control.
//!
//! The [`Telemetry`] struct implements `Stream` and must be polled regularly (or sent to a
//! background thread/task) in order for the telemetry to properly function.
//! The `Stream` generates [`TelemetryEvent`]s.

#![warn(missing_docs)]

use futures::{channel::mpsc, prelude::*};
use libp2p::{wasm_ext, Multiaddr};
use log::{error, warn};
use serde::{Deserialize, Deserializer, Serialize};
use std::{
	collections::{HashMap, HashSet},
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};
use wasm_timer::Instant;
use tracing::Id;
use parking_lot::Mutex;
use sp_utils::{status_sinks, mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender}};

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
	/// Create a `TelemetryEndpoints` based on a list of `(String, u8)`.
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

/// Substrate DEBUG log level.
pub const SUBSTRATE_DEBUG: u8 = 9;
/// Substrate INFO log level.
pub const SUBSTRATE_INFO: u8 = 0;

/// Consensus TRACE log level.
pub const CONSENSUS_TRACE: u8 = 9;
/// Consensus DEBUG log level.
pub const CONSENSUS_DEBUG: u8 = 5;
/// Consensus WARN log level.
pub const CONSENSUS_WARN: u8 = 4;
/// Consensus INFO log level.
pub const CONSENSUS_INFO: u8 = 1;

/// Telemetry object. Implements `Future` and must be polled regularly.
///
/// Dropping unregisters the telemetry.
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

#[derive(Debug)]
struct TelemetryInner {
	/// Worker for the telemetry. `None` if it failed to initialize.
	worker: Option<worker::TelemetryWorker>,
	/// Receives log entries for them to be dispatched to the worker.
	receiver: mpsc::Receiver<(u8, String)>,
}

impl Telemetry {
	/// Initializes the telemetry. See the crate root documentation for more information.
	pub fn new(
		endpoints: TelemetryEndpoints,
		wasm_external_transport: Option<wasm_ext::ExtTransport>,
		node_pool: Option<()>,
	) -> (Self, mpsc::Sender<(u8, String)>) {
		let endpoints = endpoints.0;

		let (sender, receiver) = mpsc::channel(16);

		let worker = match worker::TelemetryWorker::new(
			endpoints,
			wasm_external_transport,
			None,
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
				verbosity,
				json,
			))) = Stream::poll_next(Pin::new(&mut self.inner.receiver), cx)
			{
				if let Some(worker) = self.inner.worker.as_mut() {
					let _ = worker.log(verbosity, json.as_str());
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

/// An object that keeps track of all the [`Telemetry`] created by its `build_telemetry()` method.
///
/// [`Telemetry`] created through this object re-use connections if possible.
#[derive(Debug)]
pub struct Telemetries {
	receiver: mpsc::Receiver<(Id, u8, String)>,
	sender: mpsc::Sender<(Id, u8, String)>,
	node_map: HashMap<Id, Vec<(u8, Multiaddr)>>,
	connection_messages: HashMap<Id, String>,
	connection_sinks: HashMap<Id, TelemetryConnectionSinks>,
	senders: Senders, // TODO remove
	node_pool: HashMap<Multiaddr, crate::worker::node::Node<crate::worker::WsTrans>>, // TODO mod
	wasm_external_transport: Option<wasm_ext::ExtTransport>,
}

impl Telemetries {
	/// TODO
	pub fn new() -> Self {
		let (sender, receiver) = mpsc::channel(16);

		Self {
			receiver,
			sender,
			node_map: Default::default(),
			connection_messages: Default::default(),
			connection_sinks: Default::default(),
			senders: Default::default(),
			node_pool: Default::default(),
			wasm_external_transport: None,
		}
	}

	/// Create a [`Telemetries`] object using an `ExtTransport`.
	///
	/// This is used in WASM contexts where we need some binding between the networking provided by
	/// the operating system or environment and libp2p.
	///
	/// This constructor is expected to be used only when compiling for WASM.
	///
	/// > **Important**: Each individual call to `write` corresponds to one message. There is no
	/// >                internal buffering going on. In the context of WebSockets, each `write`
	/// >                must be one individual WebSockets frame.
	pub fn with_wasm_external_transport(wasm_external_transport: wasm_ext::ExtTransport) -> Self {
		Self {
			wasm_external_transport: Some(wasm_external_transport),
			..Self::new()
		}
	}

	/// Create a new [`Telemetry`] for the endpoints provided in argument.
	///
	/// The `endpoints` argument is a collection of telemetry WebSocket servers with a corresponding
	/// verbosity level.
	pub fn build_telemetry(&self, endpoints: TelemetryEndpoints) -> Telemetry {
		let (telemetry, sender) = Telemetry::new(
			endpoints,
			self.wasm_external_transport.clone(),
			None, // TODO
		);
		let id = telemetry.span.id().expect("the span is enabled; qed");

		self.senders.insert(id, sender);

		telemetry
	}

	/// Get a clone of the channel's [`Senders`].
	pub fn senders(&self) -> Senders {
		self.senders.clone()
	}

	/// TODO
	pub async fn run(self) {
		let Self {
			mut receiver,
			sender,
			node_map,
			connection_messages,
			connection_sinks,
			senders,
			mut node_pool,
			wasm_external_transport,
		} = self;
		let mut node_first_connect: HashSet<(Multiaddr, Id)> = node_map
			.iter()
			.map(|(id, addrs)| addrs.iter().map(move |(_, x)| (x.to_owned(), id.to_owned())))
			.flatten()
			.collect();

		while let Some((id, verbosity, message)) = receiver.next().await {
			let before = Instant::now();

			let nodes = if let Some(nodes) = node_map.get(&id) {
				nodes
			} else {
				log::error!(
					target: "telemetry",
					"Received telemetry log for unknown id ({:?}): {}",
					id,
					message,
				);
				continue;
			};

			for (node_max_verbosity, addr) in nodes {
				let node = if let Some(node) = node_pool.get_mut(addr) {
					node
				} else {
					log::error!(
						target: "telemetry",
						"Could not find telemetry server in the NodePool: {}",
						addr,
					);
					continue;
				};

				if verbosity > *node_max_verbosity {
					log::trace!(
						target: "telemetry",
						"Skipping {} for log entry with verbosity {:?}",
						addr,
						verbosity);
					continue;
				}

				// Disconnection
				if !matches!(node.next().await, Some(crate::worker::node::NodeEvent::Connected)) {
					node_first_connect.insert((addr.to_owned(), id.to_owned()));
					continue;
				}

				// Reconnection handling
				if node_first_connect.remove(&(addr.to_owned(), id.clone())) {
					if let Some(connection_sink) = connection_sinks.get(&id) {
						connection_sink.fire();
					}
					if let Some(message) = connection_messages.get(&id) {
						let _ = node.send_message(message.clone()); // TODO probably dont need to clone
					}
				}

				// `send_message` returns an error if we're not connected, which we silently ignore.
				let _ = node.send_message(message.clone()); // TODO probably dont need to clone
			}

			if before.elapsed() > Duration::from_millis(200) {
				log::warn!(
					target: "telemetry",
					"Processing one telemetry message took more than 200ms",
				);
			}
		}
	}
}

/// Sinks to propagate telemetry connection established events.
#[derive(Default, Clone, Debug)]
pub struct TelemetryConnectionSinks(Arc<Mutex<Vec<TracingUnboundedSender<()>>>>);

impl TelemetryConnectionSinks {
	/// Get event stream for telemetry connection established events.
	pub fn on_connect_stream(&self) -> TracingUnboundedReceiver<()> {
		let (sink, stream) =tracing_unbounded("mpsc_telemetry_on_connect");
		self.0.lock().push(sink);
		stream
	}

	pub(crate) fn fire(&self) {
		self.0.lock().retain(|sink| {
			sink.unbounded_send(()).is_ok()
		});
	}
}

/// Translates to `tracing::info!`, but contains an additional verbosity
/// parameter which the log record is tagged with. Additionally the verbosity
/// parameter is added to the record as a key-value pair.
#[macro_export(local_inner_macros)]
macro_rules! telemetry {
	( $a:expr; $b:expr; $( $t:tt )* ) => {{
		let verbosity: u8 = $a;
		match format_fields_to_json!($($t)*) {
			Err(err) => {
				$crate::tracing::error!(
					target: "telemetry",
					"Could not serialize value for telemetry: {}",
					err,
				);
			},
			Ok(mut json) => {
				// NOTE: the span id will be added later in the JSON for the greater good
				json.insert("msg".into(), $b.into());
				json.insert("ts".into(), $crate::chrono::Local::now().to_rfc3339().into());
				let serialized_json = $crate::serde_json::to_string(&json)
					.expect("contains only string keys; qed");
				$crate::tracing::info!(target: $crate::TELEMETRY_LOG_SPAN,
					verbosity,
					json = serialized_json.as_str(),
				);
			},
		}
	}};
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! format_fields_to_json {
	( $k:literal => $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		$crate::serde_json::to_value(&$v)
			.map(|value| {
				let mut map = $crate::serde_json::Map::new();
				map.insert($k.into(), value);
				map
			})
			$(
				.and_then(|mut prev_map| {
					format_fields_to_json!($($t)*)
						.map(move |mut other_map| {
							prev_map.append(&mut other_map);
							prev_map
						})
				})
			)*
	}};
	( $k:literal => ? $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		let mut map = $crate::serde_json::Map::new();
		map.insert($k.into(), std::format!("{:?}", &$v).into());
		let ok_map: Result<_, $crate::serde_json::Error> = Ok(map);
		ok_map
		$(
			.and_then(|mut prev_map| {
				format_fields_to_json!($($t)*)
					.map(move |mut other_map| {
						prev_map.append(&mut other_map);
						prev_map
					})
			})
		)*
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
