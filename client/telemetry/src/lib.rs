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

//! Telemetry utilities. TODO update doc
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
//! To re-use connections to the same server you need to use the `TelemetryWorker` object to create
//! multiple `Telemetry`. `TelemetryWorker` also manages a collection of channel `Sender` for you (see
//! `Senders`). `TelemetryWorker` should be used unless you need finer control.
//!
//! The [`Telemetry`] struct implements `Stream` and must be polled regularly (or sent to a
//! background thread/task) in order for the telemetry to properly function.
//! The `Stream` generates [`TelemetryEvent`]s.

#![warn(missing_docs)]

use futures::{channel::mpsc, prelude::*};
use libp2p::{
	wasm_ext, Multiaddr,
};
use log::{error, warn};
use std::{
	collections::{HashMap, HashSet},
	io,
	sync::Arc,
	time::Duration,
};
use wasm_timer::Instant;
use tracing::Id;
use parking_lot::Mutex;
use sp_utils::{mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender}};

pub use chrono;
pub use libp2p::wasm_ext::ExtTransport;
pub use serde_json;
pub use tracing;

mod layer;
mod node;
mod dispatcher;
mod transport;
mod endpoints;

pub use layer::*;
use node::*;
use dispatcher::*;
pub use endpoints::*;
use transport::*;

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

pub(crate) type InitPayload = (Id, TelemetryEndpoints, serde_json::Value, TelemetryConnectionNotifier);

/// An object that keeps track of all the [`Telemetry`] created by its `build_telemetry()` method.
///
/// [`Telemetry`] created through this object re-use connections if possible.
#[derive(Debug)]
pub struct TelemetryWorker {
	receiver: mpsc::Receiver<(Id, u8, String)>,
	sender: mpsc::Sender<(Id, u8, String)>,
	init_receiver: mpsc::UnboundedReceiver<InitPayload>,
	init_sender: mpsc::UnboundedSender<InitPayload>,
	transport: WsTrans,
}

impl TelemetryWorker {
	/// Create a [`TelemetryWorker`] instance using an `ExtTransport`.
	///
	/// This is used in WASM contexts where we need some binding between the networking provided by
	/// the operating system or environment and libp2p.
	///
	/// This constructor is expected to be used only when compiling for WASM.
	///
	/// > **Important**: Each individual call to `write` corresponds to one message. There is no
	/// >                internal buffering going on. In the context of WebSockets, each `write`
	/// >                must be one individual WebSockets frame.
	pub fn new(wasm_external_transport: Option<wasm_ext::ExtTransport>) -> Result<Self, io::Error> {
		let (sender, receiver) = mpsc::channel(16);
		let (init_sender, init_receiver) = mpsc::unbounded();

		Ok(Self {
			receiver,
			sender,
			init_receiver,
			init_sender,
			transport: initialize_transport(wasm_external_transport)?,
		})
	}

	/// Get a handle to this [`TelemetryWorker`].
	///
	/// This is used when you want to register a new telemetry for a Substrate node.
	pub fn handle(&self) -> TelemetryHandle {
		TelemetryHandle(self.init_sender.clone())
	}

	/// Get a clone of the channel's `Sender` used to send telemetry event.
	pub(crate) fn sender(&self) -> mpsc::Sender<(Id, u8, String)> {
		self.sender.clone()
	}

	/// Run the telemetry worker.
	pub async fn run(self) {
		let Self {
			receiver,
			sender: _sender,
			mut init_receiver,
			init_sender,
			transport,
		} = self;

		let mut node_map: HashMap<Id, Vec<(u8, Multiaddr)>> = HashMap::new();
		let mut connection_messages: HashMap<Multiaddr, Vec<serde_json::Value>> = HashMap::new();
		let mut telemetry_connection_notifier: HashMap<Multiaddr, Vec<TelemetryConnectionNotifier>> = HashMap::new();
		let mut existing_nodes: HashSet<Multiaddr> = HashSet::new();

		// initialize the telemetry nodes
		init_sender.close_channel();
		while let Some((id, endpoints, connection_message, connection_sink)) = init_receiver.next().await
		{
			let endpoints = endpoints.0;

			for (addr, verbosity) in endpoints {
				node_map.entry(id.clone()).or_insert_with(Vec::new)
					.push((verbosity, addr.clone()));
				existing_nodes.insert(addr.clone());
				let mut json = connection_message.clone();
				let obj = json.as_object_mut().expect("todo");
				obj.insert("msg".into(), "system.connected".into());
				obj.insert("id".into(), id.into_u64().into());
				connection_messages.entry(addr.clone()).or_insert_with(Vec::new)
					.push(json);
				telemetry_connection_notifier.entry(addr.clone()).or_insert_with(Vec::new)
					.push(connection_sink.clone());
			}
		}

		let mut node_pool: Dispatcher =
			existing_nodes
				.iter()
				.map(|addr| {
					let connection_messages = connection_messages.remove(addr)
						.expect("there is a node for every connection message; qed");
					let telemetry_connection_notifier = telemetry_connection_notifier.remove(addr)
						.expect("there is a node for every connection sink; qed");
					let node = Node::new(transport.clone(), addr.clone(), connection_messages, telemetry_connection_notifier);
					(addr.clone(), node)
				})
				.collect();

		let _ = receiver
			.filter_map(|(id, verbosity, message): (Id, u8, String)| {
				if let Some(nodes) = node_map.get(&id) {
					future::ready(Some((verbosity, message, nodes)))
				} else {
					log::error!(
						target: "telemetry",
						"Received telemetry log for unknown id ({:?}): {}",
						id,
						message,
					);
					future::ready(None)
				}
			})
			.flat_map(|(verbosity, message, nodes): (u8, String, &Vec<(u8, Multiaddr)>)| {
				let mut to_send = Vec::with_capacity(nodes.len());
				let before = Instant::now();

				for (node_max_verbosity, addr) in nodes {
					if verbosity > *node_max_verbosity {
						log::trace!(
							target: "telemetry",
							"Skipping {} for log entry with verbosity {:?}",
							addr,
							verbosity);
						continue;
					}

					to_send.push((addr.clone(), message.clone()));
				}

				if before.elapsed() > Duration::from_millis(200) {
					log::warn!(
						target: "telemetry",
						"Processing one telemetry message took more than 200ms",
					);
				}

				stream::iter(to_send)
			})
			.map(|x| Ok(x))
			.boxed()
			.forward(&mut node_pool)
			.await;

		log::error!(
			target: "telemetry",
			"Unexpected end of stream. This is a bug.",
		);
	}
}

/// Handle to the [`TelemetryWorker`] thats allows initializing the telemetry for a Substrate node.
#[derive(Clone, Debug)]
pub struct TelemetryHandle(mpsc::UnboundedSender<InitPayload>);

impl TelemetryHandle {
	/// Initialize the telemetry with the endpoints provided in argument for the current substrate
	/// node.
	///
	/// This method must be called during the substrate node initialization.
	///
	/// The `endpoints` argument is a collection of telemetry WebSocket servers with a corresponding
	/// verbosity level.
	///
	/// The `connection_message` argument is a JSON object that is sent every time the connection
	/// (re-)establishes.
	pub fn start_telemetry(
		&mut self,
		endpoints: TelemetryEndpoints,
		connection_message: serde_json::Value,
	) -> TelemetryConnectionNotifier {
		let connection_sink = TelemetryConnectionNotifier::default();
		let span = tracing::info_span!(TELEMETRY_LOG_SPAN);

		match span.id() {
			Some(id) => {
				match self.0.unbounded_send(
					(id.clone(), endpoints, connection_message, connection_sink.clone()),
				) {
					Ok(()) =>
						tracing::dispatcher::get_default(move |dispatch| dispatch.enter(&id)),
					Err(err) => error!(
						target: "telemetry",
						"Could not initialize telemetry: {}",
						err,
					),
				}
			},
			None => error!(
				target: "telemetry",
				"Could not initialize telemetry: the span could not be entered",
			),
		}

		connection_sink
	}
}

/// Used to create a stream of events with only one event: when a telemetry connection
/// (re-)establishes.
#[derive(Default, Clone, Debug)]
pub struct TelemetryConnectionNotifier(Arc<Mutex<Vec<TracingUnboundedSender<()>>>>);

impl TelemetryConnectionNotifier {
	/// Get event stream for telemetry connection established events.
	pub fn on_connect_stream(&self) -> TracingUnboundedReceiver<()> {
		let (sink, stream) = tracing_unbounded("mpsc_telemetry_on_connect");
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
