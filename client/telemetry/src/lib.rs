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

//! To start using this module, please initialize the global logger from `sc-tracing`. This will
//! return a [`TelemetryWorker`] which can be used to register substrate node. In order to do that,
//! first call [`TelemetryWorker::handle()`] to get a handle to the worker, then use
//! [`TelemetryHandle::start_telemetry()`] to initialize the telemetry. This will also return a
//! [`TelemetryConnectionNotifier`] which can be used to create streams of events for whenever the
//! connection to a telemetry server is (re-)established.
//!
//! The macro [`telemetry`] can be used to report telemetries from anywhere in the code but the
//! telemetry must have been initialized through [`TelemetryHandle::start_telemetry()`].
//! Initializing the telemetry will make all the following code execution (including newly created
//! async background tasks) report the telemetries through the endpoints provided during the
//! initialization. If multiple telemetries have been started, the latest one (higher up in the
//! stack) will be used. If no telemetry has been started, nothing will be reported.

#![warn(missing_docs)]

use futures::{channel::mpsc, prelude::*};
use libp2p::{wasm_ext, Multiaddr};
use log::{error, warn};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver};
use std::{
	collections::{HashMap, HashSet},
	time::Duration,
};
use tracing::Id;
use wasm_timer::Instant;

pub use chrono;
pub use libp2p::wasm_ext::ExtTransport;
pub use serde_json;
pub use tracing;

mod dispatcher;
mod endpoints;
mod layer;
mod node;
mod transport;

use dispatcher::*;
pub use endpoints::*;
pub use layer::*;
use node::*;
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

pub(crate) type InitPayload = (
	Id,
	TelemetryEndpoints,
	ConnectionMessage,
	mpsc::UnboundedReceiver<ConnectionNotifierSender>,
);

/// Telemetry worker.
///
/// It should be ran as a background task using the [`TelemetryWorker::run`] method. This method
/// will consume the object and any further attempts of initializing a new telemetry through its
/// handle will fail (without being fatal).
#[derive(Debug)]
pub struct TelemetryWorker {
	receiver: mpsc::Receiver<(Id, u8, String)>,
	sender: mpsc::Sender<(Id, u8, String)>,
	init_receiver: mpsc::UnboundedReceiver<InitPayload>,
	init_sender: mpsc::UnboundedSender<InitPayload>,
	transport: WsTrans,
}

/// Telemetry Result typedef.
pub type Result<T> = std::result::Result<T, Error>;

/// Telemetry errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum Error {
	#[error(transparent)]
	Io(#[from] std::io::Error),
}

impl TelemetryWorker {
	/// Create a [`TelemetryWorker`] instance using an [`ExtTransport`].
	///
	/// The [`ExtTransport`] is used in WASM contexts where we need some binding between the
	/// networking provided by the operating system or environment and libp2p.
	///
	/// > **Important**: Each individual call to `write` corresponds to one message. There is no
	/// >                internal buffering going on. In the context of WebSockets, each `write`
	/// >                must be one individual WebSockets frame.
	pub(crate) fn new(wasm_external_transport: Option<wasm_ext::ExtTransport>) -> Result<Self> {
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

	/// Get a clone of the channel's `Sender` used to send telemetry events.
	pub(crate) fn sender(&self) -> mpsc::Sender<(Id, u8, String)> {
		self.sender.clone()
	}

	/// Run the telemetry worker.
	///
	/// This should be run in a background task.
	pub async fn run(self) {
		let Self {
			receiver,
			sender: _sender,
			mut init_receiver,
			init_sender: _init_sender,
			transport,
		} = self;

		let mut node_map: HashMap<Id, Vec<(u8, Multiaddr)>> = HashMap::new();
		let mut node_args: HashMap<
			Multiaddr,
			(Vec<ConnectionMessage>, Vec<ConnectionNotifierSender>),
		> = HashMap::new();
		let mut existing_nodes: HashSet<Multiaddr> = HashSet::new();

		// initialize the telemetry nodes
		init_receiver.close();
		while let Some((id, endpoints, connection_message, mut connection_notifiers_rx)) =
			init_receiver.next().await
		{
			let endpoints = endpoints.0;

			connection_notifiers_rx.close();
			let connection_notifier_senders: Vec<_> = connection_notifiers_rx.collect().await;

			for (addr, verbosity) in endpoints {
				node_map
					.entry(id.clone())
					.or_insert_with(Vec::new)
					.push((verbosity, addr.clone()));
				existing_nodes.insert(addr.clone());
				let mut obj = connection_message.clone();
				obj.insert("msg".into(), "system.connected".into());
				obj.insert("id".into(), id.into_u64().into());
				let (connection_messages, connection_notifiers) = node_args
					.entry(addr.clone())
					.or_insert_with(|| (Vec::new(), Vec::new()));
				connection_messages.push(obj);
				connection_notifiers.extend(connection_notifier_senders.clone());
			}
		}

		let mut node_pool: Dispatcher = existing_nodes
			.iter()
			.map(|addr| {
				let (connection_messages, connection_notifiers) = node_args
					.remove(addr)
					.expect("there is a node for every connection message; qed");
				let node = Node::new(
					transport.clone(),
					addr.clone(),
					connection_messages,
					connection_notifiers,
				);
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
			.flat_map(
				|(verbosity, message, nodes): (u8, String, &Vec<(u8, Multiaddr)>)| {
					let mut to_send = Vec::with_capacity(nodes.len());
					let before = Instant::now();

					for (node_max_verbosity, addr) in nodes {
						if verbosity > *node_max_verbosity {
							log::trace!(
								target: "telemetry",
								"Skipping {} for log entry with verbosity {:?}",
								addr,
								verbosity,
							);
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
				},
			)
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
		connection_message: ConnectionMessage,
	) -> TelemetryConnectionNotifier {
		let span = tracing::info_span!(TELEMETRY_LOG_SPAN);
		let (sender, receiver) = mpsc::unbounded();
		let connection_notifier = TelemetryConnectionNotifier(sender);

		match span.id() {
			Some(id) => {
				match self
					.0
					.unbounded_send((id.clone(), endpoints, connection_message, receiver))
				{
					Ok(()) => tracing::dispatcher::get_default(move |dispatch| dispatch.enter(&id)),
					Err(err) => error!(
						target: "telemetry",
						"Could not initialize telemetry: \
						the telemetry is probably already running: {}",
						err,
					),
				}
			}
			None => error!(
				target: "telemetry",
				"Could not initialize telemetry: the span could not be entered",
			),
		}

		connection_notifier
	}
}

/// Used to create a stream of events with only one event: when a telemetry connection
/// (re-)establishes.
#[derive(Clone, Debug)]
pub struct TelemetryConnectionNotifier(mpsc::UnboundedSender<ConnectionNotifierSender>);

impl TelemetryConnectionNotifier {
	/// Get event stream for telemetry connection established events.
	pub fn on_connect_stream(&self) -> TracingUnboundedReceiver<()> {
		let (sender, receiver) = tracing_unbounded("mpsc_telemetry_on_connect");
		if let Err(err) = self.0.unbounded_send(sender) {
			error!(
				target: "telemetry",
				"Could not create a telemetry connection notifier: \
				the telemetry is probably already running: {}",
				err,
			);
		}
		receiver
	}
}

/// Report a telemetry.
///
/// Translates to [`tracing::info`], but contains an additional verbosity parameter which the log
/// record is tagged with. Additionally the verbosity parameter is added to the record as a
/// key-value pair.
///
/// # Example
///
/// ```no_run
/// # use sc_telemetry::*;
/// # let authority_id = 42_u64;
/// # let set_id = (43_u64, 44_u64);
/// # let authorities = vec![45_u64];
/// telemetry!(CONSENSUS_INFO; "afg.authority_set";
/// 	"authority_id" => authority_id.to_string(),
/// 	"authority_set_id" => ?set_id,
/// 	"authorities" => authorities,
/// );
/// ```
#[macro_export(local_inner_macros)]
macro_rules! telemetry {
	( $verbosity:expr; $msg:expr; $( $t:tt )* ) => {{
		let verbosity: u8 = $verbosity;
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
				json.insert("msg".into(), $msg.into());
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
		let ok_map: $crate::serde_json::Result<_> = Ok(map);
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
