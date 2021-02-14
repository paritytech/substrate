// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate's client telemetry is a part of substrate that allows ingesting telemetry data
//! with for example [Polkadot telemetry](https://github.com/paritytech/substrate-telemetry).
//!
//! It works using Tokio's [tracing](https://github.com/tokio-rs/tracing/) library. The telemetry
//! information uses tracing's logging to report the telemetry data which is then retrieved by a
//! tracing `Layer`. This layer will then send the data through an asynchronous channel to a
//! background task called [`TelemetryWorker`] which will send the information to the configured
//! remote telemetry servers.
//!
//! If multiple substrate nodes are running in the same process, it uses a `tracing::Span` to
//! identify which substrate node is reporting the telemetry. Every task spawned using sc-service's
//! `TaskManager` automatically inherit this span.
//!
//! Substrate's nodes initialize/register with the [`TelemetryWorker`] using a [`TelemetryHandle`].
//! This handle can be cloned and passed around. It uses an asynchronous channel to communicate with
//! the running [`TelemetryWorker`] dedicated to registration. Registering can happen at any point
//! in time during the process execution.

#![warn(missing_docs)]

use futures::{channel::mpsc, prelude::*};
use libp2p::Multiaddr;
use log::{error, warn};
use serde::Serialize;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver};
use std::collections::HashMap;
use tracing::Id;

pub use libp2p::wasm_ext::ExtTransport;
pub use serde_json;
pub use tracing;

mod endpoints;
mod layer;
mod node;
mod transport;

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

pub(crate) type TelemetryMessage = (Id, u8, String);

/// A handle representing a telemetry span, with the capability to enter the span if it exists.
#[derive(Debug, Clone)]
pub struct TelemetrySpan(tracing::Span);

impl TelemetrySpan {
	/// Enters this span, returning a guard that will exit the span when dropped.
	pub fn enter(&self) -> tracing::span::Entered {
		self.0.enter()
	}

	/// Constructs a new [`TelemetrySpan`].
	pub fn new() -> Self {
		Self(tracing::error_span!(TELEMETRY_LOG_SPAN))
	}

	/// Return a clone of the underlying `tracing::Span` instance.
	pub fn span(&self) -> tracing::Span {
		self.0.clone()
	}
}

/// Message sent when the connection (re-)establishes.
#[derive(Debug, Serialize)]
pub struct ConnectionMessage {
	/// Node's name.
	pub name: String,
	/// Node's implementation.
	pub implementation: String,
	/// Node's version.
	pub version: String,
	/// Node's configuration.
	pub config: String,
	/// Node's chain.
	pub chain: String,
	/// Node's genesis hash.
	pub genesis_hash: String,
	/// Node is an authority.
	pub authority: bool,
	/// Node's startup time.
	pub startup_time: String,
	/// Node's network ID.
	pub network_id: String,
}

/// Telemetry worker.
///
/// It should run as a background task using the [`TelemetryWorker::run`] method. This method
/// will consume the object and any further attempts of initializing a new telemetry through its
/// handle will fail (without being fatal).
#[derive(Debug)]
pub struct TelemetryWorker {
	message_receiver: mpsc::Receiver<TelemetryMessage>,
	message_sender: mpsc::Sender<TelemetryMessage>,
	register_receiver: mpsc::UnboundedReceiver<Register>,
	register_sender: mpsc::UnboundedSender<Register>,
	transport: WsTrans,
}

impl TelemetryWorker {
	pub(crate) fn new(buffer_size: usize, transport: WsTrans) -> Self {
		let (message_sender, message_receiver) = mpsc::channel(buffer_size);
		let (register_sender, register_receiver) = mpsc::unbounded();

		Self {
			message_receiver,
			message_sender,
			register_receiver,
			register_sender,
			transport,
		}
	}

	/// Get a new [`TelemetryHandle`].
	///
	/// This is used when you want to register with the [`TelemetryWorker`].
	pub fn handle(&self) -> TelemetryHandle {
		TelemetryHandle {
			message_sender: self.register_sender.clone(),
		}
	}

	/// Get a clone of the channel's `Sender` used to send telemetry events.
	pub(crate) fn message_sender(&self) -> mpsc::Sender<TelemetryMessage> {
		self.message_sender.clone()
	}

	/// Run the telemetry worker.
	///
	/// This should be run in a background task.
	pub async fn run(self) {
		let Self {
			mut message_receiver,
			message_sender: _,
			mut register_receiver,
			register_sender: _,
			transport,
		} = self;

		let mut node_map: HashMap<Id, Vec<(u8, Multiaddr)>> = HashMap::new();
		let mut node_pool: HashMap<Multiaddr, _> = HashMap::new();

		loop {
			futures::select! {
				message = message_receiver.next() => Self::process_message(
					message,
					&mut node_pool,
					&node_map,
				).await,
				init_payload = register_receiver.next() => Self::process_register(
					init_payload,
					&mut node_pool,
					&mut node_map,
					transport.clone(),
				).await,
			}
		}
	}

	async fn process_register(
		input: Option<Register>,
		node_pool: &mut HashMap<Multiaddr, Node<WsTrans>>,
		node_map: &mut HashMap<Id, Vec<(u8, Multiaddr)>>,
		transport: WsTrans,
	) {
		let input = input.expect("the stream is never closed; qed");

		match input {
			Register::Telemetry {
				id,
				endpoints,
				connection_message,
			} => {
				let endpoints = endpoints.0;

				let connection_message = match serde_json::to_value(&connection_message) {
					Ok(serde_json::Value::Object(mut value)) => {
						value.insert("msg".into(), "system.connected".into());
						let mut obj = serde_json::Map::new();
						obj.insert("id".to_string(), id.into_u64().into());
						obj.insert("payload".to_string(), value.into());
						Some(obj)
					}
					Ok(_) => {
						unreachable!("ConnectionMessage always serialize to an object; qed")
					}
					Err(err) => {
						log::error!(
							target: "telemetry",
							"Could not serialize connection message: {}",
							err,
						);
						None
					}
				};

				for (addr, verbosity) in endpoints {
					log::trace!(
						target: "telemetry",
						"Initializing telemetry for: {:?}",
						addr,
					);
					node_map
						.entry(id.clone())
						.or_default()
						.push((verbosity, addr.clone()));

					let node = node_pool.entry(addr.clone()).or_insert_with(|| {
						Node::new(transport.clone(), addr.clone(), Vec::new(), Vec::new())
					});

					node.connection_messages.extend(connection_message.clone());
				}
			}
			Register::Notifier {
				addresses,
				connection_notifier,
			} => {
				for addr in addresses {
					if let Some(node) = node_pool.get_mut(&addr) {
						node.telemetry_connection_notifier
							.push(connection_notifier.clone());
					} else {
						log::error!(
							target: "telemetry",
							"Received connection notifier for unknown node ({}). This is a bug.",
							addr,
						);
					}
				}
			}
		}
	}

	// dispatch messages to the telemetry nodes
	async fn process_message(
		input: Option<TelemetryMessage>,
		node_pool: &mut HashMap<Multiaddr, Node<WsTrans>>,
		node_map: &HashMap<Id, Vec<(u8, Multiaddr)>>,
	) {
		let (id, verbosity, message) = input.expect("the stream is never closed; qed");

		let nodes = if let Some(nodes) = node_map.get(&id) {
			nodes
		} else {
			// This is a normal error because the telemetry span is entered before the telemetry
			// is initialized so it is possible that some messages in the beginning don't get
			// through.
			log::trace!(
				target: "telemetry",
				"Received telemetry log for unknown id ({:?}): {}",
				id,
				message,
			);
			return;
		};

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

			if let Some(node) = node_pool.get_mut(&addr) {
				let _ = node.send(message.clone()).await;
			} else {
				log::error!(
					target: "telemetry",
					"Received message for unknown node ({}). This is a bug. \
					Message sent: {}",
					addr,
					message,
				);
			}
		}
	}
}

/// Handle to the [`TelemetryWorker`] thats allows initializing the telemetry for a Substrate node.
#[derive(Debug, Clone)]
pub struct TelemetryHandle {
	message_sender: mpsc::UnboundedSender<Register>,
}

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
		span: TelemetrySpan,
		endpoints: TelemetryEndpoints,
		connection_message: ConnectionMessage,
	) -> TelemetryConnectionNotifier {
		let Self { message_sender } = self;

		let connection_notifier = TelemetryConnectionNotifier {
			message_sender: message_sender.clone(),
			addresses: endpoints.0.iter().map(|(addr, _)| addr.clone()).collect(),
		};

		match span.0.id() {
			Some(id) => {
				match message_sender.unbounded_send(Register::Telemetry {
					id,
					endpoints,
					connection_message,
				}) {
					Ok(()) => {}
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
pub struct TelemetryConnectionNotifier {
	message_sender: mpsc::UnboundedSender<Register>,
	addresses: Vec<Multiaddr>,
}

impl TelemetryConnectionNotifier {
	/// Get event stream for telemetry connection established events.
	///
	/// This function will return an error if the telemetry has already been started by
	/// [`TelemetryHandle::start_telemetry`].
	pub fn on_connect_stream(&self) -> TracingUnboundedReceiver<()> {
		let (message_sender, message_receiver) = tracing_unbounded("mpsc_telemetry_on_connect");
		if let Err(err) = self.message_sender.unbounded_send(Register::Notifier {
			addresses: self.addresses.clone(),
			connection_notifier: message_sender,
		}) {
			error!(
				target: "telemetry",
				"Could not create a telemetry connection notifier: \
				the telemetry is probably already running: {}",
				err,
			);
		}
		message_receiver
	}
}

#[derive(Debug)]
enum Register {
	Telemetry {
		id: Id,
		endpoints: TelemetryEndpoints,
		connection_message: ConnectionMessage,
	},
	Notifier {
		addresses: Vec<Multiaddr>,
		connection_notifier: ConnectionNotifierSender,
	},
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
		$crate::serde_json::Result::Ok(map)
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
